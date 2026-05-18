// world-model-trajectories — browser glue.
// wmt-core (Rust→wasm) owns registry/trajectory/AGM/SMT assembly.
// Z3 (wasm) is the only solver. Each script runs in a FRESH context so a
// call is hermetic — exactly the `z3 -in` per-invocation semantics the
// crate's native tests verify against.
import initWasm, { WmtEngine } from './pkg/wmt_core.js';
import { init as z3Init } from './vendor/z3/z3-solver.bundle.mjs';

const $ = (s) => document.querySelector(s);
const esc = (s) => String(s).replace(/[&<>]/g, (c) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;' }[c]));
let engine, Z3, z3ok = false;

async function boot() {
  await initWasm();
  engine = new WmtEngine();
  try {
    const z = await z3Init();
    Z3 = z.Z3;
    z3ok = true;
    $('#z3status').textContent = 'Z3 ready';
  } catch (e) {
    $('#z3status').textContent = 'Z3 failed to load';
    console.error(e);
  }
  wire();
  refresh();
}

async function run(script) {
  const cfg = Z3.mk_config();
  const ctx = Z3.mk_context(cfg);
  const out = await Z3.eval_smtlib2_string(ctx, script);
  try { Z3.del_context(ctx); } catch (_) {}
  return String(out).trim();
}
function status(out) {
  const ls = out.split('\n').map((s) => s.trim()).filter(Boolean);
  for (const l of ls) if (l === 'sat' || l === 'unsat' || l === 'unknown') return l;
  if (/^unsat\b/m.test(out)) return 'unsat';
  if (/^unknown\b/m.test(out)) return 'unknown';
  if (/^sat\b/m.test(out)) return 'sat';
  return 'error';
}
function core(out) {
  const m = out.match(/\(([^()]*)\)\s*$/m) || out.match(/\(([^()]*)\)/);
  return m ? m[1].split(/\s+/).filter(Boolean) : [];
}

function refresh() {
  const meta = JSON.parse(engine.meta());
  // trajectory
  const box = $('#claims');
  box.innerHTML = '';
  if (!meta.claims.length) box.innerHTML = '<p class="muted small">empty — load the demo, or formalize a claim below.</p>';
  for (const c of meta.claims) {
    const d = document.createElement('div');
    d.className = 'claim' + (c.active ? '' : ' inactive');
    d.id = 'claim-' + c.id;
    d.innerHTML =
      `<div class="src">${esc(c.source || c.gloss || c.id)}</div>` +
      `<div class="smt">${esc(c.smt)}</div>` +
      `<div class="row" style="margin:8px 0 0"><span class="id">${esc(c.id)}</span>` +
      (c.active
        ? `<button class="btn ghost sm" data-act="retract" data-id="${esc(c.id)}">retract</button>`
        : `<button class="btn ghost sm" data-act="reactivate" data-id="${esc(c.id)}">reactivate</button>`) +
      `<button class="btn ghost sm" data-act="remove" data-id="${esc(c.id)}">remove</button></div>`;
    box.appendChild(d);
  }
  // registry
  $('#registry').innerHTML = meta.decls.length
    ? meta.decls.map((x) => `<div><code>${esc(x.smtlib)}</code> — ${esc(x.gloss)}</div>`).join('')
    : '<p class="muted">empty</p>';
  box.querySelectorAll('button[data-act]').forEach((b) =>
    b.onclick = () => {
      const id = b.dataset.id;
      if (b.dataset.act === 'retract') engine.retract(id);
      else if (b.dataset.act === 'reactivate') engine.reactivate(id);
      else engine.remove(id);
      refresh();
    });
  analyze(meta);
}

function mark(ids) {
  document.querySelectorAll('.claim').forEach((e) => e.classList.remove('conflict'));
  ids.forEach((id) => document.getElementById('claim-' + id)?.classList.add('conflict'));
}

async function analyze(meta) {
  const sl = $('#statusLine');
  if (!z3ok) { sl.innerHTML = '<span class="status warn">Z3 not loaded — checks unavailable</span>'; return; }
  if (!meta.claims.some((c) => c.active)) {
    sl.innerHTML = '<span class="status muted">no active claims</span>';
    $('#forced').innerHTML = ''; mark([]); return;
  }
  sl.innerHTML = '<span class="status muted">checking with Z3…</span>';
  const st = status(await run(engine.smt_check()));
  if (st === 'sat') {
    sl.innerHTML = '<span class="status ok">✓ consistent</span>';
    mark([]);
    await forced(meta);
  } else if (st === 'unsat') {
    const c = core(await run(engine.smt_consistency()));
    sl.innerHTML =
      '<span class="status bad">✗ inconsistent</span> <span class="small">minimal conflict — these claims cannot all hold: ' +
      c.map((x) => `<code>${esc(x)}</code>`).join(' · ') +
      ' &nbsp;<span class="muted">retract one (your call)</span></span>';
    mark(c);
    $('#forced').innerHTML = '';
  } else if (st === 'unknown') {
    sl.innerHTML = '<span class="status warn">? Z3 returned <b>unknown</b> — undecided on this fragment, NOT assumed consistent</span>';
    mark([]); $('#forced').innerHTML = '';
  } else {
    sl.innerHTML = '<span class="status bad">Z3 error — the formalization did not type-check</span>';
  }
}

async function forced(meta) {
  const atoms = meta.bool_atoms || [];
  const out = [];
  for (const a of atoms) {
    if (status(await run(engine.smt_entails(a))) === 'unsat') { out.push([a, true]); continue; }
    if (status(await run(engine.smt_entails(`(not ${a})`))) === 'unsat') out.push([a, false]);
  }
  $('#forced').innerHTML = out.length
    ? '<div class="forced"><b>forced — entailed though no single claim asserts it:</b> ' +
      out.map(([a, v]) => `<code>${esc(a)}</code> = ${v ? 'true' : 'false'}`).join(' &nbsp;·&nbsp; ') +
      '</div>'
    : '';
}

function wire() {
  $('#seedBtn').onclick = () => { engine.seed_demo(); refresh(); };
  $('#promptBtn').onclick = () => { $('#prompt').value = engine.prompt($('#nl').value || ''); };
  $('#copyBtn').onclick = async () => {
    try { await navigator.clipboard.writeText($('#prompt').value); $('#copyBtn').textContent = 'Copied'; setTimeout(() => ($('#copyBtn').textContent = 'Copy'), 1200); }
    catch (_) { $('#prompt').select(); }
  };
  $('#ingestBtn').onclick = () => {
    const res = JSON.parse(engine.ingest($('#json').value || ''));
    $('#errs').innerHTML = res.ok ? '' : '<div class="errbox">' + res.errors.map(esc).join('\n') + '</div>';
    if (res.ok) $('#json').value = '';
    refresh();
  };
  $('#askBtn').onclick = async () => {
    const t = ($('#query').value || '').trim();
    if (!t || !z3ok) return;
    const st = status(await run(engine.smt_entails(t)));
    $('#askOut').innerHTML =
      st === 'unsat' ? '<span class="status ok">entailed — everything you\'ve said forces this</span>'
      : st === 'sat' ? '<span class="status muted">not entailed — its negation is consistent with your set</span>'
      : st === 'unknown' ? '<span class="status warn">Z3: unknown</span>'
      : '<span class="status bad">Z3 error — check the SMT-LIB2 term</span>';
  };
}

boot();
