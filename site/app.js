// world-model-trajectories — browser glue.
// wmt-core (Rust→wasm) owns the typed IR, the IR↔SMT compiler, the English
// renderer, the trajectory, and the analysis step-driver. Z3 (wasm) is the
// only solver. The human never sees SMT — only their sentence + our English
// render. Each script runs in a fresh Z3 context (hermetic, == the `z3 -in`
// semantics the crate's native tests verify against).
// Per-commit cache-busting: __WMTVER__ is replaced with the short commit
// SHA by the Pages workflow at deploy time. Mutable assets (this file,
// the wasm-bindgen glue, our wasm, css) are version-pinned per deploy so a
// returning visitor never gets a stale app.js against a fresh wasm. The
// vendored Z3 (34 MB, version-pinned, immutable) is intentionally left
// un-busted so it stays long-cached. Locally the literal token is a
// harmless query value the dev server ignores.
const VER = '__WMTVER__';

const $ = (s) => document.querySelector(s);
const esc = (s) => String(s).replace(/[&<>]/g, (c) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;' }[c]));
let engine, WmtEngine, Z3, z3ok = false;

async function boot() {
  const wasmMod = await import(`./pkg/wmt_core.js?v=${VER}`);
  WmtEngine = wasmMod.WmtEngine;
  const { init: z3Init } = await import('./vendor/z3/z3-solver.bundle.mjs');
  await wasmMod.default(`./pkg/wmt_core_bg.wasm?v=${VER}`);
  engine = new WmtEngine();
  try {
    const z = await z3Init();
    Z3 = z.Z3; z3ok = true;
    $('#z3status').textContent = 'Z3 ready';
  } catch (e) { $('#z3status').textContent = 'Z3 failed to load'; console.error(e); }
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
const z3head = (o) => (o.split('\n').map((x) => x.trim()).find(Boolean) || '');

function refresh() {
  const meta = JSON.parse(engine.meta());
  const box = $('#claims');
  box.innerHTML = meta.claims.length ? '' :
    '<p class="muted small">empty — load the demo, or formalize a claim below.</p>';
  for (const c of meta.claims) {
    const d = document.createElement('div');
    d.className = 'claim' + (c.active ? '' : ' inactive');
    d.id = 'claim-' + c.id;
    d.innerHTML =
      `<div class="src">${esc(c.source || c.gloss || c.id)}</div>` +
      `<div class="smt">⊢ ${esc(c.render)}</div>` +
      `<div class="row" style="margin:8px 0 0">` +
      `<span class="id">${esc(c.id)}</span>` +
      `<label class="chip">entrenchment <input type="number" min="1" max="99" value="${c.weight}" ` +
      `data-w="${esc(c.id)}" style="width:46px;font-family:var(--mono)"></label>` +
      (c.active
        ? `<button class="btn ghost sm" data-act="retract" data-id="${esc(c.id)}">retract</button>`
        : `<button class="btn ghost sm" data-act="reactivate" data-id="${esc(c.id)}">reactivate</button>`) +
      `<button class="btn ghost sm" data-act="remove" data-id="${esc(c.id)}">remove</button></div>`;
    box.appendChild(d);
  }
  $('#registry').innerHTML = '<pre class="small" style="white-space:pre-wrap">' + esc(meta.vocab) + '</pre>';
  box.querySelectorAll('button[data-act]').forEach((b) => b.onclick = () => {
    const id = b.dataset.id, a = b.dataset.act;
    if (a === 'retract') engine.retract(id);
    else if (a === 'reactivate') engine.reactivate(id);
    else engine.remove(id);
    refresh();
  });
  box.querySelectorAll('input[data-w]').forEach((inp) => inp.onchange = () => {
    engine.set_weight(inp.dataset.w, parseInt(inp.value, 10) || 1); refresh();
  });
  analyze(meta);
}

function mark(ids) {
  document.querySelectorAll('.claim').forEach((e) => e.classList.remove('conflict'));
  ids.forEach((id) => document.getElementById('claim-' + id)?.classList.add('conflict'));
}

async function analyze(meta) {
  const sl = $('#statusLine');
  if (!z3ok) { sl.innerHTML = '<span class="status warn">Z3 not loaded</span>'; return; }
  if (!meta.claims.some((c) => c.active)) {
    sl.innerHTML = '<span class="status muted">no active claims</span>';
    $('#forced').innerHTML = ''; mark([]); return;
  }
  sl.innerHTML = '<span class="status muted">analyzing with Z3…</span>';
  engine.analyze_begin();
  let guard = 0;
  while (true) {
    const s = engine.analyze_next();
    if (!s) break;
    engine.analyze_feed(await run(s));
    if (++guard > 400) break;
  }
  const r = JSON.parse(engine.analyze_result());
  if (r.status === 'consistent') {
    sl.innerHTML = '<span class="status ok">✓ consistent</span>';
    mark([]); await forced(meta);
  } else if (r.status === 'unknown') {
    sl.innerHTML = '<span class="status warn">? Z3 returned <b>unknown</b> — undecided on this fragment, NOT assumed consistent</span>';
    mark([]); $('#forced').innerHTML = '';
  } else if (r.status === 'inconsistent') {
    mark(r.mus);
    const drop = r.repair.drop || [];
    sl.innerHTML =
      '<span class="status bad">✗ inconsistent</span> ' +
      '<div class="small" style="margin-top:8px"><b>minimal conflict</b> — these cannot all hold: ' +
      r.mus.map((x) => `<code>${esc(x)}</code>`).join(' · ') + '</div>' +
      '<div class="forced" style="margin-top:8px"><b>optimal repair</b> (least total entrenchment to give up, weight ' +
      esc(r.repair.weight) + '): drop ' + drop.map((x) => `<code>${esc(x)}</code>`).join(' · ') +
      ` &nbsp;<button class="btn warm sm" id="applyRepair">retract these</button>` +
      ` <span class="muted">— or pick your own; the selection is yours.</span></div>`;
    $('#forced').innerHTML = '';
    const ar = $('#applyRepair');
    if (ar) ar.onclick = () => { drop.forEach((id) => engine.retract(id)); refresh(); };
  } else {
    sl.innerHTML = '<span class="status bad">Z3 error — the formalization did not type-check (surfaced, not guessed)</span>';
  }
}

async function forced(meta) {
  const atoms = meta.bool_atoms || [];
  const out = [];
  for (const a of atoms) {
    const f = JSON.stringify({ op: 'pred', name: a, args: [] });
    if (z3head(await run(engine.smt_entails_json(f))) === 'unsat') { out.push([a, true]); continue; }
    const nf = JSON.stringify({ op: 'not', x: { op: 'pred', name: a, args: [] } });
    if (z3head(await run(engine.smt_entails_json(nf))) === 'unsat') out.push([a, false]);
  }
  $('#forced').innerHTML = out.length
    ? '<div class="forced"><b>forced — entailed though no single claim asserts it:</b> ' +
      out.map(([a, v]) => `<code>${esc(a)}</code> = ${v ? 'true' : 'false'}`).join(' &nbsp;·&nbsp; ') + '</div>'
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
    let res;
    try { res = JSON.parse(engine.ingest($('#json').value || '')); }
    catch (e) { $('#errs').innerHTML = '<div class="errbox">engine error: ' + esc(e) + '</div>'; return; }
    $('#errs').innerHTML = res.ok ? '' : '<div class="errbox">' + res.errors.map(esc).join('\n') + '</div>';
    if (res.ok) $('#json').value = '';
    refresh();
  };
}

boot();
