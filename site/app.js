// world-model-trajectories — the instrument.
// wmt-core (Rust→wasm) owns the typed IR, the IR↔SMT compiler, the English
// renderer, the trajectory, and the lattice/repair drivers. Z3 (wasm) is
// the only solver. The human reads their sentence + our English render —
// never logic syntax. Per-commit cache-busting: __WMTVER__ is replaced
// with the short commit SHA at deploy (locally a harmless query value).
const VER = '__WMTVER__';
const $ = (s) => document.querySelector(s);
const esc = (s) => String(s).replace(/[&<>]/g, (c) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;' }[c]));
const short = (id) => id.replace(/^c_/, '').replace(/_/g, ' ');
let engine, Z3, z3ok = false;

async function boot() {
  const m = await import(`./pkg/wmt_core.js?v=${VER}`);
  // the z3-solver browser bundle is CJS→ESM: only a default export (the
  // exports object) — there is no named `init`. (A real-browser headless
  // test caught this; it had been latently broken.)
  const z3mod = await import('./vendor/z3/z3-solver.bundle.mjs');
  const z3Init = (z3mod.default && z3mod.default.init) || z3mod.init;
  await m.default(`./pkg/wmt_core_bg.wasm?v=${VER}`);
  engine = new m.WmtEngine();
  try {
    const z = await z3Init();
    Z3 = z.Z3; z3ok = true;
    const el = $('#z3'); el.textContent = 'Z3 ready'; el.classList.add('rdy');
  } catch (e) { $('#z3').textContent = 'Z3 failed'; console.error(e); }
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

async function driveDriver() {
  engine.analyze_begin();
  let g = 0;
  for (let s = engine.analyze_next(); s; s = engine.analyze_next()) {
    engine.analyze_feed(await run(s));
    if (++g > 600) break;
  }
  return JSON.parse(engine.analyze_result());
}
async function driveLattice() {
  engine.lattice_begin();
  let g = 0;
  for (let s = engine.lattice_next(); s; s = engine.lattice_next()) {
    engine.lattice_feed(await run(s));
    if (++g > 4096) break;
  }
  return JSON.parse(engine.lattice_result());
}

let META = { claims: [] };

function renderClaims(statusOf) {
  const box = $('#claims');
  box.innerHTML = META.claims.length ? '' :
    '<p class="muted small">empty — load the penguin trajectory, or add a claim.</p>';
  for (const c of META.claims) {
    const st = c.active ? (statusOf ? statusOf(c.id) : 'coherent') : 'inactive';
    const d = document.createElement('div');
    d.className = `claim ${c.active ? st : 'inactive'}`;
    d.id = 'cl-' + c.id;
    d.innerHTML =
      `<div class="src">${esc(c.source || c.gloss || c.id)}</div>` +
      `<div class="ren">${esc(c.render)}</div>` +
      `<div class="foot">` +
      `<span class="cid">${esc(c.id)}</span>` +
      `<span class="wt">w<input type="number" min="1" max="99" value="${c.weight}" data-w="${esc(c.id)}"></span>` +
      `<span class="dot ${c.active ? st : 'inactive'}" title="${st}"></span>` +
      (c.active
        ? `<button class="btn tiny ghost" data-a="retract" data-id="${esc(c.id)}">retract</button>`
        : `<button class="btn tiny ghost" data-a="reactivate" data-id="${esc(c.id)}">restore</button>`) +
      `<button class="btn tiny ghost" data-a="remove" data-id="${esc(c.id)}">×</button>` +
      `</div>`;
    box.appendChild(d);
  }
  box.querySelectorAll('button[data-a]').forEach((b) => b.onclick = () => {
    const { a, id } = b.dataset;
    if (a === 'retract') engine.retract(id);
    else if (a === 'reactivate') engine.reactivate(id);
    else engine.remove(id);
    refresh();
  });
  box.querySelectorAll('input[data-w]').forEach((i) => i.onchange = () => {
    engine.set_weight(i.dataset.w, parseInt(i.value, 10) || 1); refresh();
  });
}

function svgField(activeIds, muses) {
  const n = activeIds.length;
  if (!n) return '';
  const W = 640, H = Math.max(260, 90 + n * 26), cx = 210, cy = H / 2, R = Math.min(cy - 40, 150);
  const pt = (i) => {
    const a = -Math.PI / 2 + (2 * Math.PI * i) / n;
    return [cx + R * Math.cos(a), cy + R * Math.sin(a)];
  };
  const hues = ['#b9534a', '#d99a3f', '#5b8a5a', '#2a3a55', '#8a6a47'];
  let hulls = '';
  muses.forEach((m, k) => {
    const col = hues[k % hues.length];
    const pts = m.map((id) => pt(activeIds.indexOf(id))).filter((p) => p[0] !== undefined);
    if (pts.length >= 2) {
      const dpath = pts.map((p, j) => (j ? 'L' : 'M') + p[0].toFixed(1) + ',' + p[1].toFixed(1)).join(' ') + ' Z';
      hulls += `<path d="${dpath}" fill="${col}22" stroke="${col}" stroke-width="1.5" stroke-dasharray="${pts.length === 2 ? '4 3' : '0'}"/>`;
    }
  });
  let nodes = '';
  activeIds.forEach((id, i) => {
    const [x, y] = pt(i);
    nodes += `<circle cx="${x.toFixed(1)}" cy="${y.toFixed(1)}" r="6" fill="#faf6ea" stroke="#241f19" stroke-width="1.5"/>` +
      `<text x="${(x + (x < cx ? -10 : 10)).toFixed(1)}" y="${(y + 4).toFixed(1)}" font-size="12" font-family="'JetBrains Mono',monospace" fill="#241f19" text-anchor="${x < cx ? 'end' : 'start'}">${esc(short(id))}</text>`;
  });
  let legend = '';
  muses.forEach((m, k) => {
    legend += `<rect x="430" y="${28 + k * 22}" width="12" height="12" fill="${hues[k % hues.length]}33" stroke="${hues[k % hues.length]}"/>` +
      `<text x="450" y="${38 + k * 22}" font-size="12" font-family="'JetBrains Mono',monospace" fill="#241f19">disagreement ${k + 1} (${m.length})</text>`;
  });
  return `<svg viewBox="0 0 ${W} ${H}" role="img" aria-label="conflict structure">${hulls}${nodes}${legend}</svg>`;
}

async function forced() {
  // probe 0-ary propositions AND ground atoms (predicates on declared
  // constants) — "you never asserted this but are committed to it".
  const probes = [
    ...(META.bool_atoms || []).map((a) => ({ label: a, formula: { op: 'pred', name: a, args: [] } })),
    ...(META.ground_atoms || []),
  ];
  const out = [];
  for (const p of probes) {
    if (z3head(await run(engine.smt_entails_json(JSON.stringify(p.formula)))) === 'unsat') {
      out.push([p.label, true]); continue;
    }
    if (z3head(await run(engine.smt_entails_json(JSON.stringify({ op: 'not', x: p.formula })))) === 'unsat') {
      out.push([p.label, false]);
    }
  }
  return out.length
    ? `<div class="fieldlabel">What you're committed to</div><div class="forced">` +
      out.map(([a, v]) => `<code class="tok">${esc(a)}</code> = ${v ? 'true' : 'false'}`).join(' &nbsp;·&nbsp; ') +
      `</div>` : '';
}

async function refresh() {
  META = JSON.parse(engine.meta());
  renderClaims(null);
  const status = $('#status'), field = $('#field');
  if (!z3ok) { status.className = 'statusbar warn'; status.innerHTML = '<span>Z3 not loaded</span>'; return; }
  const active = META.claims.filter((c) => c.active).map((c) => c.id);
  if (!active.length) {
    status.className = 'statusbar muted';
    status.innerHTML = '<span>no active claims</span>'; field.innerHTML = ''; return;
  }
  status.className = 'statusbar muted';
  status.innerHTML = '<span class="spin"></span><span>analyzing the trajectory with Z3…</span>';
  field.innerHTML = '';

  const drv = await driveDriver();
  const lat = await driveLattice();

  // dialectical status per active claim
  let statusOf;
  if (lat.consistent || drv.status === 'consistent') {
    statusOf = () => 'coherent';
  } else if (lat.capped || !lat.mss || !lat.mss.length) {
    const inMus = new Set(drv.mus || []);
    statusOf = (id) => (inMus.has(id) ? 'contested' : 'coherent');
  } else {
    const P = lat.mss;
    statusOf = (id) => {
      const k = P.filter((p) => p.includes(id)).length;
      return k === P.length ? 'necessary' : k === 0 ? 'defeated' : 'contested';
    };
  }
  renderClaims(statusOf);

  if (drv.status === 'unknown') {
    status.className = 'statusbar warn';
    status.innerHTML = '<span class="big">unknown</span><span>Z3 is undecided on this fragment — <b>not</b> assumed consistent. Try a less heavily-quantified formalization.</span>';
    return;
  }
  if (lat.consistent || drv.status === 'consistent') {
    status.className = 'statusbar ok';
    status.innerHTML = '<span class="big">coherent</span><span>every active claim holds together — one position: all of them.</span>';
    field.innerHTML = await forced();
    return;
  }

  // inconsistent
  status.className = 'statusbar bad';
  status.innerHTML = `<span class="big">inconsistent</span><span>${lat.capped
    ? 'large set — showing the single minimal conflict + optimal repair (full lattice capped at 10 active claims)'
    : `${lat.mus.length} irreducible disagreement${lat.mus.length > 1 ? 's' : ''}, ${lat.mss.length} coherent position${lat.mss.length > 1 ? 's' : ''}`}</span>`;

  const muses = lat.capped ? [drv.mus || []] : lat.mus;
  let html = svgField(active, muses);

  // optimal repair (min total entrenchment) from the driver
  const drop = (drv.repair && drv.repair.drop) || [];
  html += `<div class="fieldlabel">Optimal repair · least entrenchment to give up</div>`;
  html += `<div class="pos suggested"><h4><span class="star">★</span> drop ${drop.map((x) => `<code class="tok">${esc(short(x))}</code>`).join(' · ')} <span class="muted small">(weight ${esc(drv.repair ? drv.repair.weight : '?')})</span></h4>` +
    `<div class="keeps small">the cheapest way back to coherence by your entrenchment weights — a suggestion, not a verdict. The selection is yours.</div>` +
    `<div class="row"><button class="btn warm sm" id="applyrep">adopt this repair</button></div></div>`;

  if (!lat.capped) {
    html += `<div class="fieldlabel">Positions · maximal sets that cohere</div><div class="positions">`;
    lat.mss.forEach((p, i) => {
      const gives = active.filter((id) => !p.includes(id));
      const isSug = drop.length && gives.length === drop.length && drop.every((d) => gives.includes(d));
      html += `<div class="pos${isSug ? ' suggested' : ''}"><h4>${isSug ? '<span class="star">★</span>' : ''}Position ${String.fromCharCode(65 + i)} <span class="muted small">keeps ${p.length}/${active.length}</span></h4>` +
        `<div class="gives">concedes: ${gives.map((g) => `<code class="tok">${esc(short(g))}</code>`).join(' · ') || '—'}</div>` +
        `<div class="row"><button class="btn ghost sm" data-pos='${esc(JSON.stringify(gives))}'>adopt — retract the conceded</button></div></div>`;
    });
    html += `</div>`;
    html += `<div class="fieldlabel">Irreducible disagreements</div>`;
    lat.mus.forEach((m, k) => {
      html += `<div class="mus"><b>conflict ${k + 1}:</b> these cannot all hold — ${m.map((x) => `<code class="tok">${esc(short(x))}</code>`).join(' · ')}</div>`;
    });
  } else {
    html += `<div class="mus"><b>minimal conflict:</b> ${(drv.mus || []).map((x) => `<code class="tok">${esc(short(x))}</code>`).join(' · ')}</div>`;
  }
  field.innerHTML = html;

  $('#applyrep')?.addEventListener('click', () => { drop.forEach((id) => engine.retract(id)); refresh(); });
  field.querySelectorAll('button[data-pos]').forEach((b) => b.onclick = () => {
    JSON.parse(b.dataset.pos).forEach((id) => engine.retract(id)); refresh();
  });
}

function wire() {
  $('#seed').onclick = () => { engine.seed_demo(); refresh(); };
  $('#mkprompt').onclick = () => { $('#prompt').value = engine.prompt($('#nl').value || ''); };
  $('#copy').onclick = async () => {
    try { await navigator.clipboard.writeText($('#prompt').value); $('#copy').textContent = 'Copied'; setTimeout(() => ($('#copy').textContent = 'Copy'), 1200); }
    catch (_) { $('#prompt').select(); }
  };
  $('#ingest').onclick = () => {
    let r;
    try { r = JSON.parse(engine.ingest($('#json').value || '')); }
    catch (e) { $('#errs').innerHTML = '<div class="errbox">engine error: ' + esc(e) + '</div>'; return; }
    $('#errs').innerHTML = r.ok ? '' : '<div class="errbox">' + r.errors.map(esc).join('\n') + '</div>';
    if (r.ok) { $('#json').value = ''; }
    refresh();
  };
}

boot();
