import { chromium } from 'playwright';

const BASE = process.env.BASE || 'http://localhost:8791/';
const PEN_NOFLY = JSON.stringify({
  claims: [{
    id: 'c_pen_nofly', source: 'Penguins cannot fly.', weight: 3,
    formula: { op: 'forall', vars: [{ name: 'x', sort: 'Thing' }],
      body: { op: 'imp',
        a: { op: 'pred', name: 'Penguin', args: [{ t: 'var', name: 'x' }] },
        b: { op: 'not', x: { op: 'pred', name: 'Flies', args: [{ t: 'var', name: 'x' }] } } } } }]
});

const browser = await chromium.launch({ ...(process.env.PW_CHANNEL?{channel:process.env.PW_CHANNEL}:{}),headless:true });
const page = await browser.newPage();
const errs = [];
page.on('pageerror', (e) => errs.push('PAGEERROR ' + e.message));
page.on('console', (m) => { if (m.type() === 'error') errs.push('CONSOLE ' + m.text()); });

function fail(msg) { console.log('FAIL: ' + msg); if (errs.length) console.log(errs.join('\n')); process.exit(1); }

await page.goto(BASE, { waitUntil: 'load' });
// Z3 loads ~34MB wasm — be patient.
await page.waitForFunction(() => /Z3 ready/.test(document.querySelector('#z3')?.textContent || ''), null, { timeout: 180000 }).catch(() => fail('Z3 never became ready'));
console.log('· Z3 ready');

// 1. consistent trajectory
await page.click('#seed');
await page.waitForFunction(() => /coherent/i.test(document.querySelector('#status')?.textContent || ''), null, { timeout: 90000 }).catch(() => fail('seed demo did not reach "coherent"'));
const claimN = await page.$$eval('#claims .claim', (e) => e.length);
if (claimN !== 3) fail('expected 3 seeded claims, got ' + claimN);
// forced consequences fill #field asynchronously after "coherent" shows
await page.waitForFunction(() => /because/.test(document.querySelector('#field')?.textContent || ''), null, { timeout: 90000 }).catch(() => fail('forced consequence + "because" witness never rendered'));
{
  const fld = await page.$eval('#field', (e) => e.textContent);
  if (!/Flies/.test(fld)) fail('expected Flies(tweety) forced, got ' + fld.slice(0, 140));
}
console.log('· consistent: 3 claims, forced consequence shown');

// 2. introduce the contradiction via the IR loop
await page.evaluate(() => { document.querySelector('#loop').open = true; });
await page.fill('#json', PEN_NOFLY);
await page.click('#ingest');
await page.waitForFunction(() => /inconsistent/i.test(document.querySelector('#status')?.textContent || ''), null, { timeout: 90000 }).catch(() => fail('did not reach "inconsistent" after adding pen_nofly'));

const field = await page.$eval('#field', (e) => e.innerHTML);
const hasSvg = (await page.$$('#field svg')).length >= 1;
if (!hasSvg) fail('no conflict SVG rendered');
if (!/Position\s*A/.test(field)) fail('no Position cards rendered');
if (!/irreducible disagreement|conflict 1/.test(field)) fail('no irreducible-disagreement listing');
if (!/★|Optimal repair/i.test(field)) fail('no optimal repair shown');
// dialectical colouring reached the claims
const colored = await page.$$eval('#claims .claim', (els) =>
  els.filter((e) => /necessary|contested|defeated/.test(e.className)).length);
if (colored < 4) fail('claims not dialectically coloured, got ' + colored);
console.log('· inconsistent: SVG + positions + disagreements + optimal repair + coloured claims');

// 3. argumentation-framework view (Increment B): attack graph + acceptance
{
  const svgs = (await page.$$('#field svg')).length;
  if (svgs < 2) fail('expected conflict SVG + attack-graph SVG, got ' + svgs);
  const f = await page.$eval('#field', (e) => e.textContent);
  if (!/Argumentation/.test(f)) fail('no argumentation section');
  if (!/skeptical/.test(f) || !/contested/.test(f) || !/defeated/.test(f)) fail('no acceptance summary');
  if (!/Dung/.test(f)) fail('argumentation honesty note missing');
}
console.log('· argumentation: attack graph + skeptical/contested/defeated + honest Dung note');

// 4. forkable trajectory tree (Increment C): save this (inconsistent)
//    state as a branch, deterministic from a cleared tree.
await page.evaluate(() => { try { localStorage.removeItem('wmt.tree.v2'); } catch (_) {} });
await page.fill('#branchname', 'in-conflict');
await page.click('#savebranch');
await page.waitForFunction(() => document.querySelectorAll('#branches .bnode').length === 1, null, { timeout: 5000 }).catch(() => fail('branch was not saved'));

// 5. adopt the optimal repair → back to coherent
await page.click('#applyrep');
await page.waitForFunction(() => /coherent/i.test(document.querySelector('#status')?.textContent || ''), null, { timeout: 90000 }).catch(() => fail('optimal-repair did not restore coherence'));
console.log('· optimal repair restores coherence');

// 6. save the repaired state, then compare the two branches side by side
await page.fill('#branchname', 'repaired');
await page.click('#savebranch');
await page.waitForFunction(() => document.querySelectorAll('#branches .bnode').length === 2, null, { timeout: 5000 }).catch(() => fail('second branch was not saved'));
await page.$$eval('#branches button[data-b="cmp"]', (bs) => bs.forEach((b) => b.click()));
{
  const cmp = await page.$eval('#cmp', (e) => e.textContent);
  if (!/Branch compare/.test(cmp)) fail('compare view did not render');
  if (!/inconsistent/.test(cmp) || !/coherent/.test(cmp)) fail('compare did not contrast the two branch summaries: ' + cmp.slice(0, 160));
  if (!/only in|reformulated|toggled/.test(cmp)) fail('compare did not show a claim-set delta');
}
console.log('· trajectory tree: fork + switch + side-by-side branch compare');

// 7. OpenRouter auto-formalize seam present, and the key-less path is
//    honest: it surfaces a clear message and makes NO network call.
//    (The live LLM round-trip is the external seam — deliberately not
//    asserted here; it needs a real key + service.)
await page.evaluate(() => { document.querySelector('#loop').open = true; });
if (!(await page.$('#autoform'))) fail('auto-formalize control missing');
let netHit = false;
page.on('request', (rq) => { if (/openrouter\.ai/.test(rq.url())) netHit = true; });
await page.fill('#orkey', '');
await page.fill('#nl', 'Some claim.');
await page.click('#autoform');
await page.waitForFunction(() => /OpenRouter API key/.test(document.querySelector('#orstat')?.textContent || ''), null, { timeout: 5000 }).catch(() => fail('key-less auto-formalize did not surface an honest error'));
if (netHit) fail('key-less auto-formalize must not call OpenRouter');
console.log('· auto-formalize: present; key-less path honest and offline');

if (errs.length) fail('console/page errors:\n' + errs.join('\n'));
console.log('PASS — full real-browser stack verified (wasm core + Z3-wasm + DOM + lattice + seam)');
await browser.close();
process.exit(0);
