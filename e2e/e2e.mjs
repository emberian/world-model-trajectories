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
await page.waitForFunction(() => /Flies/.test(document.querySelector('#field')?.textContent || ''), null, { timeout: 90000 }).catch(() => fail('forced consequence Flies(tweety) never rendered'));
console.log('· consistent: 3 claims, forced consequence shown');

// 2. introduce the contradiction via the IR loop
await page.evaluate(() => { document.querySelector('#loop').open = true; });
await page.fill('#json', PEN_NOFLY);
await page.click('#ingest');
await page.waitForFunction(() => /inconsistent/i.test(document.querySelector('#status')?.textContent || ''), null, { timeout: 90000 }).catch(() => fail('did not reach "inconsistent" after adding pen_nofly'));

const field = await page.$eval('#field', (e) => e.innerHTML);
const hasSvg = (await page.$$('#field svg')).length === 1;
if (!hasSvg) fail('no conflict SVG rendered');
if (!/Position\s*A/.test(field)) fail('no Position cards rendered');
if (!/irreducible disagreement|conflict 1/.test(field)) fail('no irreducible-disagreement listing');
if (!/★|Optimal repair/i.test(field)) fail('no optimal repair shown');
// dialectical colouring reached the claims
const colored = await page.$$eval('#claims .claim', (els) =>
  els.filter((e) => /necessary|contested|defeated/.test(e.className)).length);
if (colored < 4) fail('claims not dialectically coloured, got ' + colored);
console.log('· inconsistent: SVG + positions + disagreements + optimal repair + coloured claims');

// 3. adopt the optimal repair → back to coherent
await page.click('#applyrep');
await page.waitForFunction(() => /coherent/i.test(document.querySelector('#status')?.textContent || ''), null, { timeout: 90000 }).catch(() => fail('optimal-repair did not restore coherence'));
console.log('· optimal repair restores coherence');

if (errs.length) fail('console/page errors:\n' + errs.join('\n'));
console.log('PASS — full real-browser stack verified (wasm core + Z3-wasm + DOM + lattice)');
await browser.close();
process.exit(0);
