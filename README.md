# world-model-trajectories

A consistency loop for a set of natural-language claims, built for
[@bananawalnutz](https://twitter.com/bananawalnutz)'s question: *parse claims
into programmable logic so that adding a claim computes contradictions
against the user's axiom set and a selection must be made — goal is
consistency, not truth.*

It is a sibling of [stella / svenvs](https://github.com/emberian): same
honesty discipline, same design language, no overclaim.

## The one idea

**The tool does not parse natural language. You + your own LLM do, in the
open, by copy-paste — and that round-trip *is* the seam, surfaced on
purpose.**

1. You type natural-language claims.
2. The tool builds a prompt (carrying your current typed vocabulary so the
   LLM reuses your symbols instead of inventing synonyms) — you paste it
   into whatever LLM you like.
3. You paste back a **typed many-sorted first-order IR as JSON** — *not*
   SMT-LIB2. (Models are reliable at structured JSON and unreliable at
   solver s-expressions; this also kills the "solver syntax error" failure
   mode.) You never read logic syntax: each claim is shown as your sentence
   plus a deterministic **plain-English rendering** of what it became,
   which you confirm.
4. A trusted, test-pinned Rust compiler turns the IR into SMT-LIB2 (a
   private compile target, never shown) and a real solver — **Z3 4.16,
   wasm, entirely in the browser tab** — drives:
   - the **minimal conflict**: the smallest set of claims that cannot all
     hold (assumption-core + deletion-shrink to a true MUS);
   - the **optimal repair**: the minimum-entrenchment-weight set of claims
     to give up, computed exactly over the conflict (you set the weights;
     the suggestion is yours to take or override — AGM selection);
   - **forced consequences**: atoms entailed by the whole set though no
     single claim asserts them.
5. Same claim id = revision (replace), not append. That is the trajectory.

The logic is real SMT — `Bool / Int / Real / = /` uninterpreted functions
/ quantifiers — not toy propositional. `x > 5` and `x < 3`, or quantified
`∀x. Penguin(x) ⇒ ¬Flies(x)` against `∀x. Bird(x) ⇒ Flies(x)`, are
detected contradictions a propositional engine could not see.

## Why this shape (the honest part)

General NL→logic *without manual intervention* is not reliable and this
tool does not pretend to do it. The faithfulness of the formalization is a
**seam**, and the only honest move is to make it cheap and visible rather
than hidden:

1. **NL → IR faithfulness** is the human+LLM step; you confirm the
   plain-English render, never logic syntax. The tool guarantees
   consistency *of the formalization*, never that it captures your
   sentence. That stays yours.
2. **Z3 may answer `unknown`** on hard quantified fragments. It is reported
   as `unknown` — never silently treated as consistent.
3. **Registry discipline** (reuse a symbol, don't mint a synonym — the
   single most common way contradiction-detection silently breaks) is
   enforced by Z3's own type-checker: a bad symbol surfaces as Z3's
   verbatim error, not a guess.

Goal: **consistency, not truth.** The tool never claims your claims are
correct — only whether they can all hold at once (the smallest, and the
only fully-mechanizable, part of the problem) and what they jointly force.

This is, deliberately, a *truth-maintenance system + AGM belief revision*
(Doyle/de&nbsp;Kleer/Alchourrón–Gärdenfors–Makinson; minimal-unsat-core =
Reiter's conflict sets). None of that is novel; the contribution is the
honest UX of the seam.

## Architecture

- `crate/` — `wmt-core`, a Rust crate compiled to wasm. It owns the typed
  IR, the **IR↔SMT-LIB2 compiler**, the **IR→English renderer**, the typed
  vocabulary, the claim trajectory, AGM selection/weights, the LLM prompt,
  and the analysis step-driver. **It does not solve.**
- The solver is **Z3** (vendored `z3-solver` wasm in `site/vendor/z3/`).
- `site/` — a static page (no server, no API keys, no build step to run
  it). The Rust→wasm core in `site/pkg/`; open `site/index.html` via any
  static host.

## What is verified, and how (no overclaim)

- The engine's correctness is tested **end-to-end against the native `z3`
  binary**: `cd crate && cargo test`. Eight tests: IR→SMT compiles & runs;
  the English render contains no solver syntax; a **quantified** penguin
  contradiction; the analysis driver yields the exact minimal conflict
  **and** the min-entrenchment optimal repair; a consistent set; a
  **beyond-propositional** arithmetic conflict; a forced-consequence
  entailment; same-id revision. (MaxSMT was tried and *rejected* — it
  hangs on quantifiers; the shipped design is assumption-core +
  Rust-side exact repair, which composes with quantifiers. That finding
  is in the commit history, not hidden.)
- The browser solver is the official `z3-solver` wasm; it was checked to
  return **byte-identical** results to that binary on the same scripts.
- What is *not* independently re-verified here is the static page wiring
  itself (standard ES-module + a classic `z3-built.js` script that
  registers the Z3 factory); it is plain, inspectable glue.

First load fetches ~34&nbsp;MB of Z3 wasm, then it is cached. Everything
runs locally in the tab; nothing is sent anywhere.

## Run it

```sh
cd crate && cargo test                 # prove the engine vs the z3 binary
wasm-pack build --release --target web --out-dir ../site/pkg   # rebuild wasm
cd ../site && python3 -m http.server   # then open http://localhost:8000
```

Or just open the deployed page and click **Load the penguin demo**.

## License

MIT OR Apache-2.0 for this project's code. Bundled Z3 is © Microsoft,
MIT (`site/vendor/z3/Z3-LICENSE.txt`).
