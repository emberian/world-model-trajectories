//! world-model-trajectories — wmt-core
//!
//! A consistency engine for a *human + their own LLM* loop. It does NOT
//! parse natural language. The human pastes this tool's prompt into
//! whatever LLM they like; the LLM returns a strict JSON formalization in
//! **SMT-LIB2**; the human pastes it back; this core maintains the claim
//! set, assembles the SMT-LIB2 program, and a real solver (**Z3**) reports:
//!
//!   * a **minimal conflict** — the smallest set of *named claims* that
//!     cannot all hold (Z3's `get-unsat-core`), and
//!   * **forced consequences** — declared boolean atoms entailed by the
//!     whole set though no single claim asserts them.
//!
//! The logic is full quantifier-free (and, where Z3 decides it, quantified)
//! SMT over `Bool/Int/Real/=`/uninterpreted functions — not toy
//! propositional. Three seams, all surfaced, none hidden:
//!   1. NL → SMT-LIB2 faithfulness is the human-mediated copy/paste step.
//!   2. Z3 may answer `unknown` on hard fragments — reported, never masked.
//!   3. The registry-reuse discipline is enforced by Z3's own type checker;
//!      a bad symbol surfaces as Z3's verbatim error, not a silent guess.
//! Goal: consistency of the formalization, not truth.
//!
//! The Rust core does NOT solve. It owns the model, the registry, the
//! trajectory, AGM selection, the prompt, and SMT assembly. The solver is
//! Z3 (the `z3` binary in native tests; `z3-solver` wasm in the browser).

use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use wasm_bindgen::prelude::*;

fn default_true() -> bool {
    true
}

/// An SMT-LIB2 declaration the claims share: a sort, const, or function.
/// `id` is the symbol the LLM must REUSE; `smtlib` is the literal
/// declaration line; `gloss` is its plain-English meaning.
#[derive(Clone, Serialize, Deserialize)]
pub struct Decl {
    pub id: String,
    pub smtlib: String,
    #[serde(default)]
    pub gloss: String,
}

#[derive(Clone, Serialize, Deserialize)]
pub struct Claim {
    pub id: String,
    #[serde(default)]
    pub source: String,
    #[serde(default)]
    pub gloss: String,
    /// One SMT-LIB2 boolean term — the content of the claim.
    pub smt: String,
    #[serde(default)]
    pub new_decls: Vec<Decl>,
    #[serde(default = "default_true")]
    pub active: bool,
}

#[derive(Deserialize)]
struct Ingest {
    #[serde(default)]
    decls: Vec<Decl>,
    claims: Vec<Claim>,
}

#[derive(Default)]
struct Core {
    claims: Vec<Claim>,
    /// id -> (smtlib decl line, gloss). Ordered, deduplicated by id.
    decls: BTreeMap<String, (String, String)>,
    decl_order: Vec<String>,
}

impl Core {
    fn active_idxs(&self) -> Vec<usize> {
        (0..self.claims.len())
            .filter(|&i| self.claims[i].active)
            .collect()
    }

    fn all_decls_block(&self) -> String {
        let mut s = String::new();
        for id in &self.decl_order {
            if let Some((smt, _)) = self.decls.get(id) {
                s.push_str(smt);
                s.push('\n');
            }
        }
        s
    }

    /// The SMT-LIB2 consistency program: declarations, every active claim
    /// asserted under its name (so `get-unsat-core` returns the minimal
    /// conflicting *claims*), then check-sat + get-unsat-core.
    pub fn smt_consistency(&self) -> String {
        let mut s = String::new();
        s.push_str("(set-option :produce-unsat-cores true)\n(set-logic ALL)\n");
        s.push_str(&self.all_decls_block());
        for &i in &self.active_idxs() {
            let c = &self.claims[i];
            s.push_str(&format!("(assert (! {} :named {}))\n", c.smt, c.id));
        }
        s.push_str("(check-sat)\n(get-unsat-core)\n");
        s
    }

    /// Consistency check WITHOUT requesting the core (one clean `sat` /
    /// `unsat` / `unknown` token — used first; the core script is only run
    /// when this says `unsat`).
    pub fn smt_check(&self) -> String {
        let mut s = String::new();
        s.push_str("(set-logic ALL)\n");
        s.push_str(&self.all_decls_block());
        for &i in &self.active_idxs() {
            s.push_str(&format!("(assert {})\n", self.claims[i].smt));
        }
        s.push_str("(check-sat)\n");
        s
    }

    /// SMT-LIB2 entailment query: is `term` forced by the active set?
    /// (active asserts) ∧ ¬term  unsat  ⟺  the set entails `term`.
    pub fn smt_entails(&self, term: &str) -> String {
        let mut s = String::new();
        s.push_str("(set-logic ALL)\n");
        s.push_str(&self.all_decls_block());
        for &i in &self.active_idxs() {
            s.push_str(&format!("(assert {})\n", self.claims[i].smt));
        }
        s.push_str(&format!("(assert (not {term}))\n(check-sat)\n"));
        s
    }

    /// Declared 0-ary Bool atoms — the ones we can auto-probe for "you
    /// never asserted this, but your set forces it".
    pub fn bool_atoms(&self) -> Vec<String> {
        self.decl_order
            .iter()
            .filter(|id| {
                self.decls
                    .get(*id)
                    .map(|(s, _)| {
                        let s = s.replace(char::is_whitespace, " ");
                        s.contains(&format!("declare-const {id} Bool"))
                            || s.contains(&format!("declare-fun {id} () Bool"))
                    })
                    .unwrap_or(false)
            })
            .cloned()
            .collect()
    }

    fn ingest(&mut self, json: &str) -> (bool, Vec<String>) {
        let ing: Ingest = match serde_json::from_str(json) {
            Ok(i) => i,
            Err(e) => {
                return (
                    false,
                    vec![format!("not valid JSON for the claim grammar: {e}")],
                )
            }
        };
        let mut errors = Vec::new();
        if ing.claims.is_empty() {
            errors.push("no claims in the pasted JSON".into());
        }
        for d in &ing.decls {
            if d.id.trim().is_empty() || d.smtlib.trim().is_empty() {
                errors.push("a decl has an empty id or smtlib".into());
            }
        }
        for c in &ing.claims {
            if c.id.trim().is_empty() {
                errors.push("a claim has an empty id".into());
            }
            if c.smt.trim().is_empty() {
                errors.push(format!("claim '{}' has an empty smt term", c.id));
            }
            for d in &c.new_decls {
                if d.id.trim().is_empty() || d.smtlib.trim().is_empty() {
                    errors.push(format!("claim '{}' has a malformed new_decl", c.id));
                }
            }
        }
        if !errors.is_empty() {
            return (false, errors);
        }
        // commit decls (batch-level then per-claim), dedup by id, keep order
        let mut add_decl = |id: &str, smt: &str, gloss: &str| {
            if !self.decls.contains_key(id) {
                self.decl_order.push(id.to_string());
            }
            self.decls
                .entry(id.to_string())
                .or_insert_with(|| (smt.to_string(), gloss.to_string()));
        };
        for d in &ing.decls {
            add_decl(&d.id, &d.smtlib, &d.gloss);
        }
        for c in &ing.claims {
            for d in &c.new_decls {
                add_decl(&d.id, &d.smtlib, &d.gloss);
            }
        }
        for c in ing.claims {
            if let Some(slot) = self.claims.iter_mut().find(|x| x.id == c.id) {
                *slot = c; // revision — the trajectory amends, not only appends
            } else {
                self.claims.push(c);
            }
        }
        (true, Vec::new())
    }

    fn set_active(&mut self, id: &str, v: bool) {
        if let Some(c) = self.claims.iter_mut().find(|c| c.id == id) {
            c.active = v;
        }
    }
    fn remove(&mut self, id: &str) {
        self.claims.retain(|c| c.id != id);
    }

    fn registry_view(&self) -> String {
        if self.decl_order.is_empty() {
            return "  (registry empty — you will declare what you need)\n".into();
        }
        let mut s = String::new();
        for id in &self.decl_order {
            if let Some((smt, g)) = self.decls.get(id) {
                s.push_str(&format!("  {id}  ::  {smt}   —  {g}\n"));
            }
        }
        s
    }

    fn prompt(&self, nl: &str) -> String {
        format!(
"You are a careful semiformalizer. Convert each natural-language claim below into\n\
SMT-LIB2 and return ONLY a JSON object of this exact shape:\n\
\n\
{{\"decls\":[{{\"id\":\"sym\",\"smtlib\":\"(declare-const sym Bool)\",\"gloss\":\"...\"}}],\n\
  \"claims\":[{{\"id\":\"c_slug\",\"source\":\"<the NL sentence verbatim>\",\n\
    \"gloss\":\"<=6 word label\",\"smt\":\"<one SMT-LIB2 Bool term>\",\n\
    \"new_decls\":[{{\"id\":\"sym\",\"smtlib\":\"(declare-fun age (Int) Int)\",\"gloss\":\"...\"}}]}}]}}\n\
\n\
Rules, most important first:\n\
1. REUSE ids from the registry below whenever the meaning matches. Minting a\n\
   synonym for something already declared is THE way this silently breaks\n\
   contradiction detection. Only declare genuinely-new symbols.\n\
2. Each claim's \"smt\" is ONE boolean term in SMT-LIB2 (logic ALL): you may\n\
   use Bool, Int, Real, =, and, or, not, =>, ite, uninterpreted functions,\n\
   and quantifiers (forall/exists) when needed. \"A implies B\" => \"(=> A B)\".\n\
3. Put every symbol you introduce in new_decls (or top-level decls) with a\n\
   declare-const / declare-fun / declare-sort line and a plain gloss.\n\
4. One claim object per natural-language statement; keep \"source\" verbatim.\n\
5. JSON only. No prose, no code fences.\n\
\n\
REGISTRY (id :: declaration — meaning):\n\
{}\n\
CLAIM(S) TO FORMALIZE:\n\
{}\n",
            self.registry_view(),
            nl
        )
    }

    fn seed_demo(&mut self) {
        // The classic: birds fly; penguins are birds; this is a penguin;
        // penguins don't fly. Consistent until the last is added.
        let demo = r#"{"decls":[
          {"id":"Bird","smtlib":"(declare-const Bird Bool)","gloss":"the thing is a bird"},
          {"id":"Flies","smtlib":"(declare-const Flies Bool)","gloss":"the thing can fly"},
          {"id":"Penguin","smtlib":"(declare-const Penguin Bool)","gloss":"the thing is a penguin"}],
          "claims":[
          {"id":"c_birds_fly","source":"Birds can fly.","gloss":"birds fly",
           "smt":"(=> Bird Flies)","new_decls":[]},
          {"id":"c_penguin_bird","source":"A penguin is a bird.","gloss":"penguin ⇒ bird",
           "smt":"(=> Penguin Bird)","new_decls":[]},
          {"id":"c_is_penguin","source":"This thing is a penguin.","gloss":"it is a penguin",
           "smt":"Penguin","new_decls":[]}]}"#;
        let _ = self.ingest(demo);
    }

    fn meta(&self) -> serde_json::Value {
        serde_json::json!({
            "claims": self.claims.iter().map(|c| serde_json::json!({
                "id": c.id, "source": c.source, "gloss": c.gloss,
                "smt": c.smt, "active": c.active,
            })).collect::<Vec<_>>(),
            "decls": self.decl_order.iter().filter_map(|id| {
                self.decls.get(id).map(|(s,g)|
                    serde_json::json!({"id": id, "smtlib": s, "gloss": g}))
            }).collect::<Vec<_>>(),
            "bool_atoms": self.bool_atoms(),
        })
    }
}

// ---- wasm facade ----------------------------------------------------------
// The browser drives Z3 (z3-solver wasm). This facade hands it the exact
// SMT-LIB2 to run and owns everything that is NOT solving.

#[wasm_bindgen]
pub struct WmtEngine {
    core: Core,
}

#[wasm_bindgen]
impl WmtEngine {
    #[wasm_bindgen(constructor)]
    pub fn new() -> WmtEngine {
        WmtEngine { core: Core::default() }
    }

    /// Ingest pasted JSON. `{ok, errors, meta}`.
    pub fn ingest(&mut self, json: &str) -> String {
        let (ok, errors) = self.core.ingest(json);
        serde_json::json!({"ok": ok, "errors": errors, "meta": self.core.meta()})
            .to_string()
    }

    pub fn retract(&mut self, id: &str) -> String {
        self.core.set_active(id, false);
        self.core.meta().to_string()
    }
    pub fn reactivate(&mut self, id: &str) -> String {
        self.core.set_active(id, true);
        self.core.meta().to_string()
    }
    pub fn remove(&mut self, id: &str) -> String {
        self.core.remove(id);
        self.core.meta().to_string()
    }
    pub fn meta(&self) -> String {
        self.core.meta().to_string()
    }
    pub fn seed_demo(&mut self) -> String {
        self.core.seed_demo();
        self.core.meta().to_string()
    }

    /// Clean sat/unsat/unknown check (run first).
    pub fn smt_check(&self) -> String {
        self.core.smt_check()
    }
    /// SMT-LIB2 with `get-unsat-core` (run only when smt_check is unsat).
    pub fn smt_consistency(&self) -> String {
        self.core.smt_consistency()
    }
    /// SMT-LIB2 to test whether the active set entails `term`.
    pub fn smt_entails(&self, term: &str) -> String {
        self.core.smt_entails(term)
    }
    pub fn prompt(&self, nl: &str) -> String {
        self.core.prompt(nl)
    }
}

impl Default for WmtEngine {
    fn default() -> Self {
        Self::new()
    }
}

// ---- native tests: REAL end-to-end against the `z3` binary ----------------

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;
    use std::process::{Command, Stdio};

    /// Run an SMT-LIB2 script through the real z3 binary. Returns its
    /// stdout lines, or None if z3 is not installed (test is then skipped
    /// with a printed notice — honest about what was and wasn't checked).
    fn z3(script: &str) -> Option<String> {
        let mut child = match Command::new("z3")
            .arg("-in")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
        {
            Ok(c) => c,
            Err(_) => {
                eprintln!("SKIP: z3 binary not found — engine assembly untested end-to-end");
                return None;
            }
        };
        child
            .stdin
            .as_mut()
            .unwrap()
            .write_all(script.as_bytes())
            .unwrap();
        let out = child.wait_with_output().unwrap();
        Some(String::from_utf8_lossy(&out.stdout).to_string())
    }

    #[test]
    fn consistent_set_checks_sat() {
        let mut c = Core::default();
        assert!(c.ingest(
            r#"{"decls":[{"id":"P","smtlib":"(declare-const P Bool)","gloss":"p"}],
                 "claims":[{"id":"c1","smt":"P"}]}"#
        ).0);
        if let Some(o) = z3(&c.smt_consistency()) {
            assert!(o.starts_with("sat"), "z3 said: {o}");
        }
    }

    #[test]
    fn penguin_contradiction_unsat_core_is_the_minimal_claims() {
        let mut c = Core::default();
        c.seed_demo();
        if let Some(o) = z3(&c.smt_consistency()) {
            assert!(o.starts_with("sat"), "pre-conflict should be sat: {o}");
        }
        assert!(c.ingest(
            r#"{"claims":[{"id":"c_pen_nofly","source":"Penguins cannot fly.",
                 "smt":"(=> Penguin (not Flies))"}]}"#
        ).0);
        if let Some(o) = z3(&c.smt_consistency()) {
            assert!(o.starts_with("unsat"), "should be unsat: {o}");
            for id in ["c_birds_fly", "c_penguin_bird", "c_is_penguin", "c_pen_nofly"] {
                assert!(o.contains(id), "unsat core missing {id}: {o}");
            }
        }
    }

    #[test]
    fn forced_consequence_via_entailment() {
        // penguin ⇒ bird ⇒ flies, and it is a penguin: Flies is forced,
        // though no claim asserts Flies on its own.
        let mut c = Core::default();
        c.seed_demo();
        assert_eq!(c.bool_atoms(), vec!["Bird", "Flies", "Penguin"]);
        if let Some(o) = z3(&c.smt_entails("Flies")) {
            assert!(o.starts_with("unsat"), "Flies should be entailed: {o}");
        }
        if let Some(o) = z3(&c.smt_entails("(not Flies)")) {
            assert!(o.starts_with("sat"), "(not Flies) not entailed: {o}");
        }
    }

    #[test]
    fn agm_retract_restores_consistency() {
        let mut c = Core::default();
        c.seed_demo();
        c.ingest(r#"{"claims":[{"id":"c_pen_nofly","smt":"(=> Penguin (not Flies))"}]}"#);
        c.set_active("c_birds_fly", false); // user's selection
        if let Some(o) = z3(&c.smt_consistency()) {
            assert!(o.starts_with("sat"), "retraction should restore sat: {o}");
        }
    }

    #[test]
    fn beyond_propositional_arithmetic_conflict() {
        // This is the point of using a real solver: x>5 ∧ x<3 is a
        // contradiction no propositional engine could see.
        let mut c = Core::default();
        assert!(c.ingest(
            r#"{"decls":[{"id":"x","smtlib":"(declare-const x Int)","gloss":"the number x"}],
                 "claims":[
                  {"id":"c_big","source":"x is more than five.","smt":"(> x 5)"},
                  {"id":"c_small","source":"x is less than three.","smt":"(< x 3)"}]}"#
        ).0);
        if let Some(o) = z3(&c.smt_consistency()) {
            assert!(o.starts_with("unsat"), "x>5 ∧ x<3 must be unsat: {o}");
            assert!(o.contains("c_big") && o.contains("c_small"), "core: {o}");
        }
    }

    #[test]
    fn revision_replaces_same_id() {
        let mut c = Core::default();
        c.ingest(
            r#"{"decls":[{"id":"P","smtlib":"(declare-const P Bool)","gloss":"p"}],
                 "claims":[{"id":"c1","smt":"P"}]}"#,
        );
        c.ingest(r#"{"claims":[{"id":"c1","smt":"(not P)"}]}"#);
        assert_eq!(c.claims.len(), 1);
        if let Some(o) = z3(&c.smt_consistency()) {
            assert!(o.starts_with("sat"), "lone ¬P is sat: {o}");
        }
    }

    #[test]
    fn empty_smt_is_rejected_surfaced_not_guessed() {
        let mut c = Core::default();
        let (ok, e) = c.ingest(r#"{"claims":[{"id":"c1","smt":"  "}]}"#);
        assert!(!ok);
        assert!(e.iter().any(|m| m.contains("empty smt")), "{e:?}");
    }
}
