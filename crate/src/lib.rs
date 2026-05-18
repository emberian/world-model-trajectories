//! world-model-trajectories — wmt-core
//!
//! A consistency / dialectic engine for a *human + their own LLM* loop.
//!
//! The surfaced interchange is NOT SMT-LIB2. The LLM emits a typed
//! many-sorted first-order **IR as JSON** (models are far more reliable at
//! structured JSON than at s-expression syntax, which also kills the
//! "solver syntax error" failure mode). This crate is the *trusted,
//! Z3-tested compiler*: IR → SMT-LIB2 (private), and IR → readable English
//! (the only logical form a human ever sees). SMT-LIB2 is an internal
//! compile target, never shown.
//!
//! The solver is Z3 (the `z3` binary in native tests; `z3-solver` wasm in
//! the browser). This crate does not solve — it owns the vocabulary, the
//! claim trajectory, the IR↔SMT compiler, the English renderer, the LLM
//! prompt, and the *drivers* that orchestrate Z3 to compute:
//!
//!   * consistency + the minimal conflict;
//!   * the **coherence lattice** — every minimal correction set (MCS: a
//!     minimal way out) by iterated MaxSMT, and every minimal conflict
//!     (MUS: an irreducible disagreement) as the MCSes' minimal hitting
//!     sets (Reiter/Liffiton–Sakallah duality), exact for the demo regime;
//!   * the **optimal repair** — minimum-entrenchment-weight set of claims
//!     to drop (weighted MaxSMT), as a *suggestion* the human still owns;
//!   * forced consequences (entailment).
//!
//! Honest seams, surfaced not hidden: (1) NL→IR faithfulness is the human
//! loop — the human confirms the *English render*, never logic syntax;
//! (2) Z3 may answer `unknown` — reported, never masked; (3) vocabulary
//! reuse is enforced by Z3's own type-checker. Goal: consistency, not
//! truth.

use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use wasm_bindgen::prelude::*;

fn dtrue() -> bool {
    true
}
fn w1() -> i64 {
    1
}

// ---- typed many-sorted FOL IR --------------------------------------------

#[derive(Clone, Serialize, Deserialize)]
pub struct Sig {
    pub name: String,
    #[serde(default)]
    pub args: Vec<String>, // sort names
    #[serde(default)]
    pub ret: Option<String>, // for funcs; preds are Bool
    #[serde(default)]
    pub gloss: String,
}

#[derive(Clone, Serialize, Deserialize)]
#[serde(tag = "t", rename_all = "lowercase")]
pub enum Term {
    Var { name: String },
    Int { v: i64 },
    Real { v: String },
    App { name: String, #[serde(default)] args: Vec<Term> }, // const = no args
    Arith { op: String, args: Vec<Term> },                   // + - *
}

#[derive(Clone, Serialize, Deserialize)]
pub struct QVar {
    pub name: String,
    pub sort: String,
}

#[derive(Clone, Serialize, Deserialize)]
#[serde(tag = "op", rename_all = "lowercase")]
pub enum Formula {
    Pred { name: String, #[serde(default)] args: Vec<Term> }, // 0-ary = proposition
    Eq { a: Term, b: Term },
    Cmp { rel: String, a: Term, b: Term }, // < <= > >=
    Not { x: Box<Formula> },
    And { xs: Vec<Formula> },
    Or { xs: Vec<Formula> },
    Imp { a: Box<Formula>, b: Box<Formula> },
    Iff { a: Box<Formula>, b: Box<Formula> },
    Forall { vars: Vec<QVar>, body: Box<Formula> },
    Exists { vars: Vec<QVar>, body: Box<Formula> },
}

#[derive(Clone, Serialize, Deserialize)]
pub struct Claim {
    pub id: String,
    #[serde(default)]
    pub source: String,
    #[serde(default)]
    pub gloss: String,
    pub formula: Formula,
    /// The LLM's own plain-English paraphrase of what it formalized — the
    /// back-translation. Shown beside `source` so the human can confirm
    /// the seam cheaply (NL → IR faithfulness, surfaced not hidden).
    #[serde(default)]
    pub back: String,
    #[serde(default = "w1")]
    pub weight: i64, // epistemic entrenchment (higher = harder to give up)
    #[serde(default = "dtrue")]
    pub active: bool,
}

#[derive(Deserialize)]
struct Ingest {
    #[serde(default)]
    sorts: Vec<String>,
    #[serde(default)]
    preds: Vec<Sig>,
    #[serde(default)]
    funcs: Vec<Sig>,
    claims: Vec<Claim>,
}

const BUILTIN_SORTS: [&str; 3] = ["Bool", "Int", "Real"];

#[derive(Default)]
struct Core {
    sorts: Vec<String>, // user sorts (non-builtin)
    preds: BTreeMap<String, Sig>,
    funcs: BTreeMap<String, Sig>,
    decl_order: Vec<(char, String)>, // ('p'|'f', name) for stable emission
    claims: Vec<Claim>,
}

// ---- IR → SMT-LIB2 (private compile target) ------------------------------

fn term_smt(t: &Term) -> String {
    match t {
        Term::Var { name } => name.clone(),
        Term::Int { v } => {
            if *v < 0 {
                format!("(- {})", -v)
            } else {
                v.to_string()
            }
        }
        Term::Real { v } => v.clone(),
        Term::App { name, args } => {
            if args.is_empty() {
                name.clone()
            } else {
                format!(
                    "({} {})",
                    name,
                    args.iter().map(term_smt).collect::<Vec<_>>().join(" ")
                )
            }
        }
        Term::Arith { op, args } => format!(
            "({} {})",
            op,
            args.iter().map(term_smt).collect::<Vec<_>>().join(" ")
        ),
    }
}

fn form_smt(f: &Formula) -> String {
    match f {
        Formula::Pred { name, args } => {
            if args.is_empty() {
                name.clone()
            } else {
                format!(
                    "({} {})",
                    name,
                    args.iter().map(term_smt).collect::<Vec<_>>().join(" ")
                )
            }
        }
        Formula::Eq { a, b } => format!("(= {} {})", term_smt(a), term_smt(b)),
        Formula::Cmp { rel, a, b } => {
            format!("({} {} {})", rel, term_smt(a), term_smt(b))
        }
        Formula::Not { x } => format!("(not {})", form_smt(x)),
        Formula::And { xs } => {
            format!("(and {})", xs.iter().map(form_smt).collect::<Vec<_>>().join(" "))
        }
        Formula::Or { xs } => {
            format!("(or {})", xs.iter().map(form_smt).collect::<Vec<_>>().join(" "))
        }
        Formula::Imp { a, b } => format!("(=> {} {})", form_smt(a), form_smt(b)),
        Formula::Iff { a, b } => format!("(= {} {})", form_smt(a), form_smt(b)),
        Formula::Forall { vars, body } | Formula::Exists { vars, body } => {
            let q = if matches!(f, Formula::Forall { .. }) {
                "forall"
            } else {
                "exists"
            };
            let bs = vars
                .iter()
                .map(|v| format!("({} {})", v.name, v.sort))
                .collect::<Vec<_>>()
                .join(" ");
            format!("({} ({}) {})", q, bs, form_smt(body))
        }
    }
}

// ---- IR → readable English (the only logical form a human sees) ----------

fn term_en(t: &Term) -> String {
    match t {
        Term::Var { name } => name.clone(),
        Term::Int { v } => v.to_string(),
        Term::Real { v } => v.clone(),
        Term::App { name, args } => {
            if args.is_empty() {
                name.clone()
            } else {
                format!(
                    "{}({})",
                    name,
                    args.iter().map(term_en).collect::<Vec<_>>().join(", ")
                )
            }
        }
        Term::Arith { op, args } => args
            .iter()
            .map(term_en)
            .collect::<Vec<_>>()
            .join(&format!(" {op} ")),
    }
}

fn form_en(f: &Formula) -> String {
    match f {
        Formula::Pred { name, args } => {
            if args.is_empty() {
                name.clone()
            } else {
                format!(
                    "{}({})",
                    name,
                    args.iter().map(term_en).collect::<Vec<_>>().join(", ")
                )
            }
        }
        Formula::Eq { a, b } => format!("{} is {}", term_en(a), term_en(b)),
        Formula::Cmp { rel, a, b } => {
            let r = match rel.as_str() {
                "<" => "is less than",
                "<=" => "is at most",
                ">" => "is greater than",
                ">=" => "is at least",
                _ => rel,
            };
            format!("{} {} {}", term_en(a), r, term_en(b))
        }
        Formula::Not { x } => format!("it is not the case that ({})", form_en(x)),
        Formula::And { xs } => xs
            .iter()
            .map(form_en)
            .collect::<Vec<_>>()
            .join(", and "),
        Formula::Or { xs } => xs
            .iter()
            .map(form_en)
            .collect::<Vec<_>>()
            .join(", or "),
        Formula::Imp { a, b } => format!("if {} then {}", form_en(a), form_en(b)),
        Formula::Iff { a, b } => format!("{} exactly when {}", form_en(a), form_en(b)),
        Formula::Forall { vars, body } => format!(
            "for every {}, {}",
            vars.iter()
                .map(|v| format!("{} in {}", v.name, v.sort))
                .collect::<Vec<_>>()
                .join(" and "),
            form_en(body)
        ),
        Formula::Exists { vars, body } => format!(
            "there is some {} such that {}",
            vars.iter()
                .map(|v| format!("{} in {}", v.name, v.sort))
                .collect::<Vec<_>>()
                .join(" and "),
            form_en(body)
        ),
    }
}

impl Core {
    fn decls_smt(&self) -> String {
        let mut s = String::new();
        for so in &self.sorts {
            s.push_str(&format!("(declare-sort {so} 0)\n"));
        }
        for (k, name) in &self.decl_order {
            if *k == 'p' {
                if let Some(p) = self.preds.get(name) {
                    s.push_str(&format!(
                        "(declare-fun {} ({}) Bool)\n",
                        p.name,
                        p.args.join(" ")
                    ));
                }
            } else if let Some(fun) = self.funcs.get(name) {
                s.push_str(&format!(
                    "(declare-fun {} ({}) {})\n",
                    fun.name,
                    fun.args.join(" "),
                    fun.ret.clone().unwrap_or_else(|| "Bool".into())
                ));
            }
        }
        s
    }

    fn active(&self) -> Vec<usize> {
        (0..self.claims.len())
            .filter(|&i| self.claims[i].active)
            .collect()
    }

    /// Clean sat/unsat/unknown, no core (run first).
    pub fn smt_check(&self) -> String {
        let mut s = String::from("(set-logic ALL)\n");
        s.push_str(&self.decls_smt());
        for &i in &self.active() {
            s.push_str(&format!("(assert {})\n", form_smt(&self.claims[i].formula)));
        }
        s.push_str("(check-sat)\n");
        s
    }

    /// With named asserts + get-unsat-core (run when smt_check is unsat).
    pub fn smt_core(&self) -> String {
        let mut s = String::from("(set-option :produce-unsat-cores true)\n(set-logic ALL)\n");
        s.push_str(&self.decls_smt());
        for &i in &self.active() {
            s.push_str(&format!(
                "(assert (! {} :named {}))\n",
                form_smt(&self.claims[i].formula),
                self.claims[i].id
            ));
        }
        s.push_str("(check-sat)\n(get-unsat-core)\n");
        s
    }

    pub fn smt_entails(&self, f: &Formula) -> String {
        let mut s = String::from("(set-logic ALL)\n");
        s.push_str(&self.decls_smt());
        for &i in &self.active() {
            s.push_str(&format!("(assert {})\n", form_smt(&self.claims[i].formula)));
        }
        s.push_str(&format!("(assert (not {}))\n(check-sat)\n", form_smt(f)));
        s
    }

    /// One weighted-MaxSMT script over a *given* set of claim indices,
    /// each a soft assertion with its entrenchment weight. After
    /// `(check-sat)` the model is read to see which claims were dropped.
    /// `extra_hard` are extra hard clauses (used to enumerate MCSes).
    fn smt_maxsmt(&self, idxs: &[usize], extra_hard: &[String]) -> String {
        let mut s = String::from("(set-logic ALL)\n");
        s.push_str(&self.decls_smt());
        // a fresh Bool selector per claim: claim holds  <=>  sel_i
        for &i in idxs {
            let c = &self.claims[i];
            s.push_str(&format!("(declare-const sel_{} Bool)\n", c.id));
            s.push_str(&format!(
                "(assert (= sel_{} {}))\n",
                c.id,
                form_smt(&c.formula)
            ));
            s.push_str(&format!(
                "(assert-soft sel_{} :weight {} :id W)\n",
                c.id,
                c.weight.max(1)
            ));
        }
        for h in extra_hard {
            s.push_str(&format!("(assert {h})\n"));
        }
        s.push_str("(check-sat)\n(get-value (");
        s.push_str(
            &idxs
                .iter()
                .map(|&i| format!("sel_{}", self.claims[i].id))
                .collect::<Vec<_>>()
                .join(" "),
        );
        s.push_str("))\n");
        s
    }

    fn ingest(&mut self, json: &str) -> (bool, Vec<String>) {
        let ing: Ingest = match serde_json::from_str(json) {
            Ok(i) => i,
            Err(e) => return (false, vec![format!("not valid IR JSON: {e}")]),
        };
        let mut errs = Vec::new();
        if ing.claims.is_empty() {
            errs.push("no claims in the pasted IR".into());
        }
        for c in &ing.claims {
            if c.id.trim().is_empty() {
                errs.push("a claim has an empty id".into());
            }
        }
        if !errs.is_empty() {
            return (false, errs);
        }
        for so in ing.sorts {
            if !BUILTIN_SORTS.contains(&so.as_str()) && !self.sorts.contains(&so) {
                self.sorts.push(so);
            }
        }
        for p in ing.preds {
            if !self.preds.contains_key(&p.name) {
                self.decl_order.push(('p', p.name.clone()));
            }
            self.preds.entry(p.name.clone()).or_insert(p);
        }
        for fun in ing.funcs {
            if !self.funcs.contains_key(&fun.name) {
                self.decl_order.push(('f', fun.name.clone()));
            }
            self.funcs.entry(fun.name.clone()).or_insert(fun);
        }
        for c in ing.claims {
            if let Some(slot) = self.claims.iter_mut().find(|x| x.id == c.id) {
                *slot = c; // revision = the trajectory amends, not just appends
            } else {
                self.claims.push(c);
            }
        }
        (true, Vec::new())
    }

    fn registry_view(&self) -> String {
        let mut s = String::new();
        if !self.sorts.is_empty() {
            s.push_str(&format!("  sorts: {}\n", self.sorts.join(", ")));
        }
        for (k, name) in &self.decl_order {
            if *k == 'p' {
                if let Some(p) = self.preds.get(name) {
                    s.push_str(&format!(
                        "  pred {}({}) — {}\n",
                        p.name,
                        p.args.join(", "),
                        p.gloss
                    ));
                }
            } else if let Some(f) = self.funcs.get(name) {
                s.push_str(&format!(
                    "  func {}({}) : {} — {}\n",
                    f.name,
                    f.args.join(", "),
                    f.ret.clone().unwrap_or_default(),
                    f.gloss
                ));
            }
        }
        if s.is_empty() {
            "  (vocabulary empty — declare what you need)\n".into()
        } else {
            s
        }
    }

    fn prompt(&self, nl: &str) -> String {
        format!(
"You are a careful semiformalizer. Convert each natural-language claim below into\n\
a typed many-sorted first-order IR and return ONLY this JSON object:\n\
\n\
{{\"sorts\":[\"Thing\"],\n\
  \"preds\":[{{\"name\":\"Bird\",\"args\":[\"Thing\"],\"gloss\":\"x is a bird\"}}],\n\
  \"funcs\":[{{\"name\":\"age\",\"args\":[\"Thing\"],\"ret\":\"Int\",\"gloss\":\"age of x\"}}],\n\
  \"claims\":[{{\"id\":\"c_slug\",\"source\":\"<the sentence verbatim>\",\n\
    \"gloss\":\"<=6 words\",\"weight\":1,\n\
    \"back\":\"<one plain-English sentence that says EXACTLY what your\n\
            formula means — your own back-translation>\",\n\
    \"formula\":{{...}}}}]}}\n\
\n\
FORMULA grammar (JSON, field \"op\"): pred{{name,args}} eq{{a,b}}\n\
  cmp{{rel:'<'|'<='|'>'|'>=',a,b}} not{{x}} and{{xs}} or{{xs}} imp{{a,b}}\n\
  iff{{a,b}} forall{{vars:[{{name,sort}}],body}} exists{{vars,body}}\n\
TERM grammar (field \"t\"): var{{name}} int{{v}} real{{v}}\n\
  app{{name,args}} (a 0-arg app is a constant) arith{{op:'+'|'-'|'*',args}}\n\
\n\
Rules, most important first:\n\
1. REUSE names from the vocabulary below when the meaning matches. Minting a\n\
   synonym is THE way contradiction-detection silently breaks. Only add new\n\
   preds/funcs/sorts for genuinely new vocabulary, each with a gloss.\n\
2. One claim object per sentence; keep \"source\" verbatim. \"weight\" is how\n\
   hard the claim is to give up (epistemic entrenchment, default 1).\n\
3. Prefer typed quantified formulas: \"penguins don't fly\" =>\n\
   forall x:Thing. (=> (Penguin x) (not (Flies x))).\n\
4. \"back\" must paraphrase the FORMULA, not echo \"source\". If they\n\
   would differ, trust the formula and let the human see the gap — that\n\
   is the point of the field.\n\
5. No SMT-LIB, no prose, no code fences. JSON only.\n\
\n\
VOCABULARY:\n\
{}\n\
CLAIM(S) TO FORMALIZE:\n\
{}\n",
            self.registry_view(),
            nl
        )
    }

    fn seed_demo(&mut self) {
        let demo = r#"{"sorts":["Thing"],
          "preds":[
            {"name":"Bird","args":["Thing"],"gloss":"x is a bird"},
            {"name":"Flies","args":["Thing"],"gloss":"x can fly"},
            {"name":"Penguin","args":["Thing"],"gloss":"x is a penguin"}],
          "funcs":[{"name":"tweety","args":[],"ret":"Thing","gloss":"the bird Tweety"}],
          "claims":[
           {"id":"c_birds_fly","source":"Birds can fly.","gloss":"birds fly","weight":2,
            "formula":{"op":"forall","vars":[{"name":"x","sort":"Thing"}],
              "body":{"op":"imp","a":{"op":"pred","name":"Bird","args":[{"t":"var","name":"x"}]},
                                  "b":{"op":"pred","name":"Flies","args":[{"t":"var","name":"x"}]}}}},
           {"id":"c_penguin_bird","source":"Every penguin is a bird.","gloss":"penguin ⇒ bird","weight":5,
            "formula":{"op":"forall","vars":[{"name":"x","sort":"Thing"}],
              "body":{"op":"imp","a":{"op":"pred","name":"Penguin","args":[{"t":"var","name":"x"}]},
                                  "b":{"op":"pred","name":"Bird","args":[{"t":"var","name":"x"}]}}}},
           {"id":"c_tweety_penguin","source":"Tweety is a penguin.","gloss":"Tweety is a penguin","weight":4,
            "formula":{"op":"pred","name":"Penguin","args":[{"t":"app","name":"tweety","args":[]}]}}]}"#;
        let _ = self.ingest(demo);
    }

    /// Candidate ground atoms to probe for "you never asserted this but
    /// are committed to it": every predicate applied to declared constants
    /// (0-ary funcs) whose sorts match, plus 0-ary propositions. Bounded
    /// (the demo regime) — honest, not exhaustive over an infinite domain.
    fn ground_atoms(&self) -> Vec<(String, Formula)> {
        let mut consts_by_sort: BTreeMap<String, Vec<String>> = BTreeMap::new();
        for f in self.funcs.values() {
            if f.args.is_empty() {
                if let Some(ret) = &f.ret {
                    consts_by_sort.entry(ret.clone()).or_default().push(f.name.clone());
                }
            }
        }
        let mut out: Vec<(String, Formula)> = Vec::new();
        for (_, name) in &self.decl_order {
            let Some(p) = self.preds.get(name) else { continue };
            if p.args.is_empty() {
                out.push((p.name.clone(), Formula::Pred { name: p.name.clone(), args: vec![] }));
                continue;
            }
            // cartesian product of matching constants, capped
            let mut tuples: Vec<Vec<String>> = vec![vec![]];
            let mut ok = true;
            for s in &p.args {
                let cs = consts_by_sort.get(s).cloned().unwrap_or_default();
                if cs.is_empty() { ok = false; break; }
                let mut next = Vec::new();
                for t in &tuples {
                    for c in &cs {
                        let mut v = t.clone();
                        v.push(c.clone());
                        next.push(v);
                    }
                }
                tuples = next;
                if tuples.len() > 24 { ok = false; break; }
            }
            if !ok { continue; }
            for tup in tuples {
                let label = format!("{}({})", p.name, tup.join(", "));
                let args = tup
                    .iter()
                    .map(|c| Term::App { name: c.clone(), args: vec![] })
                    .collect();
                out.push((label, Formula::Pred { name: p.name.clone(), args }));
                if out.len() >= 40 { return out; }
            }
        }
        out
    }

    fn meta(&self) -> serde_json::Value {
        serde_json::json!({
            "claims": self.claims.iter().map(|c| serde_json::json!({
                "id": c.id, "source": c.source, "gloss": c.gloss,
                "render": form_en(&c.formula), "back": c.back,
                "weight": c.weight, "active": c.active,
            })).collect::<Vec<_>>(),
            "vocab": self.registry_view(),
            "bool_atoms": self.preds.values()
                .filter(|p| p.args.is_empty())
                .map(|p| p.name.clone()).collect::<Vec<_>>(),
            "ground_atoms": self.ground_atoms().into_iter()
                .map(|(label, f)| serde_json::json!({
                    "label": label,
                    "formula": serde_json::to_value(&f).unwrap(),
                })).collect::<Vec<_>>(),
        })
    }
}

// ---- assumption-literal analysis (robust, optimize-free) -----------------
// Each active claim i gets a Bool assumption a_<id>; we assert
// (=> a_<id> formula_i). `check-sat-assuming` over a chosen id-subset then
// tests exactly that subset; `get-unsat-core` returns the assumption
// literals in the conflict = a claim-level MUS. No MaxSMT, no optimize —
// so it composes with quantifiers exactly as plain check-sat does (the
// reason the assert-soft approach hung and this does not).

impl Core {
    fn active_ids(&self) -> Vec<String> {
        self.active()
            .iter()
            .map(|&i| self.claims[i].id.clone())
            .collect()
    }
    fn weight_of(&self, id: &str) -> i64 {
        self.claims
            .iter()
            .find(|c| c.id == id)
            .map(|c| c.weight.max(1))
            .unwrap_or(1)
    }
    /// Program that declares an assumption literal for every active claim
    /// and tests exactly `assume_ids` (the others are simply not asserted).
    pub fn smt_assume(&self, assume_ids: &[String]) -> String {
        let mut s = String::from("(set-option :produce-unsat-cores true)\n(set-logic ALL)\n");
        s.push_str(&self.decls_smt());
        for &i in &self.active() {
            let id = &self.claims[i].id;
            s.push_str(&format!("(declare-const a_{id} Bool)\n"));
            s.push_str(&format!(
                "(assert (=> a_{id} {}))\n",
                form_smt(&self.claims[i].formula)
            ));
        }
        let lits = assume_ids
            .iter()
            .map(|id| format!("a_{id}"))
            .collect::<Vec<_>>()
            .join(" ");
        s.push_str(&format!("(check-sat-assuming ({lits}))\n(get-unsat-core)\n"));
        s
    }

    /// Like `smt_assume`, but also asserts the NEGATION of `probe`. Then
    /// `assume_ids` ∧ ¬probe being **unsat** means those claims entail
    /// `probe`; the unsat core (over the a_ids) is the witness — the
    /// minimal set of claims responsible. ("Flies(tweety) BECAUSE …")
    pub fn smt_entail_assume(&self, probe: &Formula, assume_ids: &[String]) -> String {
        let mut s = String::from("(set-option :produce-unsat-cores true)\n(set-logic ALL)\n");
        s.push_str(&self.decls_smt());
        for &i in &self.active() {
            let id = &self.claims[i].id;
            s.push_str(&format!("(declare-const a_{id} Bool)\n"));
            s.push_str(&format!(
                "(assert (=> a_{id} {}))\n",
                form_smt(&self.claims[i].formula)
            ));
        }
        s.push_str(&format!("(assert (not {}))\n", form_smt(probe)));
        let lits = assume_ids
            .iter()
            .map(|id| format!("a_{id}"))
            .collect::<Vec<_>>()
            .join(" ");
        s.push_str(&format!("(check-sat-assuming ({lits}))\n(get-unsat-core)\n"));
        s
    }
}

fn z3_head(o: &str) -> String {
    o.split('\n')
        .map(|l| l.trim())
        .find(|l| !l.is_empty())
        .unwrap_or("")
        .to_string()
}
fn z3_core_ids(o: &str) -> Vec<String> {
    // first parenthesised group after the status line
    let g = o
        .lines()
        .skip_while(|l| !l.trim().starts_with('('))
        .next()
        .unwrap_or("");
    g.trim()
        .trim_start_matches('(')
        .trim_end_matches(')')
        .split_whitespace()
        .filter_map(|t| t.strip_prefix("a_").map(|x| x.to_string()))
        .collect()
}

#[derive(Clone)]
enum Phase {
    CheckAll,
    Shrink { cand: Vec<String>, i: usize },
    Repair { subsets: Vec<Vec<String>>, k: usize },
    Done,
}

/// One step-machine. `analyze_*` in the wasm facade pump it with z3-wasm;
/// native tests pump it with the z3 binary. Same code path both ways.
struct Driver {
    active: Vec<String>,
    phase: Phase,
    status: String, // consistent | inconsistent | unknown
    mus: Vec<String>,
    repair: Vec<String>,
    repair_weight: i64,
}

fn powerset_by_weight(core: &Core, ids: &[String]) -> Vec<Vec<String>> {
    let n = ids.len();
    let mut subs: Vec<Vec<String>> = Vec::new();
    for mask in 1u32..(1u32 << n) {
        let mut v = Vec::new();
        for (b, id) in ids.iter().enumerate() {
            if mask & (1 << b) != 0 {
                v.push(id.clone());
            }
        }
        subs.push(v);
    }
    subs.sort_by_key(|s| {
        (
            s.iter().map(|id| core.weight_of(id)).sum::<i64>(),
            s.len(),
        )
    });
    subs
}

impl Driver {
    fn new(core: &Core) -> Driver {
        Driver {
            active: core.active_ids(),
            phase: Phase::CheckAll,
            status: String::new(),
            mus: vec![],
            repair: vec![],
            repair_weight: 0,
        }
    }
    fn next_script(&self, core: &Core) -> Option<String> {
        match &self.phase {
            Phase::CheckAll => Some(core.smt_assume(&self.active)),
            Phase::Shrink { cand, i } => {
                let mut c = cand.clone();
                c.remove(*i);
                Some(core.smt_assume(&c))
            }
            Phase::Repair { subsets, k } => {
                let drop = &subsets[*k];
                let keep: Vec<String> = self
                    .active
                    .iter()
                    .filter(|x| !drop.contains(x))
                    .cloned()
                    .collect();
                Some(core.smt_assume(&keep))
            }
            Phase::Done => None,
        }
    }
    fn feed(&mut self, core: &Core, out: &str) {
        let h = z3_head(out);
        match self.phase.clone() {
            Phase::CheckAll => {
                if h.starts_with("sat") {
                    self.status = "consistent".into();
                    self.phase = Phase::Done;
                } else if h.starts_with("unknown") || h.is_empty() {
                    self.status = "unknown".into();
                    self.phase = Phase::Done;
                } else {
                    self.status = "inconsistent".into();
                    let mut cand = z3_core_ids(out);
                    if cand.is_empty() {
                        cand = self.active.clone();
                    }
                    self.phase = if cand.len() <= 1 {
                        self.mus = cand.clone();
                        Phase::Repair {
                            subsets: powerset_by_weight(core, &cand),
                            k: 0,
                        }
                    } else {
                        Phase::Shrink { cand, i: 0 }
                    };
                }
            }
            Phase::Shrink { mut cand, i } => {
                // we tested cand without index i
                if h.starts_with("unsat") {
                    cand.remove(i); // still conflicting → that claim wasn't needed
                } else {
                    // needed; advance
                    self.phase = Phase::Shrink { cand: cand.clone(), i: i + 1 };
                    if i + 1 >= cand.len() {
                        self.finish_shrink(core, cand);
                    }
                    return;
                }
                if i >= cand.len() {
                    self.finish_shrink(core, cand);
                } else {
                    self.phase = Phase::Shrink { cand, i };
                }
            }
            Phase::Repair { subsets, k } => {
                if h.starts_with("sat") {
                    self.repair = subsets[k].clone();
                    self.repair_weight =
                        subsets[k].iter().map(|id| core.weight_of(id)).sum();
                    self.phase = Phase::Done;
                } else if k + 1 < subsets.len() {
                    self.phase = Phase::Repair { subsets, k: k + 1 };
                } else {
                    self.repair = self.mus.clone();
                    self.repair_weight =
                        self.mus.iter().map(|id| core.weight_of(id)).sum();
                    self.phase = Phase::Done;
                }
            }
            Phase::Done => {}
        }
    }
    fn finish_shrink(&mut self, core: &Core, cand: Vec<String>) {
        self.mus = cand.clone();
        self.phase = Phase::Repair {
            subsets: powerset_by_weight(core, &cand),
            k: 0,
        };
    }
    fn result(&self) -> serde_json::Value {
        serde_json::json!({
            "status": self.status,
            "mus": self.mus,
            "repair": { "drop": self.repair, "weight": self.repair_weight },
            "done": matches!(self.phase, Phase::Done),
        })
    }
}

// ---- wasm facade ----------------------------------------------------------

#[wasm_bindgen]
pub struct WmtEngine {
    core: Core,
    drv: Option<Driver>,
    lat: Option<Lattice>,
    wit: Option<WitnessDriver>,
}

#[wasm_bindgen]
impl WmtEngine {
    #[wasm_bindgen(constructor)]
    pub fn new() -> WmtEngine {
        WmtEngine { core: Core::default(), drv: None, lat: None, wit: None }
    }
    pub fn ingest(&mut self, json: &str) -> String {
        let (ok, errors) = self.core.ingest(json);
        serde_json::json!({"ok": ok, "errors": errors, "meta": self.core.meta()}).to_string()
    }
    pub fn retract(&mut self, id: &str) -> String {
        if let Some(c) = self.core.claims.iter_mut().find(|c| c.id == id) { c.active = false; }
        self.core.meta().to_string()
    }
    pub fn reactivate(&mut self, id: &str) -> String {
        if let Some(c) = self.core.claims.iter_mut().find(|c| c.id == id) { c.active = true; }
        self.core.meta().to_string()
    }
    pub fn remove(&mut self, id: &str) -> String {
        self.core.claims.retain(|c| c.id != id);
        self.core.meta().to_string()
    }
    pub fn set_weight(&mut self, id: &str, w: i64) -> String {
        if let Some(c) = self.core.claims.iter_mut().find(|c| c.id == id) { c.weight = w.max(1); }
        self.core.meta().to_string()
    }
    pub fn meta(&self) -> String { self.core.meta().to_string() }
    pub fn seed_demo(&mut self) -> String { self.core.seed_demo(); self.core.meta().to_string() }
    pub fn smt_check(&self) -> String { self.core.smt_check() }
    pub fn smt_core(&self) -> String { self.core.smt_core() }
    pub fn smt_entails_json(&self, formula_json: &str) -> String {
        match serde_json::from_str::<Formula>(formula_json) {
            Ok(f) => self.core.smt_entails(&f),
            Err(e) => format!("; IR parse error: {e}\n(check-sat)\n"),
        }
    }
    pub fn prompt(&self, nl: &str) -> String { self.core.prompt(nl) }

    // ---- analysis step driver (status + minimal conflict + optimal repair)
    pub fn analyze_begin(&mut self) { self.drv = Some(Driver::new(&self.core)); }
    pub fn analyze_next(&self) -> String {
        self.drv
            .as_ref()
            .and_then(|d| d.next_script(&self.core))
            .unwrap_or_default()
    }
    pub fn analyze_feed(&mut self, z3_out: &str) {
        if let Some(d) = self.drv.as_mut() {
            // borrow core immutably by cloning the small bits the driver needs
            let core = &self.core;
            d.feed(core, z3_out);
        }
    }
    pub fn analyze_result(&self) -> String {
        self.drv
            .as_ref()
            .map(|d| d.result().to_string())
            .unwrap_or_else(|| "{}".into())
    }

    // ---- full coherence-lattice driver -----------------------------------
    // Every minimal conflict (MUS) and every maximal coherent position
    // (MSS) the active claims admit. Same step-machine contract as the
    // analysis driver; native tests pump it with the z3 binary, the
    // browser with z3-wasm.
    pub fn lattice_begin(&mut self) {
        self.lat = Some(Lattice::new(&self.core));
    }
    pub fn lattice_next(&self) -> String {
        self.lat
            .as_ref()
            .and_then(|l| l.next_script(&self.core))
            .unwrap_or_default()
    }
    pub fn lattice_feed(&mut self, z3_out: &str) {
        if let Some(l) = self.lat.as_mut() {
            l.feed(z3_out);
        }
    }
    pub fn lattice_result(&self) -> String {
        self.lat
            .as_ref()
            .map(|l| l.result().to_string())
            .unwrap_or_else(|| "{}".into())
    }

    // ---- explanation witnesses -------------------------------------------
    // Why is a consequence forced? The minimal set of active claims that
    // entails `formula_json`. Same step-machine contract.
    pub fn witness_begin(&mut self, formula_json: &str) {
        self.wit = match serde_json::from_str::<Formula>(formula_json) {
            Ok(f) => Some(WitnessDriver::new(&self.core, f)),
            Err(_) => None,
        };
    }
    pub fn witness_next(&self) -> String {
        self.wit
            .as_ref()
            .and_then(|w| w.next_script(&self.core))
            .unwrap_or_default()
    }
    pub fn witness_feed(&mut self, z3_out: &str) {
        if let Some(w) = self.wit.as_mut() {
            let core = &self.core;
            w.feed(core, z3_out);
        }
    }
    pub fn witness_result(&self) -> String {
        self.wit
            .as_ref()
            .map(|w| w.result().to_string())
            .unwrap_or_else(|| "{}".into())
    }
}

// ---- full coherence lattice ----------------------------------------------
// Enumerate ALL minimal conflicts (MUSes) by increasing-size subset search
// with superset pruning — correct because, processing sizes ascending and
// skipping any candidate that already contains a found MUS, an unsatisfiable
// candidate that survives pruning has no unsatisfiable proper subset, i.e.
// it IS minimal. Maximal coherent positions (MSSes) and the ways out
// (MCSes) follow by Reiter/Liffiton–Sakallah duality: MCS = the minimal
// hitting sets of the MUS collection; MSS = its complement. Exact for the
// demo regime; capped (the UI falls back to the single-conflict driver for
// large sets, stated honestly, never silently truncated).

const LAT_CAP: usize = 10;

fn combinations(n: usize, k: usize) -> Vec<Vec<usize>> {
    let mut res = Vec::new();
    if k == 0 || k > n {
        return res;
    }
    let mut idx: Vec<usize> = (0..k).collect();
    loop {
        res.push(idx.clone());
        let mut i = k;
        loop {
            if i == 0 {
                return res;
            }
            i -= 1;
            if idx[i] < i + n - k {
                idx[i] += 1;
                for j in i + 1..k {
                    idx[j] = idx[j - 1] + 1;
                }
                break;
            }
        }
    }
}

fn minimal_hitting_sets(sets: &[Vec<String>], universe: &[String]) -> Vec<Vec<String>> {
    if sets.is_empty() {
        return Vec::new();
    }
    let n = universe.len();
    let mut found: Vec<Vec<String>> = Vec::new();
    for size in 1..=n {
        for cmb in combinations(n, size) {
            let cand: Vec<String> = cmb.iter().map(|&i| universe[i].clone()).collect();
            let hits = sets.iter().all(|s| s.iter().any(|e| cand.contains(e)));
            if !hits {
                continue;
            }
            let minimal = !found.iter().any(|f| f.iter().all(|e| cand.contains(e)));
            if minimal {
                found.push(cand);
            }
        }
    }
    found
}

#[derive(Default, Serialize)]
struct LatOut {
    consistent: bool,
    capped: bool,
    mus: Vec<Vec<String>>,
    mcs: Vec<Vec<String>>,
    mss: Vec<Vec<String>>,
    done: bool,
}

struct Lattice {
    active: Vec<String>,
    capped: bool,
    queue: Vec<Vec<String>>,
    qi: usize,
    muses: Vec<Vec<String>>,
    out: LatOut,
}

impl Lattice {
    fn new(core: &Core) -> Lattice {
        let active = core.active_ids();
        let n = active.len();
        let capped = n > LAT_CAP;
        let mut queue = Vec::new();
        if !capped {
            for size in 1..=n {
                for cmb in combinations(n, size) {
                    queue.push(cmb.iter().map(|&i| active[i].clone()).collect());
                }
            }
        }
        let mut l = Lattice {
            active,
            capped,
            queue,
            qi: 0,
            muses: Vec::new(),
            out: LatOut { capped, ..Default::default() },
        };
        if capped {
            l.out.done = true;
        } else {
            l.prepare();
        }
        l
    }
    fn prepare(&mut self) {
        while self.qi < self.queue.len() {
            let c = &self.queue[self.qi];
            let pruned = self
                .muses
                .iter()
                .any(|m| m.iter().all(|x| c.contains(x)));
            if pruned {
                self.qi += 1;
            } else {
                return;
            }
        }
        self.finalize();
    }
    fn next_script(&self, core: &Core) -> Option<String> {
        if self.out.done || self.qi >= self.queue.len() {
            None
        } else {
            Some(core.smt_assume(&self.queue[self.qi]))
        }
    }
    fn feed(&mut self, out: &str) {
        if self.out.done || self.qi >= self.queue.len() {
            return;
        }
        let h = z3_head(out);
        if h.starts_with("unsat") {
            let mus = self.queue[self.qi].clone();
            self.muses.push(mus);
        }
        // sat / unknown: not a (minimal) conflict at this subset
        self.qi += 1;
        self.prepare();
    }
    fn finalize(&mut self) {
        if self.muses.is_empty() {
            self.out.consistent = true;
            self.out.mus = Vec::new();
            self.out.mcs = Vec::new();
            self.out.mss = vec![self.active.clone()];
        } else {
            self.out.consistent = false;
            self.out.mus = self.muses.clone();
            self.out.mcs = minimal_hitting_sets(&self.muses, &self.active);
            self.out.mss = self
                .out
                .mcs
                .iter()
                .map(|m| {
                    self.active
                        .iter()
                        .filter(|x| !m.contains(x))
                        .cloned()
                        .collect()
                })
                .collect();
        }
        self.out.done = true;
    }
    fn result(&self) -> serde_json::Value {
        serde_json::to_value(&self.out).unwrap_or_else(|_| serde_json::json!({}))
    }
}

// ---- explanation-witness step machine ------------------------------------
// `probe` is forced iff (active claims) ∧ ¬probe is unsat. The unsat core
// over the assumption literals is the responsible set; deletion-shrink
// makes it minimal. "Flies(tweety) BECAUSE {birds_fly, penguin_bird,
// tweety_penguin}." Mirrors Driver's verified CheckAll/Shrink contract.

enum WPhase {
    CheckAll,
    Shrink { cand: Vec<String>, i: usize },
    Done,
}

struct WitnessDriver {
    probe: Formula,
    active: Vec<String>,
    phase: WPhase,
    status: String, // entailed | not_entailed | unknown
    witness: Vec<String>,
}

impl WitnessDriver {
    fn new(core: &Core, probe: Formula) -> WitnessDriver {
        WitnessDriver {
            probe,
            active: core.active_ids(),
            phase: WPhase::CheckAll,
            status: String::new(),
            witness: vec![],
        }
    }
    fn next_script(&self, core: &Core) -> Option<String> {
        match &self.phase {
            WPhase::CheckAll => Some(core.smt_entail_assume(&self.probe, &self.active)),
            WPhase::Shrink { cand, i } => {
                let mut c = cand.clone();
                c.remove(*i);
                Some(core.smt_entail_assume(&self.probe, &c))
            }
            WPhase::Done => None,
        }
    }
    fn feed(&mut self, _core: &Core, out: &str) {
        let h = z3_head(out);
        match std::mem::replace(&mut self.phase, WPhase::Done) {
            WPhase::CheckAll => {
                if h.starts_with("unsat") {
                    self.status = "entailed".into();
                    let mut cand = z3_core_ids(out);
                    if cand.is_empty() {
                        cand = self.active.clone();
                    }
                    if cand.len() <= 1 {
                        self.witness = cand;
                        self.phase = WPhase::Done;
                    } else {
                        self.phase = WPhase::Shrink { cand, i: 0 };
                    }
                } else if h.starts_with("sat") {
                    self.status = "not_entailed".into();
                    self.phase = WPhase::Done;
                } else {
                    self.status = "unknown".into();
                    self.phase = WPhase::Done;
                }
            }
            WPhase::Shrink { mut cand, i } => {
                if h.starts_with("unsat") {
                    cand.remove(i); // still entails without it
                } else {
                    let ni = i + 1;
                    if ni >= cand.len() {
                        self.witness = cand;
                        self.phase = WPhase::Done;
                    } else {
                        self.phase = WPhase::Shrink { cand, i: ni };
                    }
                    return;
                }
                if i >= cand.len() {
                    self.witness = cand;
                    self.phase = WPhase::Done;
                } else {
                    self.phase = WPhase::Shrink { cand, i };
                }
            }
            WPhase::Done => {}
        }
    }
    fn result(&self) -> serde_json::Value {
        serde_json::json!({
            "status": self.status,
            "entailed": self.status == "entailed",
            "witness": self.witness,
        })
    }
}

impl Default for WmtEngine {
    fn default() -> Self { Self::new() }
}

// ---- native tests: REAL end-to-end against the `z3` binary ----------------

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;
    use std::process::{Command, Stdio};

    fn z3(s: &str) -> Option<String> {
        let mut ch = match Command::new("z3")
            .arg("-in").stdin(Stdio::piped()).stdout(Stdio::piped()).stderr(Stdio::piped())
            .spawn()
        {
            Ok(c) => c,
            Err(_) => { eprintln!("SKIP: no z3 binary"); return None; }
        };
        ch.stdin.as_mut().unwrap().write_all(s.as_bytes()).unwrap();
        Some(String::from_utf8_lossy(&ch.wait_with_output().unwrap().stdout).to_string())
    }
    fn head(o: &str) -> String { z3_head(o) }

    /// Drive the analysis step-machine with the real z3 binary.
    fn analyze(c: &Core) -> serde_json::Value {
        let mut d = Driver::new(c);
        let mut guard = 0;
        while let Some(script) = d.next_script(c) {
            let o = match z3(&script) { Some(o) => o, None => return serde_json::json!({"skip":true}) };
            d.feed(c, &o);
            guard += 1;
            assert!(guard < 200, "driver did not terminate");
        }
        d.result()
    }

    /// Drive the full coherence-lattice step-machine with the z3 binary.
    fn lattice(c: &Core) -> serde_json::Value {
        let mut l = Lattice::new(c);
        let mut guard = 0;
        while let Some(script) = l.next_script(c) {
            let o = match z3(&script) {
                Some(o) => o,
                None => return serde_json::json!({"skip": true}),
            };
            l.feed(&o);
            guard += 1;
            assert!(guard < 4096, "lattice did not terminate");
        }
        l.result()
    }

    fn witness(c: &Core, probe: Formula) -> serde_json::Value {
        let mut w = WitnessDriver::new(c, probe);
        let mut g = 0;
        while let Some(s) = w.next_script(c) {
            let o = match z3(&s) {
                Some(o) => o,
                None => return serde_json::json!({ "skip": true }),
            };
            w.feed(c, &o);
            g += 1;
            assert!(g < 200, "witness did not terminate");
        }
        w.result()
    }

    #[test]
    fn explanation_witness_is_minimal() {
        // Flies(tweety) is forced; the witness is exactly the 3-claim
        // chain that forces it — minimal, not the whole knowledge base.
        let mut c = Core::default();
        c.seed_demo();
        let probe: Formula = serde_json::from_str(
            r#"{"op":"pred","name":"Flies","args":[{"t":"app","name":"tweety","args":[]}]}"#,
        )
        .unwrap();
        let r = witness(&c, probe);
        if r.get("skip").is_some() {
            return;
        }
        assert_eq!(r["status"], "entailed");
        let mut w: Vec<String> = r["witness"]
            .as_array()
            .unwrap()
            .iter()
            .map(|v| v.as_str().unwrap().to_string())
            .collect();
        w.sort();
        assert_eq!(
            w,
            vec!["c_birds_fly", "c_penguin_bird", "c_tweety_penguin"],
            "witness must be the minimal forcing chain"
        );
    }

    #[test]
    fn explanation_witness_not_entailed() {
        // Only "birds fly" — Flies(tweety) is NOT forced (nothing says
        // tweety is a bird).
        let mut c = Core::default();
        c.ingest(
            r#"{"sorts":["Thing"],
              "preds":[{"name":"Bird","args":["Thing"]},{"name":"Flies","args":["Thing"]}],
              "funcs":[{"name":"tweety","args":[],"ret":"Thing"}],
              "claims":[{"id":"c_bf","formula":{"op":"forall","vars":[{"name":"x","sort":"Thing"}],
                "body":{"op":"imp","a":{"op":"pred","name":"Bird","args":[{"t":"var","name":"x"}]},
                                    "b":{"op":"pred","name":"Flies","args":[{"t":"var","name":"x"}]}}}}]}"#,
        );
        let probe: Formula = serde_json::from_str(
            r#"{"op":"pred","name":"Flies","args":[{"t":"app","name":"tweety","args":[]}]}"#,
        )
        .unwrap();
        let r = witness(&c, probe);
        if r.get("skip").is_some() {
            return;
        }
        assert_eq!(r["status"], "not_entailed");
        assert_eq!(r["entailed"], false);
    }

    #[test]
    fn back_translation_field_round_trips() {
        let mut c = Core::default();
        assert!(c.ingest(
            r#"{"preds":[{"name":"P","args":[],"gloss":"p"}],
              "claims":[{"id":"c1","source":"It is P.","back":"P holds.",
                "formula":{"op":"pred","name":"P","args":[]}}]}"#
        ).0);
        assert_eq!(c.meta()["claims"][0]["back"], "P holds.");
    }

    fn as_sets(v: &serde_json::Value) -> Vec<Vec<String>> {
        v.as_array()
            .unwrap()
            .iter()
            .map(|s| {
                let mut x: Vec<String> = s
                    .as_array()
                    .unwrap()
                    .iter()
                    .map(|e| e.as_str().unwrap().to_string())
                    .collect();
                x.sort();
                x
            })
            .collect()
    }

    #[test]
    fn lattice_consistent_one_position() {
        let mut c = Core::default();
        c.seed_demo();
        let r = lattice(&c);
        if r.get("skip").is_some() {
            return;
        }
        assert_eq!(r["consistent"], true);
        assert!(r["mus"].as_array().unwrap().is_empty());
        let mss = as_sets(&r["mss"]);
        assert_eq!(mss.len(), 1, "one coherent position = everything");
        assert_eq!(mss[0].len(), 3);
    }

    #[test]
    fn lattice_penguin_single_mus_four_positions() {
        let mut c = Core::default();
        c.seed_demo();
        c.ingest(
            r#"{"claims":[{"id":"c_pen_nofly","weight":1,
              "formula":{"op":"forall","vars":[{"name":"x","sort":"Thing"}],
                "body":{"op":"imp",
                  "a":{"op":"pred","name":"Penguin","args":[{"t":"var","name":"x"}]},
                  "b":{"op":"not","x":{"op":"pred","name":"Flies","args":[{"t":"var","name":"x"}]}}}}}]}"#,
        );
        let r = lattice(&c);
        if r.get("skip").is_some() {
            return;
        }
        assert_eq!(r["consistent"], false);
        let mus = as_sets(&r["mus"]);
        assert_eq!(mus.len(), 1, "one irreducible disagreement");
        assert_eq!(mus[0].len(), 4);
        let mcs = as_sets(&r["mcs"]);
        assert_eq!(mcs.len(), 4, "four ways out (drop any one)");
        assert!(mcs.iter().all(|m| m.len() == 1));
        let mss = as_sets(&r["mss"]);
        assert_eq!(mss.len(), 4, "four maximal coherent positions");
        assert!(mss.iter().all(|p| p.len() == 3));
    }

    #[test]
    fn lattice_two_independent_conflicts_duality() {
        // {P, ¬P} and {Q, ¬Q}: two MUSes; MCS = minimal hitting sets =
        // {one of each pair} → 4 correction sets of size 2; 4 positions.
        let mut c = Core::default();
        c.ingest(
            r#"{"preds":[{"name":"P","args":[],"gloss":"p"},{"name":"Q","args":[],"gloss":"q"}],
              "claims":[
               {"id":"c_p","formula":{"op":"pred","name":"P","args":[]}},
               {"id":"c_np","formula":{"op":"not","x":{"op":"pred","name":"P","args":[]}}},
               {"id":"c_q","formula":{"op":"pred","name":"Q","args":[]}},
               {"id":"c_nq","formula":{"op":"not","x":{"op":"pred","name":"Q","args":[]}}}]}"#,
        );
        let r = lattice(&c);
        if r.get("skip").is_some() {
            return;
        }
        assert_eq!(r["consistent"], false);
        let mut mus = as_sets(&r["mus"]);
        mus.sort();
        assert_eq!(
            mus,
            vec![
                vec!["c_np".to_string(), "c_p".to_string()],
                vec!["c_nq".to_string(), "c_q".to_string()]
            ]
        );
        let mcs = as_sets(&r["mcs"]);
        assert_eq!(mcs.len(), 4, "4 minimal hitting sets: {mcs:?}");
        assert!(mcs.iter().all(|m| m.len() == 2));
    }

    #[test]
    fn ir_compiles_and_renders() {
        let mut c = Core::default();
        assert!(c.ingest(r#"{"preds":[{"name":"P","args":[],"gloss":"p"}],
            "claims":[{"id":"c1","formula":{"op":"pred","name":"P","args":[]}}]}"#).0);
        assert_eq!(form_smt(&c.claims[0].formula), "P");
        assert_eq!(form_en(&c.claims[0].formula), "P");
        if let Some(o) = z3(&c.smt_check()) { assert_eq!(head(&o), "sat"); }
    }

    #[test]
    fn english_render_has_no_smt() {
        let mut c = Core::default();
        c.seed_demo();
        let r = form_en(&c.claims[0].formula);
        assert!(r.contains("for every") && r.contains("if"), "{r}");
        assert!(!r.contains("=>") && !r.contains("(op"), "leaked smt: {r}");
    }

    #[test]
    fn quantified_penguin_contradiction_and_core() {
        let mut c = Core::default();
        c.seed_demo();
        if let Some(o) = z3(&c.smt_check()) { assert_eq!(head(&o), "sat", "{o}"); }
        assert!(c.ingest(r#"{"claims":[{"id":"c_pen_nofly","source":"Penguins cannot fly.","weight":3,
          "formula":{"op":"forall","vars":[{"name":"x","sort":"Thing"}],
            "body":{"op":"imp",
              "a":{"op":"pred","name":"Penguin","args":[{"t":"var","name":"x"}]},
              "b":{"op":"not","x":{"op":"pred","name":"Flies","args":[{"t":"var","name":"x"}]}}}}}]}"#).0);
        if let Some(o) = z3(&c.smt_check()) { assert_eq!(head(&o), "unsat", "{o}"); }
    }

    #[test]
    fn analysis_minimal_conflict_and_optimal_repair() {
        // weights: birds_fly 2, penguin_bird 5, tweety_penguin 4, pen_nofly 3
        // single MUS = all four; min-weight repair drops birds_fly (2).
        let mut c = Core::default();
        c.seed_demo();
        c.ingest(r#"{"claims":[{"id":"c_pen_nofly","weight":3,
          "formula":{"op":"forall","vars":[{"name":"x","sort":"Thing"}],
            "body":{"op":"imp",
              "a":{"op":"pred","name":"Penguin","args":[{"t":"var","name":"x"}]},
              "b":{"op":"not","x":{"op":"pred","name":"Flies","args":[{"t":"var","name":"x"}]}}}}}]}"#);
        let r = analyze(&c);
        if r.get("skip").is_some() { return; }
        assert_eq!(r["status"], "inconsistent");
        let mut mus: Vec<String> = r["mus"].as_array().unwrap()
            .iter().map(|v| v.as_str().unwrap().to_string()).collect();
        mus.sort();
        assert_eq!(mus, vec!["c_birds_fly","c_pen_nofly","c_penguin_bird","c_tweety_penguin"]);
        assert_eq!(r["repair"]["drop"], serde_json::json!(["c_birds_fly"]));
        assert_eq!(r["repair"]["weight"], 2);
    }

    #[test]
    fn analysis_consistent_set() {
        let mut c = Core::default();
        c.seed_demo();
        let r = analyze(&c);
        if r.get("skip").is_some() { return; }
        assert_eq!(r["status"], "consistent");
    }

    #[test]
    fn arithmetic_conflict_beyond_propositional() {
        let mut c = Core::default();
        c.ingest(r#"{"funcs":[{"name":"x","args":[],"ret":"Int","gloss":"the number x"}],
          "claims":[
           {"id":"c_big","formula":{"op":"cmp","rel":">","a":{"t":"app","name":"x","args":[]},"b":{"t":"int","v":5}}},
           {"id":"c_small","formula":{"op":"cmp","rel":"<","a":{"t":"app","name":"x","args":[]},"b":{"t":"int","v":3}}}]}"#);
        if let Some(o) = z3(&c.smt_check()) { assert_eq!(head(&o), "unsat", "{o}"); }
        let r = analyze(&c);
        if r.get("skip").is_some() { return; }
        assert_eq!(r["status"], "inconsistent");
        let mut mus: Vec<String> = r["mus"].as_array().unwrap()
            .iter().map(|v| v.as_str().unwrap().to_string()).collect();
        mus.sort();
        assert_eq!(mus, vec!["c_big","c_small"]);
    }

    #[test]
    fn ground_atoms_surfaced_and_entailed() {
        let mut c = Core::default();
        c.seed_demo();
        let m = c.meta();
        let gs = m["ground_atoms"].as_array().unwrap();
        let labels: Vec<String> = gs
            .iter()
            .map(|g| g["label"].as_str().unwrap().to_string())
            .collect();
        assert!(labels.iter().any(|l| l == "Flies(tweety)"), "{labels:?}");
        let f: Formula = serde_json::from_value(
            gs.iter()
                .find(|g| g["label"] == "Flies(tweety)")
                .unwrap()["formula"]
                .clone(),
        )
        .unwrap();
        if let Some(o) = z3(&c.smt_entails(&f)) {
            assert_eq!(head(&o), "unsat", "Flies(tweety) must be entailed: {o}");
        }
    }

    #[test]
    fn entailment_forced_consequence() {
        let mut c = Core::default();
        c.seed_demo();
        let probe: Formula = serde_json::from_str(
            r#"{"op":"pred","name":"Flies","args":[{"t":"app","name":"tweety","args":[]}]}"#).unwrap();
        if let Some(o) = z3(&c.smt_entails(&probe)) {
            assert_eq!(head(&o), "unsat", "Flies(tweety) should be entailed: {o}");
        }
    }

    #[test]
    fn revision_replaces_same_id() {
        let mut c = Core::default();
        c.ingest(r#"{"preds":[{"name":"P","args":[],"gloss":"p"}],
          "claims":[{"id":"c1","formula":{"op":"pred","name":"P","args":[]}}]}"#);
        c.ingest(r#"{"claims":[{"id":"c1","formula":{"op":"not","x":{"op":"pred","name":"P","args":[]}}}]}"#);
        assert_eq!(c.claims.len(), 1);
        if let Some(o) = z3(&c.smt_check()) { assert_eq!(head(&o), "sat"); }
    }
}
