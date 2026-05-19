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
    /// A *default*, not a strict axiom: it may be overridden by a
    /// higher-priority or logically more-specific claim instead of
    /// counting as a contradiction. Default false = strict (so all
    /// pre-existing behaviour and tests are unchanged).
    #[serde(default)]
    pub defeasible: bool,
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

#[derive(Default, Serialize, Deserialize)]
struct Core {
    #[serde(default)]
    sorts: Vec<String>, // user sorts (non-builtin)
    #[serde(default)]
    preds: BTreeMap<String, Sig>,
    #[serde(default)]
    funcs: BTreeMap<String, Sig>,
    #[serde(default)]
    decl_order: Vec<(char, String)>, // ('p'|'f', name) for stable emission
    #[serde(default)]
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
        self.autodeclare();
        (true, Vec::new())
    }

    /// Best-effort: declare any predicate / function / constant symbol a
    /// claim *uses* but did not *declare*. Elicited or hand-written IR
    /// often omits the `preds`/`funcs` blocks; without this the compiled
    /// SMT references undeclared symbols and Z3 errors out (which we then
    /// honestly report as undecided — never as a verdict). Inference is
    /// deliberately shallow (one default sort, arity from use); Z3's own
    /// type-checker still catches genuine misuse (same name, two arities).
    fn autodeclare(&mut self) {
        fn walk_term(t: &Term, f: &mut BTreeMap<String, usize>) {
            match t {
                Term::App { name, args } => {
                    f.entry(name.clone()).or_insert(args.len());
                    for a in args { walk_term(a, f); }
                }
                Term::Arith { args, .. } => for a in args { walk_term(a, f); },
                _ => {}
            }
        }
        fn walk(form: &Formula, p: &mut BTreeMap<String, usize>, f: &mut BTreeMap<String, usize>) {
            match form {
                Formula::Pred { name, args } => {
                    p.entry(name.clone()).or_insert(args.len());
                    for a in args { walk_term(a, f); }
                }
                Formula::Eq { a, b } => { walk_term(a, f); walk_term(b, f); }
                Formula::Cmp { a, b, .. } => { walk_term(a, f); walk_term(b, f); }
                Formula::Not { x } => walk(x, p, f),
                Formula::And { xs } | Formula::Or { xs } => for y in xs { walk(y, p, f); },
                Formula::Imp { a, b } | Formula::Iff { a, b } => { walk(a, p, f); walk(b, p, f); }
                Formula::Forall { body, .. } | Formula::Exists { body, .. } => walk(body, p, f),
            }
        }
        let mut preds: BTreeMap<String, usize> = BTreeMap::new();
        let mut funcs: BTreeMap<String, usize> = BTreeMap::new();
        for c in &self.claims {
            walk(&c.formula, &mut preds, &mut funcs);
        }
        let dflt = self
            .sorts
            .first()
            .cloned()
            .unwrap_or_else(|| "U".to_string());
        let need_default = preds.iter().any(|(n, _)| !self.preds.contains_key(n))
            || funcs.iter().any(|(n, _)| !self.funcs.contains_key(n));
        if need_default && !self.sorts.contains(&dflt) {
            self.sorts.push(dflt.clone());
        }
        for (name, ar) in preds {
            if !self.preds.contains_key(&name) {
                self.decl_order.push(('p', name.clone()));
                self.preds.insert(
                    name.clone(),
                    Sig { name, args: vec![dflt.clone(); ar], ret: None, gloss: "(inferred from use)".into() },
                );
            }
        }
        for (name, ar) in funcs {
            if !self.funcs.contains_key(&name) {
                self.decl_order.push(('f', name.clone()));
                self.funcs.insert(
                    name.clone(),
                    Sig {
                        name,
                        args: vec![dflt.clone(); ar],
                        ret: Some(dflt.clone()),
                        gloss: "(inferred from use)".into(),
                    },
                );
            }
        }
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

    /// Belief-elicitation prompt: ask the model to state its OWN beliefs
    /// about a domain as the IR, so the instrument can check *them* for
    /// internal consistency. The honest framing is load-bearing and is
    /// in the prompt itself: we test the mutual consistency of *these
    /// elicited statements*, never the model's "true" beliefs and never
    /// their truth. Deterministic, so it is unit-tested offline; the
    /// live call is the external seam (an ignored, key-gated test).
    fn belief_elicitation_prompt(&self, domain: &str, n: usize) -> String {
        format!(
"You are stating beliefs you hold, to be checked for INTERNAL CONSISTENCY\n\
by a theorem prover. This is not a test of truth and not a trick: list\n\
{n} separate, confident, atomic beliefs you hold about the domain below,\n\
each formalized in a typed many-sorted first-order IR. Return ONLY this\n\
JSON object:\n\
\n\
{{\"sorts\":[\"Thing\"],\n\
  \"preds\":[{{\"name\":\"Bird\",\"args\":[\"Thing\"],\"gloss\":\"x is a bird\"}}],\n\
  \"funcs\":[{{\"name\":\"age\",\"args\":[\"Thing\"],\"ret\":\"Int\",\"gloss\":\"age of x\"}}],\n\
  \"claims\":[{{\"id\":\"c_slug\",\"source\":\"<the belief, your own words>\",\n\
    \"gloss\":\"<=6 words\",\"back\":\"<one sentence: exactly what the\n\
            formula says>\",\"formula\":{{...}}}}]}}\n\
\n\
FORMULA grammar (JSON, field \"op\"): pred{{name,args}} eq{{a,b}}\n\
  cmp{{rel:'<'|'<='|'>'|'>=',a,b}} not{{x}} and{{xs}} or{{xs}} imp{{a,b}}\n\
  iff{{a,b}} forall{{vars:[{{name,sort}}],body}} exists{{vars,body}}\n\
TERM grammar (field \"t\"): var{{name}} int{{v}} real{{v}}\n\
  app{{name,args}} (0-arg app = a constant) arith{{op:'+'|'-'|'*',args}}\n\
\n\
Rules, most important first:\n\
1. REUSE one symbol per concept. If two beliefs are about the same\n\
   predicate/constant they MUST use the same name — minting a synonym is\n\
   exactly how a real inner contradiction hides. Reuse the vocabulary\n\
   below when it fits; add new symbols (with a gloss) only when needed.\n\
2. State beliefs you would actually defend, including ones that feel\n\
   OBVIOUS — latent contradictions live among the obvious ones (general\n\
   rules vs. specific cases, transitive relations, category membership).\n\
3. Prefer typed quantified formulas for general rules:\n\
   \"penguins don't fly\" => forall x:Thing.(=> (Penguin x) (not (Flies x))).\n\
4. Do not self-censor for consistency — state them independently. The\n\
   prover, not you, decides whether they cohere. We test ONLY whether\n\
   THESE STATEMENTS are mutually consistent: not their truth, not your\n\
   \"real\" beliefs. Be candid; that is the point.\n\
5. No SMT-LIB, no prose, no code fences. JSON only.\n\
\n\
DOMAIN:\n{domain}\n\
\n\
VOCABULARY ALREADY IN PLAY (reuse it):\n{}\n",
            self.registry_view()
        )
    }

    /// Triage prompt for a minimal conflict: ask the model whether the
    /// contradiction is INTRINSIC to the sentences or an artifact the
    /// FORMALIZATION introduced, and if the latter, a corrected IR
    /// (same ids) to replace it. The model only *proposes* — the engine
    /// re-checks the fix with Z3 (the abductive loop is closed by the
    /// solver, the model is never trusted). Built in the trusted core so
    /// it is deterministic and testable.
    fn triage_prompt(&self, ids: &[String]) -> String {
        let mut block = String::new();
        for id in ids {
            if let Some(c) = self.claims.iter().find(|c| &c.id == id) {
                block.push_str(&format!(
                    "- id {}\n  sentence: {}\n  reads as: {}\n  IR: {}\n",
                    c.id,
                    if c.source.is_empty() { &c.gloss } else { &c.source },
                    form_en(&c.formula),
                    serde_json::to_string(&c.formula).unwrap_or_default(),
                ));
            }
        }
        format!(
"These claims were found *mutually contradictory* by a theorem prover:\n\
\n{block}\n\
Decide ONE thing: is the contradiction INTRINSIC (the sentences\n\
themselves genuinely disagree — a real belief conflict the user must\n\
resolve) or FORMALIZATION (the sentences are compatible; a mistranslation\n\
into logic introduced the clash — e.g. a default read as a hard rule, a\n\
reused symbol that should differ, a wrong quantifier)?\n\
\n\
Return ONLY this JSON:\n\
{{\"verdict\":\"intrinsic\"|\"formalization\",\n\
  \"reason\":\"<one sentence, plain English>\",\n\
  \"fix\":<null, OR an IR object {{\\\"sorts\\\":[],\\\"preds\\\":[],\\\"funcs\\\":[],\\\"claims\\\":[...]}}\n\
        that REPLACES the mis-formalized claims — reuse the SAME ids,\n\
        keep \\\"source\\\" verbatim, change only the formula/flags so the\n\
        sentences no longer falsely clash; null if verdict is intrinsic>}}\n\
\n\
Vocabulary in play:\n{}\n\
No prose, no code fences. JSON only.\n",
            self.registry_view()
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

    /// A worked, non-toy world-model: a small project-status belief set
    /// with THREE overlapping irreducible disagreements (two claims carry
    /// blame across more than one), plus two independent facts that hold
    /// in every coherent position. It exists to show, at a glance, that
    /// this is a lattice instrument — multiple conflicts, many positions,
    /// a real argumentation graph — not a 3-claim toy. Deterministic and
    /// solver-verified by a native test.
    fn seed_scenario(&mut self) {
        let s = r#"{
          "preds":[
            {"name":"Ships","args":[],"gloss":"the project ships this week"},
            {"name":"TestsPass","args":[],"gloss":"the test suite passes"},
            {"name":"Reviewed","args":[],"gloss":"the code was reviewed"},
            {"name":"QualityHigh","args":[],"gloss":"quality is high"},
            {"name":"BudgetOK","args":[],"gloss":"the budget is fine"},
            {"name":"TeamHappy","args":[],"gloss":"the team is happy"}],
          "claims":[
           {"id":"c_ships","source":"The project ships this week.","gloss":"it ships","weight":3,
            "formula":{"op":"pred","name":"Ships","args":[]}},
           {"id":"c_ship_needs_tests","source":"If it ships, the tests pass.","gloss":"ship ⇒ tests","weight":4,
            "formula":{"op":"imp","a":{"op":"pred","name":"Ships","args":[]},"b":{"op":"pred","name":"TestsPass","args":[]}}},
           {"id":"c_tests_fail","source":"The tests do not pass.","gloss":"tests fail","weight":2,
            "formula":{"op":"not","x":{"op":"pred","name":"TestsPass","args":[]}}},
           {"id":"c_ship_needs_review","source":"If it ships, the code was reviewed.","gloss":"ship ⇒ review","weight":4,
            "formula":{"op":"imp","a":{"op":"pred","name":"Ships","args":[]},"b":{"op":"pred","name":"Reviewed","args":[]}}},
           {"id":"c_not_reviewed","source":"The code was not reviewed.","gloss":"not reviewed","weight":2,
            "formula":{"op":"not","x":{"op":"pred","name":"Reviewed","args":[]}}},
           {"id":"c_quality","source":"Quality is high.","gloss":"high quality","weight":3,
            "formula":{"op":"pred","name":"QualityHigh","args":[]}},
           {"id":"c_quality_needs_review","source":"High quality requires code review.","gloss":"quality ⇒ review","weight":5,
            "formula":{"op":"imp","a":{"op":"pred","name":"QualityHigh","args":[]},"b":{"op":"pred","name":"Reviewed","args":[]}}},
           {"id":"c_budget","source":"The budget is fine.","gloss":"budget ok","weight":3,
            "formula":{"op":"pred","name":"BudgetOK","args":[]}},
           {"id":"c_team","source":"The team is happy.","gloss":"team happy","weight":3,
            "formula":{"op":"pred","name":"TeamHappy","args":[]}}]}"#;
        let _ = self.ingest(s);
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
                "defeasible": c.defeasible,
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

    /// The entire world-model — vocabulary + trajectory — as portable
    /// JSON. This is what makes a *forkable trajectory tree* possible:
    /// a branch is just a saved `Core`. Round-trips exactly (see the
    /// `state_round_trips` native test).
    fn export_state(&self) -> String {
        serde_json::to_string(self).unwrap_or_else(|_| "{}".into())
    }
    fn import_state(&mut self, json: &str) -> bool {
        match serde_json::from_str::<Core>(json) {
            Ok(c) => {
                *self = c;
                true
            }
            Err(_) => false,
        }
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
    dfz: Option<DefeasibleDriver>,
}

#[wasm_bindgen]
impl WmtEngine {
    #[wasm_bindgen(constructor)]
    pub fn new() -> WmtEngine {
        WmtEngine { core: Core::default(), drv: None, lat: None, wit: None, dfz: None }
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
    pub fn seed_scenario(&mut self) -> String { self.core.seed_scenario(); self.core.meta().to_string() }
    /// Start from nothing — loading a demo should give you that demo, not
    /// append it to whatever was there.
    pub fn reset(&mut self) -> String {
        self.core = Core::default();
        self.drv = None;
        self.lat = None;
        self.wit = None;
        self.dfz = None;
        self.core.meta().to_string()
    }
    pub fn smt_check(&self) -> String { self.core.smt_check() }
    pub fn smt_core(&self) -> String { self.core.smt_core() }
    pub fn smt_entails_json(&self, formula_json: &str) -> String {
        match serde_json::from_str::<Formula>(formula_json) {
            Ok(f) => self.core.smt_entails(&f),
            Err(e) => format!("; IR parse error: {e}\n(check-sat)\n"),
        }
    }
    pub fn prompt(&self, nl: &str) -> String { self.core.prompt(nl) }
    pub fn belief_elicitation_prompt(&self, domain: &str, n: u32) -> String {
        self.core.belief_elicitation_prompt(domain, n as usize)
    }
    pub fn triage_prompt_json(&self, ids_json: &str) -> String {
        match serde_json::from_str::<Vec<String>>(ids_json) {
            Ok(ids) => self.core.triage_prompt(&ids),
            Err(e) => format!("; bad id list: {e}"),
        }
    }

    // ---- forkable trajectory tree (C) ------------------------------------
    // Export the whole world-model so the UI can keep a tree of branches
    // (fork = snapshot here; switch = import a snapshot; compare = analyze
    // two snapshots). The engine owns the (de)serialization so a branch is
    // guaranteed to round-trip; the tree itself lives in the UI.
    pub fn export_state(&self) -> String { self.core.export_state() }
    pub fn import_state(&mut self, json: &str) -> String {
        let ok = self.core.import_state(json);
        self.drv = None;
        self.lat = None;
        self.wit = None;
        self.dfz = None;
        serde_json::json!({"ok": ok, "meta": self.core.meta()}).to_string()
    }
    pub fn set_defeasible(&mut self, id: &str, d: bool) -> String {
        if let Some(c) = self.core.claims.iter_mut().find(|c| c.id == id) { c.defeasible = d; }
        self.core.meta().to_string()
    }

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

    // ---- defeasible / prioritized reasoning (E) --------------------------
    pub fn defeasible_begin(&mut self) { self.dfz = Some(DefeasibleDriver::new(&self.core)); }
    pub fn defeasible_next(&self) -> String {
        self.dfz.as_ref().and_then(|d| d.next_script(&self.core)).unwrap_or_default()
    }
    pub fn defeasible_feed(&mut self, z3_out: &str) {
        if let Some(d) = self.dfz.as_mut() {
            let core = &self.core;
            d.feed(core, z3_out);
        }
    }
    pub fn defeasible_result(&self) -> String {
        self.dfz.as_ref().map(|d| d.result().to_string()).unwrap_or_else(|| "{}".into())
    }
}

// ---- full coherence lattice (MARCO) --------------------------------------
// Enumerate every minimal conflict (MUS) and every maximal coherent
// position (MSS, complement = MCS) with the MARCO algorithm
// (Liffiton–Previti–Malik–Marques-Silva): a propositional *map* over one
// selector bit per active claim records the regions of the power set
// already explained. Each round: get a model of the map (a seed); ask Z3
// whether that subset of claims is consistent; if SAT, *grow* it to an
// MSS and block its down-set; if UNSAT, *shrink* it to an MUS and block
// its up-set. The map strictly shrinks each round, so this terminates
// having enumerated every MUS and MCS exactly — no subset-size blowup,
// no n≤10 cap. Cost is dominated by (#MUS + #MCS), each a handful of Z3
// calls; an honest budget stops pathological cases and is reported as
// "not exhaustive" rather than silently truncated. The argumentation
// view is still derived (not re-solved) from the result.

const LAT_BUDGET: usize = 240; // max (#MUS + #MCS) before "not exhaustive"

#[allow(dead_code)] // kept as an independent Reiter-duality test oracle
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

#[allow(dead_code)] // independent oracle: MCS == minimal hitting sets of MUS
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
    /// Z3 errored or returned `unknown` on the whole set — there is NO
    /// consistency verdict (never read `consistent` when this is true).
    unknown: bool,
    capped: bool,
    mus: Vec<Vec<String>>,
    mcs: Vec<Vec<String>>,
    mss: Vec<Vec<String>>,
    /// Dung argumentation view, derived (not re-solved) from the lattice.
    af: Af,
    done: bool,
}

/// An abstract argumentation framework read off the coherence lattice.
///
/// Arguments = the active claims. Attack = two claims co-occur in some
/// minimal conflict (an irreducible disagreement). Under exactly this
/// attack relation a set is conflict-free iff it contains no whole MUS
/// iff it is *consistent*; the preferred / stable extensions therefore
/// coincide with the maximal coherent positions (MSSes) the lattice
/// already enumerates. So the acceptance statuses below are a faithful
/// Dung reading of data we already have — not a second, unchecked solve:
///
///   * skeptical — in *every* extension (= "necessary"): cannot be given
///     up by any rational resolution of the disagreement;
///   * credulous-only — in *some* but not every extension (= "contested"):
///     defensible, but a coherent position can also reject it;
///   * defeated — in *no* extension: every maximal coherent position
///     drops it.
#[derive(Default, Serialize)]
struct Af {
    /// Unordered attack edges {a,b}, a<b, deduplicated.
    attacks: Vec<Vec<String>>,
    skeptical: Vec<String>,
    credulous: Vec<String>,
    defeated: Vec<String>,
}

/// Pure, separately tested: derive the AF from the MUS collection and the
/// extensions (MSSes) over the active arguments.
fn argumentation(muses: &[Vec<String>], mss: &[Vec<String>], active: &[String]) -> Af {
    use std::collections::BTreeSet;
    let mut edges: BTreeSet<(String, String)> = BTreeSet::new();
    for m in muses {
        for (i, a) in m.iter().enumerate() {
            for b in &m[i + 1..] {
                let (x, y) = if a <= b { (a, b) } else { (b, a) };
                edges.insert((x.clone(), y.clone()));
            }
        }
    }
    let attacks = edges.into_iter().map(|(a, b)| vec![a, b]).collect();
    let in_some = |id: &String| mss.iter().any(|e| e.contains(id));
    let in_all = |id: &String| !mss.is_empty() && mss.iter().all(|e| e.contains(id));
    let skeptical = active.iter().filter(|id| in_all(id)).cloned().collect();
    let credulous = active.iter().filter(|id| in_some(id)).cloned().collect();
    let defeated = active.iter().filter(|id| !in_some(id)).cloned().collect();
    Af { attacks, skeptical, credulous, defeated }
}

fn parse_bool_model(out: &str, n: usize) -> Vec<bool> {
    // Z3 get-value: ((m0 true) (m1 false) ...), any whitespace/newlines.
    let mut v = vec![false; n];
    let cleaned = out.replace('(', " ").replace(')', " ");
    let toks: Vec<&str> = cleaned.split_whitespace().collect();
    let mut i = 0;
    while i + 1 < toks.len() {
        if let Some(idx) = toks[i].strip_prefix('m').and_then(|d| d.parse::<usize>().ok()) {
            if idx < n {
                v[idx] = toks[i + 1] == "true";
            }
        }
        i += 1;
    }
    v
}

#[derive(Clone)]
enum MPhase {
    CheckAll,
    MapQuery,
    CheckSeed { seed: Vec<usize> },
    Grow { keep: Vec<usize>, rest: Vec<usize>, i: usize },
    Shrink { cand: Vec<usize>, i: usize },
    Done,
}

struct Lattice {
    active: Vec<String>,        // index = selector bit
    capped: bool,               // true ⇒ budget hit, NOT exhaustive (honest)
    unknown: bool,              // Z3 said `unknown` — never claim consistent
    map: Vec<Vec<i32>>,         // CNF over bits: +k ⇒ bit k-1 true, -k ⇒ false
    muses: Vec<Vec<usize>>,
    mcses: Vec<Vec<usize>>,
    phase: MPhase,
    out: LatOut,
}

impl Lattice {
    fn new(core: &Core) -> Lattice {
        let active = core.active_ids();
        Lattice {
            active,
            capped: false,
            unknown: false,
            map: Vec::new(),
            muses: Vec::new(),
            mcses: Vec::new(),
            phase: MPhase::CheckAll,
            out: LatOut::default(),
        }
    }
    fn ids(&self, idxs: &[usize]) -> Vec<String> {
        idxs.iter().map(|&i| self.active[i].clone()).collect()
    }
    /// SMT for "is there still an unexplored region?" — a model of the
    /// boolean map is a seed subset.
    fn map_script(&self) -> String {
        let n = self.active.len();
        let mut s = String::from("(set-logic ALL)\n");
        for i in 0..n {
            s.push_str(&format!("(declare-const m{i} Bool)\n"));
        }
        for cl in &self.map {
            let lits = cl
                .iter()
                .map(|&l| {
                    let k = (l.abs() - 1) as usize;
                    if l > 0 { format!("m{k}") } else { format!("(not m{k})") }
                })
                .collect::<Vec<_>>()
                .join(" ");
            s.push_str(&format!("(assert (or {lits} false))\n"));
        }
        s.push_str("(check-sat)\n(get-value (");
        s.push_str(&(0..n).map(|i| format!("m{i}")).collect::<Vec<_>>().join(" "));
        s.push_str("))\n");
        s
    }
    fn next_script(&self, core: &Core) -> Option<String> {
        match &self.phase {
            MPhase::CheckAll => Some(core.smt_assume(&self.active)),
            MPhase::MapQuery => Some(self.map_script()),
            MPhase::CheckSeed { seed } => Some(core.smt_assume(&self.ids(seed))),
            MPhase::Grow { keep, rest, i } => {
                let mut t = keep.clone();
                t.push(rest[*i]);
                Some(core.smt_assume(&self.ids(&t)))
            }
            MPhase::Shrink { cand, i } => {
                let mut t = cand.clone();
                t.remove(*i);
                Some(core.smt_assume(&self.ids(&t)))
            }
            MPhase::Done => None,
        }
    }
    fn budget_hit(&self) -> bool {
        self.muses.len() + self.mcses.len() >= LAT_BUDGET
    }
    fn feed(&mut self, out: &str) {
        let h = z3_head(out);
        let unsat = h.starts_with("unsat");
        match self.phase.clone() {
            MPhase::CheckAll => {
                if unsat {
                    self.phase = MPhase::MapQuery; // there is ≥1 conflict
                } else if h.starts_with("sat") {
                    self.finalize(); // proven consistent
                } else {
                    self.unknown = true; // Z3 undecided — do NOT claim consistent
                    self.finalize();
                }
            }
            MPhase::MapQuery => {
                if unsat || self.budget_hit() {
                    self.capped = self.budget_hit() && !(unsat);
                    self.finalize();
                } else {
                    let model = parse_bool_model(out, self.active.len());
                    let seed: Vec<usize> =
                        (0..self.active.len()).filter(|&i| model[i]).collect();
                    self.phase = MPhase::CheckSeed { seed };
                }
            }
            MPhase::CheckSeed { seed } => {
                if unsat {
                    // seed is unsatisfiable → shrink it to an MUS
                    self.phase = if seed.len() <= 1 {
                        self.record_mus(seed);
                        MPhase::MapQuery
                    } else {
                        MPhase::Shrink { cand: seed, i: 0 }
                    };
                } else {
                    // seed is satisfiable → grow it to an MSS
                    let rest: Vec<usize> = (0..self.active.len())
                        .filter(|i| !seed.contains(i))
                        .collect();
                    if rest.is_empty() {
                        self.record_mss(seed);
                        self.phase = MPhase::MapQuery;
                    } else {
                        self.phase = MPhase::Grow { keep: seed, rest, i: 0 };
                    }
                }
            }
            MPhase::Grow { mut keep, rest, i } => {
                if !unsat {
                    keep.push(rest[i]);
                }
                let ni = i + 1;
                if ni < rest.len() {
                    self.phase = MPhase::Grow { keep, rest, i: ni };
                } else {
                    self.record_mss(keep);
                    self.phase = MPhase::MapQuery;
                }
            }
            MPhase::Shrink { mut cand, i } => {
                if unsat {
                    cand.remove(i); // still conflicting without cand[i]
                    if i >= cand.len() {
                        self.record_mus(cand);
                        self.phase = MPhase::MapQuery;
                    } else {
                        self.phase = MPhase::Shrink { cand, i };
                    }
                } else {
                    let ni = i + 1; // cand[i] is necessary
                    if ni >= cand.len() {
                        self.record_mus(cand);
                        self.phase = MPhase::MapQuery;
                    } else {
                        self.phase = MPhase::Shrink { cand, i: ni };
                    }
                }
            }
            MPhase::Done => {}
        }
    }
    fn record_mus(&mut self, mut mus: Vec<usize>) {
        mus.sort_unstable();
        if !self.muses.contains(&mus) {
            self.muses.push(mus.clone());
        }
        // block its up-set: a future seed must drop ≥1 element of this MUS
        self.map.push(mus.iter().map(|&i| -(i as i32 + 1)).collect());
    }
    fn record_mss(&mut self, mss: Vec<usize>) {
        let mut keep = mss.clone();
        keep.sort_unstable();
        let mcs: Vec<usize> = (0..self.active.len())
            .filter(|i| !keep.contains(i))
            .collect();
        if !mcs.is_empty() && !self.mcses.contains(&mcs) {
            self.mcses.push(mcs.clone());
        }
        // block its down-set: a future seed must add ≥1 element outside it
        let clause: Vec<i32> = (0..self.active.len())
            .filter(|i| !keep.contains(i))
            .map(|i| i as i32 + 1)
            .collect();
        if clause.is_empty() {
            // MSS = everything ⇒ the set is consistent; nothing to block,
            // force the map closed.
            self.map.push(vec![]);
        } else {
            self.map.push(clause);
        }
    }
    fn finalize(&mut self) {
        let to_ids = |v: &Vec<usize>, act: &[String]| -> Vec<String> {
            v.iter().map(|&i| act[i].clone()).collect()
        };
        if self.unknown {
            self.out.consistent = false; // undecided is NOT a verdict
            self.out.unknown = true;
            self.out.mus = Vec::new();
            self.out.mcs = Vec::new();
            self.out.mss = Vec::new();
        } else if self.muses.is_empty() {
            self.out.consistent = true;
            self.out.mus = Vec::new();
            self.out.mcs = Vec::new();
            self.out.mss = vec![self.active.clone()];
            self.out.af = argumentation(&[], &self.out.mss, &self.active);
        } else {
            self.out.consistent = false;
            self.out.mus = self.muses.iter().map(|m| to_ids(m, &self.active)).collect();
            self.out.mcs = self.mcses.iter().map(|m| to_ids(m, &self.active)).collect();
            self.out.mss = self
                .mcses
                .iter()
                .map(|m| {
                    (0..self.active.len())
                        .filter(|i| !m.contains(i))
                        .map(|i| self.active[i].clone())
                        .collect()
                })
                .collect();
            self.out.af = argumentation(&self.out.mus, &self.out.mss, &self.active);
        }
        self.out.capped = self.capped;
        self.out.done = true;
        self.phase = MPhase::Done;
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

// ---- defeasible / prioritized reasoning ----------------------------------
// A world model with defaults ("birds fly") and exceptions ("penguins
// don't") is NOT inconsistent — the specific overrides the general. We
// implement Poole-style logical specificity (computed from the user's
// OWN strict claims, not hand-ranked) on top of a Brewka preferred-
// subtheory: process defaults best-first (more specific, then more
// entrenched), keep each only while it stays consistent. What gets
// skipped is an *overridden default*, reported as such — not a conflict.
//
// Scope, stated honestly (also surfaced in-product): specificity is
// auto-detected only for the single-antecedent universally-quantified
// rule shape  ∀x. (Pred(x) ⇒ …).  For anything else the priority is the
// entrenchment weight. Strict claims that conflict among themselves are
// still a genuine inconsistency — defeasibility never rescues those.

fn antecedent_pred(f: &Formula) -> Option<(String, String)> {
    if let Formula::Forall { vars, body } = f {
        if vars.len() == 1 {
            if let Formula::Imp { a, .. } = body.as_ref() {
                if let Formula::Pred { name, args } = a.as_ref() {
                    if let [Term::Var { name: vn }] = args.as_slice() {
                        if *vn == vars[0].name {
                            return Some((name.clone(), vars[0].sort.clone()));
                        }
                    }
                }
            }
        }
    }
    None
}

impl Core {
    fn priority_of(&self, id: &str) -> i64 {
        self.weight_of(id)
    }
    /// Is the antecedent of rule `ai` (predicate `pa` over sort `s`)
    /// logically *more specific* than that of `aj` (predicate `pb`),
    /// given the STRICT claims as background? i.e. strict ∧ pa(k) ⊨ pb(k)
    /// for a fresh k. Unsat ⇒ pa ⊑ pb.
    fn smt_more_specific(&self, pa: &str, pb: &str, sort: &str) -> String {
        let mut s = String::from("(set-logic ALL)\n");
        s.push_str(&self.decls_smt());
        for &i in &self.active() {
            if !self.claims[i].defeasible {
                s.push_str(&format!("(assert {})\n", form_smt(&self.claims[i].formula)));
            }
        }
        s.push_str(&format!("(declare-const __k {sort})\n"));
        s.push_str(&format!("(assert ({pa} __k))\n"));
        s.push_str(&format!("(assert (not ({pb} __k)))\n"));
        s.push_str("(check-sat)\n");
        s
    }
}

enum DPhase {
    Strict,
    Spec { pairs: Vec<(usize, usize)>, i: usize },
    Brewka { order: Vec<String>, i: usize },
    Done,
}

struct DefeasibleDriver {
    strict: Vec<String>,
    defs: Vec<String>,                 // defeasible claim ids
    ant: BTreeMap<String, (String, String)>, // id -> (pred, sort)
    spec: Vec<(String, String)>,       // (more_specific_id, less_specific_id)
    accepted: Vec<String>,
    overridden: Vec<String>,
    phase: DPhase,
    status: String, // coherent | defeasibly-coherent | inconsistent
}

impl DefeasibleDriver {
    fn new(core: &Core) -> DefeasibleDriver {
        let mut strict = Vec::new();
        let mut defs = Vec::new();
        let mut ant = BTreeMap::new();
        for &i in &core.active() {
            let c = &core.claims[i];
            if c.defeasible {
                defs.push(c.id.clone());
                if let Some(a) = antecedent_pred(&c.formula) {
                    ant.insert(c.id.clone(), a);
                }
            } else {
                strict.push(c.id.clone());
            }
        }
        DefeasibleDriver {
            strict,
            defs,
            ant,
            spec: Vec::new(),
            accepted: Vec::new(),
            overridden: Vec::new(),
            phase: DPhase::Strict,
            status: String::new(),
        }
    }
    fn spec_pairs(&self) -> Vec<(usize, usize)> {
        let mut v = Vec::new();
        for a in 0..self.defs.len() {
            for b in 0..self.defs.len() {
                if a != b
                    && self.ant.contains_key(&self.defs[a])
                    && self.ant.contains_key(&self.defs[b])
                {
                    v.push((a, b));
                }
            }
        }
        v
    }
    fn next_script(&self, core: &Core) -> Option<String> {
        match &self.phase {
            DPhase::Strict => Some(core.smt_assume(&self.strict)),
            DPhase::Spec { pairs, i } => {
                let (a, b) = pairs[*i];
                let (pa, s) = &self.ant[&self.defs[a]];
                let (pb, _) = &self.ant[&self.defs[b]];
                Some(core.smt_more_specific(pa, pb, s))
            }
            DPhase::Brewka { order, i } => {
                let mut keep = self.strict.clone();
                keep.extend(self.accepted.iter().cloned());
                keep.push(order[*i].clone());
                Some(core.smt_assume(&keep))
            }
            DPhase::Done => None,
        }
    }
    fn feed(&mut self, core: &Core, out: &str) {
        let h = z3_head(out);
        match std::mem::replace(&mut self.phase, DPhase::Done) {
            DPhase::Strict => {
                if h.starts_with("unsat") {
                    self.status = "inconsistent".into(); // strict core conflicts
                    self.phase = DPhase::Done;
                } else if self.defs.is_empty() {
                    self.status = "coherent".into();
                    self.accepted = self.strict.clone();
                    self.phase = DPhase::Done;
                } else {
                    let pairs = self.spec_pairs();
                    self.phase = if pairs.is_empty() {
                        DPhase::Brewka { order: self.ranked(core), i: 0 }
                    } else {
                        DPhase::Spec { pairs, i: 0 }
                    };
                }
            }
            DPhase::Spec { pairs, i } => {
                if h.starts_with("unsat") {
                    let (a, b) = pairs[i];
                    // a's antecedent ⊑ b's: a is the more specific rule
                    self.spec
                        .push((self.defs[a].clone(), self.defs[b].clone()));
                }
                let ni = i + 1;
                self.phase = if ni < pairs.len() {
                    DPhase::Spec { pairs, i: ni }
                } else {
                    DPhase::Brewka { order: self.ranked(core), i: 0 }
                };
            }
            DPhase::Brewka { order, i } => {
                if h.starts_with("sat") {
                    self.accepted.push(order[i].clone());
                } else {
                    self.overridden.push(order[i].clone());
                }
                let ni = i + 1;
                if ni < order.len() {
                    self.phase = DPhase::Brewka { order, i: ni };
                } else {
                    let mut acc = self.strict.clone();
                    acc.extend(self.accepted.iter().cloned());
                    self.accepted = acc;
                    self.status = if self.overridden.is_empty() {
                        "coherent".into()
                    } else {
                        "defeasibly-coherent".into()
                    };
                    self.phase = DPhase::Done;
                }
            }
            DPhase::Done => {}
        }
    }
    fn ranked(&self, core: &Core) -> Vec<String> {
        let depth = |id: &String| self.spec.iter().filter(|(m, _)| m == id).count() as i64;
        let mut o = self.defs.clone();
        o.sort_by(|x, y| {
            depth(y)
                .cmp(&depth(x))
                .then_with(|| core.priority_of(y).cmp(&core.priority_of(x)))
                .then_with(|| x.cmp(y))
        });
        o
    }
    fn result(&self) -> serde_json::Value {
        // for each overridden default, which accepted claims beat it:
        // its more-specific siblings if any, else the accepted set it
        // could not join.
        let beaten_by: Vec<serde_json::Value> = self
            .overridden
            .iter()
            .map(|o| {
                let mut by: Vec<String> = self
                    .spec
                    .iter()
                    .filter(|(m, l)| l == o && self.accepted.contains(m))
                    .map(|(m, _)| m.clone())
                    .collect();
                if by.is_empty() {
                    by = self.accepted.clone();
                }
                serde_json::json!({ "id": o, "by": by })
            })
            .collect();
        serde_json::json!({
            "status": self.status,
            "strict_inconsistent": self.status == "inconsistent",
            "position": self.accepted,
            "overridden": beaten_by,
            "specificity": self.spec
                .iter().map(|(m, l)| vec![m.clone(), l.clone()])
                .collect::<Vec<_>>(),
            "done": matches!(self.phase, DPhase::Done),
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
    fn state_round_trips() {
        // A branch in the trajectory tree is a saved Core. Export the
        // penguin world-model, import it into a fresh engine, and verify
        // the imported branch analyses *identically* (same conflict).
        let mut a = Core::default();
        a.seed_demo();
        a.ingest(
            r#"{"claims":[{"id":"c_pen_nofly","weight":3,
              "formula":{"op":"forall","vars":[{"name":"x","sort":"Thing"}],
                "body":{"op":"imp",
                  "a":{"op":"pred","name":"Penguin","args":[{"t":"var","name":"x"}]},
                  "b":{"op":"not","x":{"op":"pred","name":"Flies","args":[{"t":"var","name":"x"}]}}}}}]}"#,
        );
        let snap = a.export_state();
        let mut b = Core::default();
        assert!(b.import_state(&snap), "snapshot must import");
        assert_eq!(a.meta(), b.meta(), "imported branch must match exactly");
        let ra = lattice(&a);
        if ra.get("skip").is_some() {
            return;
        }
        let rb = lattice(&b);
        assert_eq!(ra, rb, "forked branch must analyse identically");
        assert!(!b.import_state("{ not json"), "garbage must be rejected");
    }

    #[test]
    fn argumentation_penguin_framework() {
        // Single 4-claim irreducible disagreement → in the Dung reading
        // every pair of the four attacks every other (6 undirected
        // edges); no claim survives in *all* maximal coherent positions
        // (each position drops a different one) so none is skeptically
        // accepted; all four are credulously defensible; none defeated.
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
        let af = &r["af"];
        let atk = as_sets(&af["attacks"]);
        assert_eq!(atk.len(), 6, "all 4 mutually attack: {atk:?}");
        assert!(af["skeptical"].as_array().unwrap().is_empty());
        assert_eq!(af["credulous"].as_array().unwrap().len(), 4);
        assert!(af["defeated"].as_array().unwrap().is_empty());
    }

    #[test]
    fn argumentation_two_conflicts_and_consistent() {
        // Two independent conflicts: attack edges are exactly the two
        // contradictory pairs (no cross edges). And a coherent world-model
        // makes every claim skeptically accepted with no attacks.
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
        let mut atk = as_sets(&r["af"]["attacks"]);
        atk.sort();
        assert_eq!(
            atk,
            vec![
                vec!["c_np".to_string(), "c_p".to_string()],
                vec!["c_nq".to_string(), "c_q".to_string()]
            ],
            "attacks must be exactly the two contradictory pairs"
        );

        let mut k = Core::default();
        k.seed_demo();
        let rk = lattice(&k);
        if rk.get("skip").is_some() {
            return;
        }
        let af = &rk["af"];
        assert!(af["attacks"].as_array().unwrap().is_empty());
        let mut sk: Vec<String> = af["skeptical"]
            .as_array()
            .unwrap()
            .iter()
            .map(|v| v.as_str().unwrap().to_string())
            .collect();
        sk.sort();
        assert_eq!(
            sk,
            vec!["c_birds_fly", "c_penguin_bird", "c_tweety_penguin"],
            "in a coherent world-model every claim is skeptically accepted"
        );
        assert!(af["defeated"].as_array().unwrap().is_empty());
    }

    fn defeasible(c: &Core) -> serde_json::Value {
        let mut d = DefeasibleDriver::new(c);
        let mut g = 0;
        while let Some(s) = d.next_script(c) {
            let o = match z3(&s) { Some(o) => o, None => return serde_json::json!({"skip": true}) };
            d.feed(c, &o);
            g += 1;
            assert!(g < 500, "defeasible driver did not terminate");
        }
        d.result()
    }

    #[test]
    fn defeasible_penguin_specificity_from_own_kb() {
        // Penguin world-model, but the two RULES are defaults; the facts
        // ("every penguin is a bird", "Tweety is a penguin") stay strict.
        // Nothing is hand-ranked: specificity is DERIVED from the user's
        // own strict claim that penguins are birds, so "penguins don't
        // fly" beats "birds fly". Result: not a contradiction — a default
        // overridden.
        let mut c = Core::default();
        c.seed_demo();
        c.ingest(
            r#"{"claims":[{"id":"c_pen_nofly","weight":1,"defeasible":true,
              "formula":{"op":"forall","vars":[{"name":"x","sort":"Thing"}],
                "body":{"op":"imp",
                  "a":{"op":"pred","name":"Penguin","args":[{"t":"var","name":"x"}]},
                  "b":{"op":"not","x":{"op":"pred","name":"Flies","args":[{"t":"var","name":"x"}]}}}}}]}"#,
        );
        c.claims.iter_mut().find(|x| x.id == "c_birds_fly").unwrap().defeasible = true;
        let r = defeasible(&c);
        if r.get("skip").is_some() {
            return;
        }
        assert_eq!(r["status"], "defeasibly-coherent", "{r}");
        let ov: Vec<String> = r["overridden"].as_array().unwrap()
            .iter().map(|o| o["id"].as_str().unwrap().to_string()).collect();
        assert_eq!(ov, vec!["c_birds_fly"], "the GENERAL rule is the one overridden");
        let pos: Vec<String> = r["position"].as_array().unwrap()
            .iter().map(|v| v.as_str().unwrap().to_string()).collect();
        assert!(pos.contains(&"c_pen_nofly".to_string()), "the specific rule survives");
        // and the specificity edge was logically derived, not declared
        let spec = as_sets(&r["specificity"]);
        assert!(
            spec.iter().any(|e| e == &vec!["c_birds_fly".to_string(), "c_pen_nofly".to_string()]
                || e == &vec!["c_pen_nofly".to_string(), "c_birds_fly".to_string()]),
            "penguin⊑bird specificity must be derived from the KB: {spec:?}"
        );
    }

    #[test]
    fn defeasible_does_not_rescue_strict_contradiction() {
        // {P, ¬P} both STRICT → still a genuine inconsistency; the
        // defeasible reading must NOT paper over it.
        let mut c = Core::default();
        c.ingest(
            r#"{"preds":[{"name":"P","args":[],"gloss":"p"}],
              "claims":[
               {"id":"c_p","formula":{"op":"pred","name":"P","args":[]}},
               {"id":"c_np","formula":{"op":"not","x":{"op":"pred","name":"P","args":[]}}}]}"#,
        );
        let r = defeasible(&c);
        if r.get("skip").is_some() {
            return;
        }
        assert_eq!(r["status"], "inconsistent");
        assert_eq!(r["strict_inconsistent"], true);
    }

    #[test]
    fn defeasible_flag_defaults_false_and_round_trips() {
        let mut c = Core::default();
        assert!(c.ingest(
            r#"{"preds":[{"name":"P","args":[],"gloss":"p"}],
              "claims":[{"id":"c1","formula":{"op":"pred","name":"P","args":[]}}]}"#
        ).0);
        assert_eq!(c.meta()["claims"][0]["defeasible"], false);
        let snap = c.export_state();
        let mut d = Core::default();
        assert!(d.import_state(&snap));
        assert_eq!(d.meta()["claims"][0]["defeasible"], false);
    }

    #[test]
    fn triage_prompt_carries_the_conflict() {
        // Deterministic (no LLM): the triage prompt must name each
        // conflicting claim's id, verbatim source, English render and
        // IR, and ask the intrinsic-vs-formalization question.
        let mut c = Core::default();
        c.seed_demo();
        let p = c.triage_prompt(&["c_birds_fly".into(), "c_tweety_penguin".into()]);
        assert!(p.contains("id c_birds_fly") && p.contains("id c_tweety_penguin"));
        assert!(p.contains("Birds can fly.") && p.contains("Tweety is a penguin."));
        assert!(p.contains("for every") && p.contains("\"op\""), "render + IR present");
        assert!(p.contains("INTRINSIC") && p.contains("FORMALIZATION"));
        assert!(p.contains("\"verdict\"") && p.contains("\"fix\""));
    }

    #[test]
    fn marco_scales_past_the_old_cap() {
        // 12 active claims — the OLD enumerator capped at 10 and produced
        // nothing. One genuine 3-claim conflict {P, P⇒Q, ¬Q} plus 9
        // independent consistent claims. MARCO must enumerate it exactly
        // and NOT report capped.
        let mut c = Core::default();
        let mut preds = String::from(r#"{"name":"P","args":[]},{"name":"Q","args":[]}"#);
        for i in 1..=9 {
            preds.push_str(&format!(r#",{{"name":"R{i}","args":[]}}"#));
        }
        let mut claims = String::from(
            r#"{"id":"c_a","formula":{"op":"pred","name":"P","args":[]}},
               {"id":"c_b","formula":{"op":"imp","a":{"op":"pred","name":"P","args":[]},"b":{"op":"pred","name":"Q","args":[]}}},
               {"id":"c_c","formula":{"op":"not","x":{"op":"pred","name":"Q","args":[]}}}"#,
        );
        for i in 1..=9 {
            claims.push_str(&format!(
                r#",{{"id":"c_r{i}","formula":{{"op":"pred","name":"R{i}","args":[]}}}}"#
            ));
        }
        assert!(c.ingest(&format!(r#"{{"preds":[{preds}],"claims":[{claims}]}}"#)).0);
        assert_eq!(c.active().len(), 12);
        let r = lattice(&c);
        if r.get("skip").is_some() {
            return;
        }
        assert_eq!(r["consistent"], false);
        assert_eq!(r["capped"], false, "MARCO must not cap at 12 claims");
        let mut mus = as_sets(&r["mus"]);
        mus.sort();
        assert_eq!(mus, vec![vec!["c_a".to_string(), "c_b".into(), "c_c".into()]]);
        let mcs = as_sets(&r["mcs"]);
        assert_eq!(mcs.len(), 3, "3 ways out (drop any of the 3): {mcs:?}");
        assert!(mcs.iter().all(|m| m.len() == 1));
        let mss = as_sets(&r["mss"]);
        assert_eq!(mss.len(), 3);
        assert!(mss.iter().all(|p| p.len() == 11), "each position keeps 11/12");
    }

    #[test]
    fn autodeclare_underdeclared_ir_is_well_formed_not_unknown() {
        // IR that declares the predicate but uses 0-ary constants it
        // never declares (exactly what an elicited model produced).
        // Before autodeclare this compiled to undeclared-symbol SMT, Z3
        // errored, and we mislabeled it. Now it must be well-formed:
        // a real verdict, never `unknown`.
        let mut c = Core::default();
        assert!(c.ingest(
            r#"{"sorts":["Thing"],
              "preds":[{"name":"Bigger","args":["Thing","Thing"],"gloss":"x>y"}],
              "claims":[
               {"id":"c_ab","formula":{"op":"pred","name":"Bigger","args":[
                 {"t":"app","name":"A","args":[]},{"t":"app","name":"B","args":[]}]}},
               {"id":"c_bc","formula":{"op":"pred","name":"Bigger","args":[
                 {"t":"app","name":"B","args":[]},{"t":"app","name":"C","args":[]}]}}]}"#
        ).0);
        let r = lattice(&c);
        if r.get("skip").is_some() { return; }
        assert_eq!(r["unknown"], false, "must NOT be undecided: {r}");
        assert_eq!(r["consistent"], true, "two unrelated facts cohere");

        // Same under-declared style, but a strict cycle with transitivity
        // and irreflexivity → a genuine MUS Z3 must find.
        let mut d = Core::default();
        assert!(d.ingest(
            r#"{"sorts":["Thing"],
              "preds":[{"name":"Gt","args":["Thing","Thing"],"gloss":"x>y"}],
              "claims":[
               {"id":"c_trans","formula":{"op":"forall",
                 "vars":[{"name":"x","sort":"Thing"},{"name":"y","sort":"Thing"},{"name":"z","sort":"Thing"}],
                 "body":{"op":"imp",
                   "a":{"op":"and","xs":[
                     {"op":"pred","name":"Gt","args":[{"t":"var","name":"x"},{"t":"var","name":"y"}]},
                     {"op":"pred","name":"Gt","args":[{"t":"var","name":"y"},{"t":"var","name":"z"}]}]},
                   "b":{"op":"pred","name":"Gt","args":[{"t":"var","name":"x"},{"t":"var","name":"z"}]}}}},
               {"id":"c_irr","formula":{"op":"forall","vars":[{"name":"x","sort":"Thing"}],
                 "body":{"op":"not","x":{"op":"pred","name":"Gt","args":[{"t":"var","name":"x"},{"t":"var","name":"x"}]}}}},
               {"id":"c_ab","formula":{"op":"pred","name":"Gt","args":[{"t":"app","name":"A","args":[]},{"t":"app","name":"B","args":[]}]}},
               {"id":"c_bc","formula":{"op":"pred","name":"Gt","args":[{"t":"app","name":"B","args":[]},{"t":"app","name":"C","args":[]}]}},
               {"id":"c_ca","formula":{"op":"pred","name":"Gt","args":[{"t":"app","name":"C","args":[]},{"t":"app","name":"A","args":[]}]}}]}"#
        ).0);
        let r = lattice(&d);
        if r.get("skip").is_some() { return; }
        assert_eq!(r["unknown"], false);
        assert_eq!(r["consistent"], false, "a strict 3-cycle is inconsistent");
        assert!(!r["mus"].as_array().unwrap().is_empty(), "the cycle is a real MUS");
    }

    #[test]
    fn scenario_seed_is_a_rich_lattice() {
        // The "demonstrate the depth" seed: exactly 3 overlapping
        // irreducible disagreements, several coherent positions, and the
        // two independent facts skeptically accepted (in every position).
        let mut c = Core::default();
        c.seed_scenario();
        let r = lattice(&c);
        if r.get("skip").is_some() { return; }
        assert_eq!(r["unknown"], false);
        assert_eq!(r["consistent"], false);
        assert_eq!(r["capped"], false, "must be exhaustive, not budget-capped");
        let mut mus = as_sets(&r["mus"]); // as_sets sorts each inner vec
        mus.sort();
        let want = |xs: &[&str]| xs.iter().map(|s| s.to_string()).collect::<Vec<_>>();
        assert_eq!(
            mus,
            vec![
                want(&["c_not_reviewed", "c_quality", "c_quality_needs_review"]),
                want(&["c_not_reviewed", "c_ship_needs_review", "c_ships"]),
                want(&["c_ship_needs_tests", "c_ships", "c_tests_fail"]),
            ],
            "exactly the three intended overlapping conflicts"
        );
        assert!(r["mss"].as_array().unwrap().len() >= 3, "several coherent positions");
        let sk = &r["af"]["skeptical"];
        let sk: Vec<&str> = sk.as_array().unwrap().iter().filter_map(|v| v.as_str()).collect();
        assert!(sk.contains(&"c_budget") && sk.contains(&"c_team"),
            "independent facts must be skeptically accepted: {sk:?}");
    }

    #[test]
    fn marco_mcs_is_reiter_dual_of_mus() {
        // Independent oracle: MARCO's MCS collection must equal the
        // minimal hitting sets of MARCO's MUS collection (Reiter /
        // Liffiton–Sakallah duality), on both the single- and
        // two-conflict cases.
        for setup in [0u8, 1u8] {
            let mut c = Core::default();
            if setup == 0 {
                c.seed_demo();
                c.ingest(
                    r#"{"claims":[{"id":"c_pen_nofly",
                      "formula":{"op":"forall","vars":[{"name":"x","sort":"Thing"}],
                        "body":{"op":"imp",
                          "a":{"op":"pred","name":"Penguin","args":[{"t":"var","name":"x"}]},
                          "b":{"op":"not","x":{"op":"pred","name":"Flies","args":[{"t":"var","name":"x"}]}}}}}]}"#,
                );
            } else {
                c.ingest(
                    r#"{"preds":[{"name":"P","args":[]},{"name":"Q","args":[]}],
                      "claims":[
                       {"id":"c_p","formula":{"op":"pred","name":"P","args":[]}},
                       {"id":"c_np","formula":{"op":"not","x":{"op":"pred","name":"P","args":[]}}},
                       {"id":"c_q","formula":{"op":"pred","name":"Q","args":[]}},
                       {"id":"c_nq","formula":{"op":"not","x":{"op":"pred","name":"Q","args":[]}}}]}"#,
                );
            }
            let r = lattice(&c);
            if r.get("skip").is_some() {
                return;
            }
            let mus: Vec<Vec<String>> = as_sets(&r["mus"]);
            let active: Vec<String> = c.active_ids();
            let mut expect = minimal_hitting_sets(&mus, &active);
            for s in expect.iter_mut() {
                s.sort();
            }
            expect.sort();
            let mut got = as_sets(&r["mcs"]);
            got.sort();
            assert_eq!(got, expect, "MCS must be the minimal hitting sets of MUS (setup {setup})");
        }
    }

    #[test]
    fn belief_elicitation_prompt_is_honest_and_well_formed() {
        // Deterministic, offline: the elicitation prompt must carry the
        // IR grammar, the symbol-reuse discipline (or contradictions
        // hide), the domain + N, and — load-bearing — the honest framing
        // that we test mutual consistency of THESE statements, not truth.
        let mut c = Core::default();
        c.seed_demo(); // vocabulary should be carried in for reuse
        let p = c.belief_elicitation_prompt("animal flight and taxonomy", 12);
        assert!(p.contains("animal flight and taxonomy") && p.contains("12 separate"));
        assert!(p.contains("\"op\"") && p.contains("forall"), "IR grammar present");
        assert!(p.contains("REUSE one symbol per concept"));
        assert!(p.contains("not their truth"), "honesty framing present");
        assert!(p.contains("Bird"), "existing vocabulary carried for reuse");
        assert!(!p.contains("```"), "must forbid code fences");
    }

    /// The headline "next level" demo, kept OUT of the default suite:
    /// elicit a model's own beliefs, then let Z3/MARCO find the minimal
    /// self-contradictions among *its stated beliefs*. External model +
    /// network, so it is #[ignore]d and offline-skips. Two backends:
    ///   WMT_KIMI=1 [WMT_DOMAIN="..."] cargo test --release \
    ///     -- --ignored --nocapture llm_self_probe       (local `kimi`)
    ///   WMT_OR_KEY=sk-or-... [WMT_OR_MODEL=...] [WMT_DOMAIN="..."] …
    ///                                                   (OpenRouter)
    #[test]
    #[ignore]
    fn llm_self_probe() {
        let domain = std::env::var("WMT_DOMAIN").unwrap_or_else(|_| {
            "everyday physical & biological commonsense: animals, flight, \
             size, age, and habitats — include the obvious".into()
        });
        let mut c = Core::default();
        let prompt = c.belief_elicitation_prompt(&domain, 14);
        let or_key = std::env::var("WMT_OR_KEY").ok().filter(|k| !k.is_empty());

        let (content, model): (String, String) = if std::env::var("WMT_KIMI").is_ok() {
            // Local emulation of the workflow via the `kimi` CLI agent —
            // no external API, no rate limits. Prompt piped on stdin.
            let mut ch = match Command::new("kimi")
                .args(["--quiet", "--print", "--input-format", "text"])
                .stdin(Stdio::piped())
                .stdout(Stdio::piped())
                .stderr(Stdio::null())
                .spawn()
            {
                Ok(c) => c,
                Err(_) => { eprintln!("SKIP: no `kimi` on PATH"); return; }
            };
            ch.stdin.as_mut().unwrap().write_all(prompt.as_bytes()).unwrap();
            drop(ch.stdin.take());
            let o = ch.wait_with_output().unwrap();
            (String::from_utf8_lossy(&o.stdout).to_string(), "kimi (local)".into())
        } else if let Some(key) = or_key {
            // Free OpenRouter providers are flaky/rate-limited; bound
            // each call and fall back across known-good free models.
            let mut models: Vec<String> = Vec::new();
            if let Ok(m) = std::env::var("WMT_OR_MODEL") { if !m.is_empty() { models.push(m); } }
            for m in ["nvidia/nemotron-3-super-120b-a12b:free", "google/gemma-4-31b-it:free"] {
                if !models.iter().any(|x| x == m) { models.push(m.into()); }
            }
            let mut content = String::new();
            let mut used = String::new();
            for m in &models {
                let body = serde_json::json!({
                    "model": m,
                    "messages": [{"role": "user", "content": prompt}],
                    "temperature": 0
                })
                .to_string();
                let out = Command::new("curl")
                    .args([
                        "-s", "--max-time", "150",
                        "https://openrouter.ai/api/v1/chat/completions",
                        "-H", &format!("Authorization: Bearer {key}"),
                        "-H", "Content-Type: application/json",
                        "-d", &body,
                    ])
                    .output();
                let resp = match out {
                    Ok(o) => String::from_utf8_lossy(&o.stdout).to_string(),
                    Err(_) => { eprintln!("SKIP: no curl"); return; }
                };
                let v: serde_json::Value = serde_json::from_str(&resp).unwrap_or_default();
                let cc = v["choices"][0]["message"]["content"].as_str().unwrap_or("");
                if !cc.is_empty() {
                    content = cc.to_string();
                    used = m.clone();
                    break;
                }
                eprintln!("  {m}: empty/err ({})", resp.chars().take(160).collect::<String>().replace('\n', " "));
            }
            (content, used)
        } else {
            eprintln!("SKIP: set WMT_KIMI=1 (local) or WMT_OR_KEY=sk-or-… to run");
            return;
        };
        if content.trim().is_empty() {
            eprintln!("SKIP: backend returned empty (rate-limited/contended) — rerun");
            return;
        }
        let content = content.as_str();
        let (a, b) = (content.find('{'), content.rfind('}'));
        let ir = match (a, b) {
            (Some(a), Some(b)) if b > a => &content[a..=b],
            _ => { eprintln!("SKIP: no JSON in reply"); return; }
        };
        let _ = std::fs::write("/tmp/wmt_selfprobe_last.json", ir);
        let (ok, errs) = c.ingest(ir);
        assert!(ok, "model IR did not ingest: {errs:?}\n---\n{ir}");
        let n = c.active().len();
        eprintln!("\n=== {model} stated {n} beliefs about: {domain}");
        for cl in &c.claims {
            eprintln!(
                "  [{}] {}",
                cl.id,
                if cl.source.is_empty() { form_en(&cl.formula) } else { cl.source.clone() }
            );
        }
        let r = lattice(&c);
        if r.get("skip").is_some() { return; }
        if r["unknown"] == serde_json::json!(true) {
            eprintln!("=== UNDECIDED — Z3 errored/unknown on this set; NOT a verdict");
            eprintln!("=== (ill-formed or undecidable IR; honest non-answer, not 'consistent')");
            return;
        }
        eprintln!("=== consistent: {} (capped {})", r["consistent"], r["capped"]);
        for (k, m) in r["mus"].as_array().unwrap_or(&vec![]).iter().enumerate() {
            let ids: Vec<&str> = m.as_array().unwrap().iter().filter_map(|x| x.as_str()).collect();
            eprintln!("--- self-contradiction {}: it cannot consistently hold all of:", k + 1);
            for id in ids {
                if let Some(cl) = c.claims.iter().find(|cc| cc.id == id) {
                    eprintln!("    • {}", if cl.source.is_empty() { form_en(&cl.formula) } else { cl.source.clone() });
                }
            }
        }
        // The pipeline must have produced a verdict; we do NOT assert the
        // model is inconsistent (honest — it may cohere on a given run).
        assert!(r.get("consistent").is_some(), "MARCO produced no verdict");
        eprintln!("=== (this checks the consistency of THESE elicited statements, not their truth)");
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
