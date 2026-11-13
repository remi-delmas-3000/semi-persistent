// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Equality certificates for the Lean checker (`proofs/checker`).
//!
//! [`EGraph::write_certificate`] writes, for each equality a `check-eq`
//! established, a derivation in the six inferences of the checker's kernel
//! (`proofs/checker/SemperCheck/Kernel.lean`): reflexivity, symmetry,
//! transitivity, an axiom (a `union`), a rule instance, and congruence modulo
//! an operator's laws. The checker re-derives every step against the program
//! text, so this writer is not trusted: a step it gets wrong is rejected, never
//! accepted.
//!
//! Each node of the certificate is an e-node's term: its operator over the
//! certificate nodes of its original children (with each AC child repeated by
//! its multiplicity), which is the term the client built. A forest edge
//! becomes:
//!
//! * `Axiom`: an `axiom` step, cited by the byte offset of its `union` form.
//! * `Congruence`: a `cong` step whose premises prove each pair of original
//!   children (by position, swapped for a commutative operator, or grouped by
//!   class for an associative one).
//! * `Build`, `Normalize` and the completion steps between two nodes of an
//!   associative, AC or ACI operator: a `cong` step over the arguments both
//!   nodes flatten to, each argument rewritten to one member of its class (the
//!   unit's node for the unit's class).
//!
//! * `Rewrite`: a `rule` step for the command the rule was written in. The
//!   writer reads the command as the checker's reader does, recovers the
//!   variable bindings by matching the rule's sides against the two nodes
//!   modulo their classes, and joins the instance to the two nodes by `cong`
//!   steps whose premises are forest paths.
//!
//! An edge the writer cannot express (cancellation, an assumption, a law the
//! kernel does not model) leaves its goal unproved; the writer counts it by
//! kind.

use super::*;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::fmt::Write as _;

/// A term as the program wrote it: an application, a literal, or a node a
/// `let` name stands for.
#[derive(Clone, Debug)]
pub enum ClientTerm<G> {
    Node(G),
    Lit(String),
    App(String, Vec<ClientTerm<G>>),
}

/// The two terms of a `union` or a `check-eq` as written (`None` for a term
/// the writer cannot spell), and the nodes built for them.
#[derive(Clone, Debug)]
pub struct CertGoal<G> {
    pub lhs: Option<ClientTerm<G>>,
    pub rhs: Option<ClientTerm<G>>,
    pub a: G,
    pub b: G,
}

/// What [`EGraph::write_certificate`] wrote.
#[derive(Debug, Default)]
pub struct CertStats {
    pub goals: usize,
    pub proved: usize,
    pub nodes: usize,
    pub steps: usize,
    /// Edges the writer could not express, by justification kind.
    pub unsupported: BTreeMap<&'static str, usize>,
}

/// A literal as the program spells it: a string in quotes, any other literal
/// as it displays.
pub fn lit_spelling<V: std::fmt::Display + std::fmt::Debug>(v: &V) -> String {
    let d = format!("{v:?}");
    if d.starts_with('"') { d } else { v.to_string() }
}

/// The kernel's reading of an operator's laws (`Kind` in `Syntax.lean`).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum LeanKind {
    Plain,
    Comm,
    Assoc,
    Ac,
    Aci,
}

/// Byte offsets of the top-level forms of `src` whose head is `head`.
pub fn form_offsets(src: &str, head: &str) -> Vec<usize> {
    let b = src.as_bytes();
    let mut out = Vec::new();
    let mut depth = 0usize;
    let mut i = 0;
    while i < b.len() {
        match b[i] {
            b';' => {
                while i < b.len() && b[i] != b'\n' {
                    i += 1;
                }
                continue;
            }
            b'"' => {
                i += 1;
                while i < b.len() && b[i] != b'"' {
                    if b[i] == b'\\' {
                        i += 1;
                    }
                    i += 1;
                }
            }
            b'(' => {
                if depth == 0 {
                    let rest = &src[i + 1..];
                    let name: String = rest
                        .chars()
                        .take_while(|c| !c.is_whitespace() && *c != '(' && *c != ')')
                        .collect();
                    if name == head {
                        out.push(i);
                    }
                }
                depth += 1;
            }
            b')' => depth = depth.saturating_sub(1),
            _ => {}
        }
        i += 1;
    }
    out
}

/// What [`EGraph::write_certificate`] reads besides the e-graph.
pub struct CertInputs<'a, G> {
    /// The program text: the certificate cites its commands by byte offset.
    pub src: &'a str,
    /// The `check-eq` commands that held, in program order.
    pub goals: &'a [CertGoal<G>],
    /// The `union` commands, by axiom id.
    pub unions: &'a [CertGoal<G>],
    /// The source offset of each rule's left-hand side, by rule id.
    pub rule_spans: &'a HashMap<usize, usize>,
    /// The term each `let` name was bound to, as written.
    pub globals: &'a HashMap<String, ClientTerm<G>>,
}

/// An S-expression as the checker's reader (`readTop` in `Parse.lean`) reads it.
#[derive(Clone, Debug)]
enum Sx {
    Atom(String),
    List(Vec<Sx>),
}

fn is_ws(c: u8) -> bool {
    matches!(c, b' ' | b'\t' | b'\r' | b'\n')
}

fn skip_ws(b: &[u8], i: &mut usize) {
    while *i < b.len() {
        if b[*i] == b';' {
            while *i < b.len() && b[*i] != b'\n' {
                *i += 1;
            }
        } else if is_ws(b[*i]) {
            *i += 1;
        } else {
            break;
        }
    }
}

fn read_sx(src: &str, i: &mut usize) -> Option<Sx> {
    let b = src.as_bytes();
    skip_ws(b, i);
    match *b.get(*i)? {
        b'(' => {
            *i += 1;
            let mut v = Vec::new();
            loop {
                skip_ws(b, i);
                if *b.get(*i)? == b')' {
                    *i += 1;
                    return Some(Sx::List(v));
                }
                v.push(read_sx(src, i)?);
            }
        }
        b')' => None,
        b'"' => {
            let start = *i;
            *i += 1;
            loop {
                match *b.get(*i)? {
                    b'\\' => *i += 2,
                    b'"' => {
                        *i += 1;
                        break;
                    }
                    _ => *i += 1,
                }
            }
            Some(Sx::Atom(src.get(start..*i)?.to_string()))
        }
        _ => {
            let start = *i;
            while *i < b.len() && !is_ws(b[*i]) && !matches!(b[*i], b'(' | b')' | b';') {
                *i += 1;
            }
            Some(Sx::Atom(src.get(start..*i)?.to_string()))
        }
    }
}

/// The top-level forms of `src` with their byte offsets; empty for input the
/// checker's reader rejects.
fn read_top(src: &str) -> Vec<(usize, Sx)> {
    let b = src.as_bytes();
    let mut i = 0;
    let mut out = Vec::new();
    loop {
        skip_ws(b, &mut i);
        if i >= b.len() {
            return out;
        }
        let at = i;
        match read_sx(src, &mut i) {
            Some(x) => out.push((at, x)),
            None => return Vec::new(),
        }
    }
}

/// `isLiteral` of `Parse.lean`.
fn is_literal(a: &str) -> bool {
    match a.chars().next() {
        Some(c) => {
            c.is_ascii_digit()
                || c == '"'
                || (c == '-' && a.chars().count() > 1)
                || a == "true"
                || a == "false"
        }
        None => false,
    }
}

/// A rule pattern (`Pat` of `Syntax.lean`). A `let` name stands for its term;
/// `Opaque` is one whose term the interpreter could not spell, which keeps
/// the rule's position in the command's rule list but matches nothing.
#[derive(Clone, Debug)]
enum CPat<G> {
    Var(String),
    Lit(String),
    App(String, Vec<CPat<G>>),
    Term(ClientTerm<G>),
    Opaque,
}

#[derive(Clone, Debug)]
struct CRule<G> {
    lhs: CPat<G>,
    rhs: CPat<G>,
    eqs: Vec<(CPat<G>, CPat<G>)>,
}

impl<G> CPat<G> {
    fn vars<'p>(&'p self, out: &mut Vec<&'p str>) {
        match self {
            CPat::Var(x) => out.push(x),
            CPat::App(_, ps) => ps.iter().for_each(|p| p.vars(out)),
            _ => {}
        }
    }
}

/// The names in scope at a command, as the checker's reader has them there.
struct Scope<'a, G> {
    ops: HashSet<String>,
    globals: HashMap<String, Option<&'a ClientTerm<G>>>,
}

impl<G: Clone> Scope<'_, G> {
    /// `Env.pat` of `Parse.lean`.
    fn pat(&self, x: &Sx) -> Option<CPat<G>> {
        match x {
            Sx::Atom(a) => {
                if is_literal(a) {
                    Some(CPat::Lit(a.clone()))
                } else if a.starts_with("..") || a.starts_with(':') || a.contains(':') {
                    None
                } else if let Some(t) = self.globals.get(a) {
                    Some(t.map_or(CPat::Opaque, |t| CPat::Term(t.clone())))
                } else if self.ops.contains(a) {
                    Some(CPat::App(a.clone(), Vec::new()))
                } else {
                    Some(CPat::Var(a.clone()))
                }
            }
            Sx::List(v) => match v.split_first() {
                Some((Sx::Atom(f), args)) if f != "=" && self.ops.contains(f) => Some(CPat::App(
                    f.clone(),
                    args.iter().map(|a| self.pat(a)).collect::<Option<_>>()?,
                )),
                _ => None,
            },
        }
    }

    /// `Env.guard` of `Parse.lean`.
    fn guard(&self, x: &Sx) -> Option<Vec<(CPat<G>, CPat<G>)>> {
        if let Sx::List(v) = x
            && let [Sx::Atom(e), p, q] = v.as_slice()
            && e == "="
        {
            return Some(vec![(self.pat(p)?, self.pat(q)?)]);
        }
        self.pat(x).map(|_| Vec::new())
    }

    /// `Env.rewriteRules` of `Parse.lean`.
    fn rewrite_rules(&self, lhs: &Sx, rhs: &Sx, tags: &[Sx]) -> Vec<CRule<G>> {
        let (lhs, root) = match lhs {
            Sx::List(v) => match v.as_slice() {
                [Sx::Atom(e), Sx::Atom(x), p] if e == "=" => (
                    p,
                    self.pat(p)
                        .map(|pp| vec![(CPat::Var(x.clone()), pp)])
                        .unwrap_or_default(),
                ),
                _ => (lhs, Vec::new()),
            },
            _ => (lhs, Vec::new()),
        };
        let mut when = None;
        for k in 0..tags.len() {
            if matches!(&tags[k], Sx::Atom(a) if a == ":when") && k + 1 < tags.len() {
                when = Some(&tags[k + 1]);
                break;
            }
        }
        let guards = match when {
            Some(Sx::List(gs)) => gs
                .iter()
                .map(|g| self.guard(g))
                .collect::<Option<Vec<_>>>()
                .map(|v| v.concat()),
            Some(_) => None,
            None => Some(Vec::new()),
        };
        if tags.iter().any(|t| matches!(t, Sx::Atom(a) if a == ":let")) {
            return Vec::new();
        }
        match (self.pat(lhs), self.pat(rhs), guards) {
            (Some(l), Some(r), Some(gs)) => {
                let mut eqs = root;
                eqs.extend(gs);
                vec![CRule {
                    lhs: l,
                    rhs: r,
                    eqs,
                }]
            }
            _ => Vec::new(),
        }
    }

    /// `Env.ruleRules` of `Parse.lean`.
    fn rule_rules(&self, body: &[Sx], actions: &[Sx]) -> Vec<CRule<G>> {
        let Some(eqs) = body
            .iter()
            .map(|g| self.guard(g))
            .collect::<Option<Vec<_>>>()
            .map(|v| v.concat())
        else {
            return Vec::new();
        };
        fn subst<G: Clone>(lets: &[(String, CPat<G>)], p: CPat<G>) -> CPat<G> {
            match p {
                CPat::Var(x) => lets
                    .iter()
                    .find(|(n, _)| *n == x)
                    .map_or(CPat::Var(x), |(_, q)| q.clone()),
                CPat::App(f, ps) => CPat::App(f, ps.into_iter().map(|q| subst(lets, q)).collect()),
                other => other,
            }
        }
        let mut lets: Vec<(String, CPat<G>)> = Vec::new();
        let mut out = Vec::new();
        for a in actions {
            let Sx::List(v) = a else { continue };
            match v.as_slice() {
                [Sx::Atom(u), p, q] if u == "union" => {
                    if let (Some(l), Some(r)) = (self.pat(p), self.pat(q)) {
                        out.push(CRule {
                            lhs: subst(&lets, l),
                            rhs: subst(&lets, r),
                            eqs: eqs.clone(),
                        });
                    }
                }
                [Sx::Atom(l), Sx::Atom(x), t] if l == "let" => match self.pat(t) {
                    Some(p) => {
                        let p = subst(&lets, p);
                        lets.insert(0, (x.clone(), p));
                    }
                    None => return out,
                },
                _ => {}
            }
        }
        out
    }

    /// The rules of the command `x` (`step` of `Parse.lean`).
    fn rules(&self, x: &Sx) -> Vec<CRule<G>> {
        let Sx::List(v) = x else { return Vec::new() };
        match v.as_slice() {
            [Sx::Atom(h), l, r, tags @ ..] if h == "rewrite" => self.rewrite_rules(l, r, tags),
            [Sx::Atom(h), l, r, tags @ ..] if h == "birewrite" => {
                let mut rs = self.rewrite_rules(l, r, tags);
                rs.extend(self.rewrite_rules(r, l, tags));
                rs
            }
            [Sx::Atom(h), Sx::List(body), Sx::List(actions), ..] if h == "rule" => {
                self.rule_rules(body, actions)
            }
            _ => Vec::new(),
        }
    }
}

/// A certificate under construction. It outlives the e-graph states it is
/// written from: a lazy `check-eq` is proved before its transaction discards
/// the nodes it built ([`EGraph::cert_prove_goals`]), and
/// [`EGraph::cert_forget`] then drops what was keyed by a discarded node id.
/// The certificate's nodes are terms, and its steps are equalities between
/// terms, so both stay valid across a restore.
pub struct CertState<G> {
    nodes: String,
    steps: String,
    lines: String,
    n_nodes: usize,
    n_steps: usize,
    n_goals: usize,
    n_proved: usize,
    /// The next `check-eq` (index into the interpreter's list) to prove.
    next_goal: usize,
    node_of: HashMap<usize, usize>,
    key_of: HashMap<(String, Vec<usize>), usize>,
    proved: HashMap<(usize, usize), Option<usize>>,
    in_progress: HashSet<(usize, usize)>,
    axiom_offsets: Vec<usize>,
    check_offsets: Vec<usize>,
    /// Each certificate node: its operator (`None` for a literal) and children.
    table: Vec<(Option<String>, Vec<usize>)>,
    kinds: HashMap<String, (LeanKind, Option<usize>)>,
    unsupported: BTreeMap<&'static str, usize>,
    forms: Vec<(usize, Sx)>,
    /// The rules of the command at each offset, as the checker reads them.
    rules_at: HashMap<usize, Vec<CRule<G>>>,
}

impl<G> CertState<G> {
    /// An empty certificate for the program `src`.
    pub fn new(src: &str) -> Self {
        CertState {
            nodes: String::new(),
            steps: String::new(),
            lines: String::new(),
            n_nodes: 0,
            n_steps: 0,
            n_goals: 0,
            n_proved: 0,
            next_goal: 0,
            node_of: HashMap::new(),
            key_of: HashMap::new(),
            proved: HashMap::new(),
            in_progress: HashSet::new(),
            axiom_offsets: form_offsets(src, "union"),
            check_offsets: form_offsets(src, "check-eq"),
            table: Vec::new(),
            kinds: HashMap::new(),
            unsupported: BTreeMap::new(),
            forms: read_top(src),
            rules_at: HashMap::new(),
        }
    }

    /// Writes the certificate (format `semper-cert 1`).
    pub fn finish<W: std::io::Write>(self, mut out: W) -> std::io::Result<CertStats> {
        writeln!(out, "semper-cert 1")?;
        out.write_all(self.nodes.as_bytes())?;
        out.write_all(self.steps.as_bytes())?;
        out.write_all(self.lines.as_bytes())?;
        Ok(CertStats {
            goals: self.n_goals,
            proved: self.n_proved,
            nodes: self.n_nodes,
            steps: self.n_steps,
            unsupported: self.unsupported,
        })
    }
}

struct Writer<'a, Cfg: EGraphConfig, L: LitVal, const TRACK: bool, const PROOFS: bool>
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
    Cfg::Policy: crate::config::StorePolicy<Cfg, TRACK>,
{
    eg: &'a EGraph<Cfg, L, TRACK, PROOFS>,
    st: &'a mut CertState<Cfg::G>,
    unions: &'a [CertGoal<Cfg::G>],
    rule_spans: &'a HashMap<usize, usize>,
    globals: &'a HashMap<String, ClientTerm<Cfg::G>>,
}

impl<Cfg: EGraphConfig, L: LitVal, const TRACK: bool, const PROOFS: bool> std::ops::Deref
    for Writer<'_, Cfg, L, TRACK, PROOFS>
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
    Cfg::Policy: crate::config::StorePolicy<Cfg, TRACK>,
{
    type Target = CertState<Cfg::G>;
    fn deref(&self) -> &Self::Target {
        self.st
    }
}

impl<Cfg: EGraphConfig, L: LitVal, const TRACK: bool, const PROOFS: bool> std::ops::DerefMut
    for Writer<'_, Cfg, L, TRACK, PROOFS>
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
    Cfg::Policy: crate::config::StorePolicy<Cfg, TRACK>,
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.st
    }
}

impl<'a, Cfg: EGraphConfig, L: LitVal, const TRACK: bool, const PROOFS: bool>
    Writer<'a, Cfg, L, TRACK, PROOFS>
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
    Cfg::Policy: crate::config::StorePolicy<Cfg, TRACK>,
{
    fn kind(&self, op: Cfg::O) -> LeanKind {
        match &self.eg.ops.info(op).kind {
            OpKind::Commutative { .. } => LeanKind::Comm,
            OpKind::A {
                dir: crate::registry::AssocDir::Both,
                ..
            } => LeanKind::Assoc,
            OpKind::MSet { .. } => LeanKind::Ac,
            OpKind::Set { .. } => LeanKind::Aci,
            _ => LeanKind::Plain,
        }
    }

    /// The original children of `id`, each AC child repeated by its multiplicity.
    fn children(&self, id: Cfg::G) -> Vec<Cfg::G> {
        let mut g = Vec::new();
        let mut ms = Vec::new();
        if self.eg.nodes.original_children(id, &mut g, &mut ms) {
            for c in &ms {
                let k = Cfg::mset_child_mult(c).to_usize();
                for _ in 0..k {
                    g.push(Cfg::mset_child_id(c));
                }
            }
            return g;
        }
        self.eg.for_each_child(id, |c, m| {
            for _ in 0..m.to_usize() {
                g.push(c);
            }
        });
        g
    }

    fn add_node(&mut self, key: (String, Vec<usize>), line: String) -> usize {
        if let Some(&k) = self.key_of.get(&key) {
            return k;
        }
        let k = self.n_nodes;
        self.n_nodes += 1;
        self.nodes.push_str(&format!("n {k} {line}\n"));
        let entry = if key.0.starts_with("#lit ") {
            (None, Vec::new())
        } else {
            (Some(key.0.clone()), key.1.clone())
        };
        self.table.push(entry);
        self.key_of.insert(key, k);
        k
    }

    /// The certificate node of e-node `id`'s term.
    fn node(&mut self, id: Cfg::G) -> usize {
        if let Some(&k) = self.node_of.get(&id.to_usize()) {
            return k;
        }
        let k = if let Some(v) = self.eg.get_lit_val(id) {
            let v = lit_spelling(v);
            self.add_node((format!("#lit {v}"), Vec::new()), format!("l {v}"))
        } else {
            let kids: Vec<usize> = self
                .children(id)
                .into_iter()
                .map(|c| self.node(c))
                .collect();
            let op = self.eg.node_op_name(id).to_string();
            let mut line = format!("a {op}");
            for c in &kids {
                let _ = write!(line, " {c}");
            }
            self.add_node((op, kids), line)
        };
        self.node_of.insert(id.to_usize(), k);
        k
    }

    fn step(&mut self, s: String) -> usize {
        let k = self.n_steps;
        self.n_steps += 1;
        self.steps.push_str(&format!("s {k} {s}\n"));
        k
    }

    fn miss(&mut self, why: &'static str) -> Option<usize> {
        *self.unsupported.entry(why).or_default() += 1;
        None
    }

    /// A step proving `a = b`, if the writer can express its derivation.
    fn prove(&mut self, a: Cfg::G, b: Cfg::G) -> Option<usize> {
        let key = (a.to_usize(), b.to_usize());
        if let Some(&r) = self.proved.get(&key) {
            return r;
        }
        if a == b {
            let na = self.node(a);
            let s = self.step(format!("refl {na}"));
            self.proved.insert(key, Some(s));
            return Some(s);
        }
        if !self.in_progress.insert(key) {
            return self.miss("cyclic premise");
        }
        let r = self.prove_path(a, b);
        self.in_progress.remove(&key);
        self.proved.insert(key, r);
        r
    }

    /// The forest path from `a` to `b`, edge by edge, joined by `trans`.
    fn prove_path(&mut self, a: Cfg::G, b: Cfg::G) -> Option<usize> {
        let mut buf = ProofBuf::new();
        if !self.eg.explain(a, b, &mut buf) {
            return self.miss("not equal");
        }
        let edges: Vec<(Cfg::G, Cfg::G, Justification<Cfg::G>)> = buf.steps.clone();
        // Order the edges along the path from `a`.
        let mut cur = a;
        let mut used = vec![false; edges.len()];
        let mut acc: Option<usize> = None;
        while cur != b {
            let next = edges
                .iter()
                .enumerate()
                .find(|(i, (x, y, _))| !used[*i] && (*x == cur || *y == cur));
            let Some((i, &(x, y, j))) = next else {
                return self.miss("broken path");
            };
            used[i] = true;
            let e = self.edge(x, y, j)?;
            let (e, to) = if x == cur {
                (e, y)
            } else {
                (self.step(format!("symm {e}")), x)
            };
            acc = Some(match acc {
                None => e,
                Some(p) => self.step(format!("trans {p} {e}")),
            });
            cur = to;
        }
        acc
    }

    /// A step proving `x = y` for one forest edge.
    fn edge(&mut self, x: Cfg::G, y: Cfg::G, j: Justification<Cfg::G>) -> Option<usize> {
        match j {
            Justification::Axiom { .. } => {
                let id: Cfg::A = j.axiom_id::<Cfg::A>()?;
                let i = id.to_usize();
                let Some(&off) = self.axiom_offsets.get(i) else {
                    return self.miss("axiom without a union form");
                };
                let Some(u) = self.unions.get(i).cloned() else {
                    return self.miss("axiom without its terms");
                };
                // written lhs = a's node, so a's node = written lhs by symm.
                let (cl, la) = self.written(&u.lhs, u.a)?;
                let (cr, lb) = self.written(&u.rhs, u.b)?;
                let ax = self.step(format!("axiom {off} {cl} {cr}"));
                let la = la.map(|s| self.step(format!("symm {s}")));
                let nb = self.node(u.b);
                let s = self.chain(&[la, Some(ax), lb], nb);
                if (x, y) == (u.a, u.b) {
                    Some(s)
                } else if (x, y) == (u.b, u.a) {
                    Some(self.step(format!("symm {s}")))
                } else {
                    self.miss("axiom edge between other nodes")
                }
            }
            Justification::Congruence { .. } => self.congruence(x, y),
            Justification::Build { .. }
            | Justification::Normalize { .. }
            | Justification::ACSuperposition { .. }
            | Justification::ACInterReduction { .. }
            | Justification::ACAxiomCP { .. }
            | Justification::InverseCancel { .. } => self.assoc_cong(x, y),
            Justification::Rewrite { rule_id, .. } => self.rewrite(x, y, rule_id.to_usize()),
            Justification::Cancellative { .. } => self.miss("cancellative"),
            Justification::Assumption { .. } => self.miss("assumption"),
            Justification::Filler => self.miss("filler"),
        }
    }

    fn congruence(&mut self, x: Cfg::G, y: Cfg::G) -> Option<usize> {
        let op = self.eg.node_op(x);
        if op != self.eg.node_op(y) {
            return self.miss("congruence across operators");
        }
        let kind = self.kind(op);
        if matches!(kind, LeanKind::Assoc | LeanKind::Ac | LeanKind::Aci) {
            return self.assoc_cong(x, y);
        }
        let (cx, cy) = (self.children(x), self.children(y));
        let straight = cx.len() == cy.len()
            && cx
                .iter()
                .zip(&cy)
                .all(|(a, b)| self.eg.find_const(*a) == self.eg.find_const(*b));
        let order: Vec<Cfg::G> = if straight {
            cy.clone()
        } else if kind == LeanKind::Comm && cy.len() == 2 {
            vec![cy[1], cy[0]]
        } else {
            return self.miss("congruence children differ");
        };
        let mut prems = Vec::new();
        for (a, b) in cx.iter().zip(&order) {
            if a != b {
                prems.push(self.prove(*a, *b)?);
            }
        }
        let (nx, ny) = (self.node(x), self.node(y));
        let f = self.eg.ops.info(op).name.clone();
        let mut s = format!("cong {f} {nx} {ny}");
        for p in prems {
            let _ = write!(s, " {p}");
        }
        Some(self.step(s))
    }

    /// The rules of the command at offset `o`, read in the scope the checker's
    /// reader has there.
    fn rules_for(&mut self, o: usize) -> Vec<CRule<Cfg::G>> {
        if let Some(rs) = self.rules_at.get(&o) {
            return rs.clone();
        }
        let mut scope = Scope {
            ops: HashSet::new(),
            globals: HashMap::new(),
        };
        let mut cmd = None;
        for (off, x) in &self.forms {
            if *off == o {
                cmd = Some(x);
                break;
            }
            let Sx::List(v) = x else { continue };
            match v.as_slice() {
                [Sx::Atom(h), Sx::Atom(f), _, _, ..] if h == "function" || h == "constructor" => {
                    scope.ops.insert(f.clone());
                }
                [Sx::Atom(h), Sx::Atom(f), ..] if h == "relation" => {
                    scope.ops.insert(f.clone());
                }
                [Sx::Atom(h), _, variants @ ..] if h == "datatype" => {
                    for w in variants {
                        if let Sx::List(w) = w
                            && let Some(Sx::Atom(f)) = w.first()
                        {
                            scope.ops.insert(f.clone());
                        }
                    }
                }
                [Sx::Atom(h), Sx::Atom(x), _] if h == "let" => {
                    scope.globals.insert(x.clone(), self.globals.get(x));
                }
                _ => {}
            }
        }
        let rs = cmd.map(|c| scope.rules(c)).unwrap_or_default();
        self.rules_at.insert(o, rs.clone());
        rs
    }

    /// Up to 64 members of `g`'s class, `g` first.
    fn members(&self, g: Cfg::G) -> Vec<Cfg::G> {
        let mut v = vec![g];
        v.extend(self.eg.class_members(g).filter(|&m| m != g).take(63));
        v
    }

    /// Whether `p` matches a member of `g`'s class, each variable bound in
    /// `sig` standing for its class; binds the variables it meets unbound.
    fn pmatch(
        &mut self,
        p: &CPat<Cfg::G>,
        g: Cfg::G,
        sig: &mut Vec<(String, Cfg::G)>,
        fuel: &mut usize,
    ) -> bool {
        if *fuel == 0 {
            return false;
        }
        *fuel -= 1;
        match p {
            CPat::Var(x) => match sig.iter().find(|(n, _)| n == x) {
                Some(&(_, b)) => self.eg.find_const(b) == self.eg.find_const(g),
                None => {
                    sig.push((x.clone(), g));
                    true
                }
            },
            CPat::Lit(v) => self.lit_member(v, g).is_some(),
            CPat::Term(t) => self.term_member(t, g).is_some(),
            CPat::Opaque => false,
            CPat::App(f, ps) => {
                for m in self.members(g) {
                    if self.eg.get_lit_val(m).is_some() || self.eg.node_op_name(m) != f {
                        continue;
                    }
                    for kids in self.orders(m, ps.len()) {
                        let save = sig.len();
                        let mut ok = true;
                        for (q, &k) in ps.iter().zip(&kids) {
                            if !self.pmatch(q, k, sig, fuel) {
                                ok = false;
                                break;
                            }
                        }
                        if ok {
                            return true;
                        }
                        sig.truncate(save);
                    }
                }
                false
            }
        }
    }

    /// The orders in which a pattern of `n` arguments may take `m`'s
    /// children: as stored, and swapped for a commutative operator, whose
    /// `cong` step the kernel checks either way.
    fn orders(&self, m: Cfg::G, n: usize) -> Vec<Vec<Cfg::G>> {
        let kids = self.children(m);
        if kids.len() != n {
            return Vec::new();
        }
        let mut out = vec![kids.clone()];
        if n == 2 && self.kind(self.eg.node_op(m)) == LeanKind::Comm {
            out.push(vec![kids[1], kids[0]]);
        }
        out
    }

    fn lit_member(&self, v: &str, g: Cfg::G) -> Option<Cfg::G> {
        self.members(g)
            .into_iter()
            .find(|&m| self.eg.get_lit_val(m).is_some_and(|l| lit_spelling(l) == v))
    }

    fn term_member(&mut self, t: &ClientTerm<Cfg::G>, g: Cfg::G) -> Option<Cfg::G> {
        let c = self.client_node(t)?;
        self.members(g).into_iter().find(|&m| self.node(m) == c)
    }

    /// The certificate node of `p` with each variable read from `sig`.
    fn inst(&mut self, p: &CPat<Cfg::G>, sig: &[(String, Cfg::G)]) -> Option<usize> {
        match p {
            CPat::Var(x) => {
                let g = sig.iter().find(|(n, _)| n == x)?.1;
                Some(self.node(g))
            }
            CPat::Lit(v) => {
                Some(self.add_node((format!("#lit {v}"), Vec::new()), format!("l {v}")))
            }
            CPat::Term(t) => self.client_node(t),
            CPat::Opaque => None,
            CPat::App(f, ps) => {
                let mut ids = Vec::with_capacity(ps.len());
                for q in ps {
                    ids.push(self.inst(q, sig)?);
                }
                let mut line = format!("a {f}");
                for c in &ids {
                    let _ = write!(line, " {c}");
                }
                Some(self.add_node((f.clone(), ids), line))
            }
        }
    }

    /// A step proving `p`'s instance by `sig` equal to `g`'s node (`Some(None)`
    /// when they are the same node), for a `p` that `pmatch` matched to `g`.
    fn tie(
        &mut self,
        p: &CPat<Cfg::G>,
        g: Cfg::G,
        sig: &[(String, Cfg::G)],
    ) -> Option<Option<usize>> {
        let (m, s) = match p {
            CPat::Var(x) => (sig.iter().find(|(n, _)| n == x)?.1, None),
            CPat::Lit(v) => (self.lit_member(v, g)?, None),
            CPat::Term(t) => (self.term_member(t, g)?, None),
            CPat::Opaque => return None,
            CPat::App(f, ps) => {
                let mut found = None;
                for m in self.members(g) {
                    if self.eg.get_lit_val(m).is_some() || self.eg.node_op_name(m) != f {
                        continue;
                    }
                    for kids in self.orders(m, ps.len()) {
                        let mut probe = sig.to_vec();
                        let mut fuel = 10_000;
                        if ps
                            .iter()
                            .zip(&kids)
                            .all(|(q, &k)| self.pmatch(q, k, &mut probe, &mut fuel))
                            && probe.len() == sig.len()
                        {
                            found = Some((m, kids));
                            break;
                        }
                    }
                    if found.is_some() {
                        break;
                    }
                }
                let (m, kids) = found?;
                let mut prems = Vec::new();
                for (q, &k) in ps.iter().zip(&kids) {
                    if let Some(t) = self.tie(q, k, sig)? {
                        prems.push(t);
                    }
                }
                let a = self.inst(p, sig)?;
                let nm = self.node(m);
                let s = if a == nm && prems.is_empty() {
                    None
                } else {
                    let mut line = format!("cong {f} {a} {nm}");
                    for t in prems {
                        let _ = write!(line, " {t}");
                    }
                    Some(self.step(line))
                };
                (m, s)
            }
        };
        let path = if m == g {
            None
        } else {
            Some(self.prove(m, g)?)
        };
        Some(match (s, path) {
            (None, None) => None,
            (Some(a), None) | (None, Some(a)) => Some(a),
            (Some(a), Some(b)) => Some(self.step(format!("trans {a} {b}"))),
        })
    }

    /// Binds `sig` so that rule `r` sends `l` to `rr`: the left side matched
    /// to `l`, each equality premise to the class of its bound side, and the
    /// right side to `rr`. Returns each premise's anchor node.
    fn bind(
        &mut self,
        r: &CRule<Cfg::G>,
        l: Cfg::G,
        rr: Cfg::G,
        sig: &mut Vec<(String, Cfg::G)>,
    ) -> Option<Vec<Cfg::G>> {
        let mut fuel = 10_000;
        if !self.pmatch(&r.lhs, l, sig, &mut fuel) {
            return None;
        }
        let bound = |sig: &[(String, Cfg::G)], p: &CPat<Cfg::G>| match p {
            CPat::Var(x) => sig.iter().find(|(n, _)| n == x).map(|e| e.1),
            _ => None,
        };
        let mut anchors: Vec<Option<Cfg::G>> = vec![None; r.eqs.len()];
        // Two passes: a premise whose sides are both unbound after the left
        // side may be anchored by the right side's bindings.
        for pass in 0..2 {
            if pass == 1 && !self.pmatch(&r.rhs, rr, sig, &mut fuel) {
                return None;
            }
            for (i, (p, q)) in r.eqs.iter().enumerate() {
                if anchors[i].is_some() {
                    continue;
                }
                let a = match (bound(sig, p), bound(sig, q)) {
                    (Some(a), _) => {
                        if !self.pmatch(q, a, sig, &mut fuel) {
                            return None;
                        }
                        a
                    }
                    (None, Some(a)) => {
                        if !self.pmatch(p, a, sig, &mut fuel) {
                            return None;
                        }
                        a
                    }
                    // The root binding of a `rewrite`: `(= v lhs)`.
                    (None, None) if matches!(p, CPat::Var(_)) && pass == 0 => {
                        if !self.pmatch(q, l, sig, &mut fuel) || !self.pmatch(p, l, sig, &mut fuel)
                        {
                            return None;
                        }
                        l
                    }
                    _ => continue,
                };
                anchors[i] = Some(a);
            }
        }
        let mut vars = Vec::new();
        r.lhs.vars(&mut vars);
        r.rhs.vars(&mut vars);
        for (p, q) in &r.eqs {
            p.vars(&mut vars);
            q.vars(&mut vars);
        }
        if vars.iter().any(|v| !sig.iter().any(|(n, _)| n == v)) {
            return None;
        }
        anchors.into_iter().collect()
    }

    /// `x = y` for a `Rewrite` edge of rule `rule_id`.
    fn rewrite(&mut self, x: Cfg::G, y: Cfg::G, rule_id: usize) -> Option<usize> {
        let Some(&span) = self.rule_spans.get(&rule_id) else {
            return self.miss("rewrite without a source");
        };
        let Some(o) = self
            .forms
            .iter()
            .map(|(o, _)| *o)
            .take_while(|&o| o <= span)
            .last()
        else {
            return self.miss("rewrite without a source");
        };
        let rules = self.rules_for(o);
        if rules.is_empty() {
            // A rest variable, a multiplicity, a primitive or a `:let`: the
            // checker's reader reads no rule from the command.
            return self.miss("rule outside the checker's language");
        }
        for (j, r) in rules.iter().enumerate() {
            for (l, rr, flip) in [(x, y, false), (y, x, true)] {
                let mut sig = Vec::new();
                let Some(anchors) = self.bind(r, l, rr, &mut sig) else {
                    continue;
                };
                let tl = self.tie(&r.lhs, l, &sig)?;
                let tr = self.tie(&r.rhs, rr, &sig)?;
                let mut prems = Vec::new();
                for ((p, q), &a) in r.eqs.iter().zip(&anchors) {
                    let tp = self.tie(p, a, &sig)?;
                    let tq = self
                        .tie(q, a, &sig)?
                        .map(|t| self.step(format!("symm {t}")));
                    let ip = self.inst(p, &sig)?;
                    prems.push(self.chain(&[tp, tq], ip));
                }
                let (a, b) = (self.inst(&r.lhs, &sig)?, self.inst(&r.rhs, &sig)?);
                let mut line = format!("rule {o} {j} {a} {b} {}", sig.len());
                for (n, g) in sig.clone() {
                    let c = self.node(g);
                    let _ = write!(line, " {n} {c}");
                }
                for p in prems {
                    let _ = write!(line, " {p}");
                }
                let st = self.step(line);
                let tl = tl.map(|t| self.step(format!("symm {t}")));
                let nl = self.node(l);
                let s = self.chain(&[tl, Some(st), tr], nl);
                return Some(if flip {
                    self.step(format!("symm {s}"))
                } else {
                    s
                });
            }
        }
        self.miss("rewrite not matched")
    }

    /// The arguments `n` flattens to under `op`, and the applications of `op`
    /// below `n` it flattens through; `None` for an application with no
    /// arguments.
    fn view(
        &self,
        op: Cfg::O,
        n: Cfg::G,
        root: bool,
        out: &mut Vec<Cfg::G>,
        inner: &mut Vec<Cfg::G>,
    ) -> Option<()> {
        if self.eg.get_lit_val(n).is_none() && self.eg.node_op(n) == op {
            let kids = self.children(n);
            if kids.is_empty() {
                return None;
            }
            if !root {
                inner.push(n);
            }
            for c in kids {
                self.view(op, c, false, out, inner)?;
            }
        } else {
            out.push(n);
        }
        Some(())
    }

    /// `x = y` modulo the laws of the associative operator of either node.
    fn assoc_cong(&mut self, x: Cfg::G, y: Cfg::G) -> Option<usize> {
        let op = [x, y].into_iter().find_map(|n| {
            if self.eg.get_lit_val(n).is_some() {
                return None;
            }
            let op = self.eg.node_op(n);
            matches!(
                self.kind(op),
                LeanKind::Assoc | LeanKind::Ac | LeanKind::Aci
            )
            .then_some(op)
        });
        let Some(op) = op else {
            return self.miss("law step without an associative operator");
        };
        let kind = self.kind(op);
        let (mut vx, mut vy, mut inner) = (Vec::new(), Vec::new(), Vec::new());
        if self.view(op, x, true, &mut vx, &mut inner).is_none()
            || self.view(op, y, true, &mut vy, &mut inner).is_none()
        {
            return self.miss("empty application");
        }
        // An argument whose class holds an application of `op` that the other
        // side flattens through is replaced by that application, whose
        // arguments the kernel then flattens in: this is how a build that
        // spliced a nested node, or a completion rule, rewrote it.
        let mut expand: HashMap<Cfg::G, (Cfg::G, Vec<Cfg::G>)> = HashMap::new();
        for &n in &inner {
            let c = self.eg.find_const(n);
            if expand.contains_key(&c) {
                continue;
            }
            let (mut v, mut ignore) = (Vec::new(), Vec::new());
            if self.view(op, n, true, &mut v, &mut ignore).is_some() {
                expand.insert(c, (n, v));
            }
        }
        let unit = self.eg.unit_node(op);
        let unit_class = unit.map(|u| self.eg.find_const(u));
        // One member per class stands for the class: the unit's node for the
        // unit's class, else an argument that an expansion contributes (it is
        // not rewritten again), else the first argument met.
        let mut rep: HashMap<Cfg::G, Cfg::G> = HashMap::new();
        if let (Some(u), Some(uc)) = (unit, unit_class) {
            rep.insert(uc, u);
        }
        for (_, v) in expand.values() {
            for &a in v {
                rep.entry(self.eg.find_const(a)).or_insert(a);
            }
        }
        for &a in vx.iter().chain(&vy) {
            rep.entry(self.eg.find_const(a)).or_insert(a);
        }
        // The kernel's side: each first-level argument replaced by its target
        // (an expansion or its class's member) and flattened again.
        let contributed: HashSet<Cfg::G> = expand
            .values()
            .flat_map(|(_, v)| v.iter().copied())
            .collect();
        let target = |a: Cfg::G| -> Cfg::G {
            let c = self.eg.find_const(a);
            match expand.get(&c) {
                Some((n, _)) if !contributed.contains(&a) => *n,
                _ => rep[&c],
            }
        };
        let side = |v: &[Cfg::G]| -> Vec<usize> {
            let mut out: Vec<usize> = Vec::new();
            for &a in v {
                let t = target(a);
                match expand.get(&self.eg.find_const(a)) {
                    Some((n, args)) if *n == t => {
                        out.extend(args.iter().map(|g| g.to_usize()));
                    }
                    _ => out.push(t.to_usize()),
                }
            }
            if let Some(u) = unit {
                out.retain(|r| *r != u.to_usize());
            }
            match kind {
                LeanKind::Ac => out.sort_unstable(),
                LeanKind::Aci => {
                    out.sort_unstable();
                    out.dedup();
                }
                _ => {}
            }
            out
        };
        if side(&vx) != side(&vy) {
            return self.miss("arguments differ modulo the kernel's laws");
        }
        let mut atoms: Vec<Cfg::G> = vx.iter().chain(&vy).copied().collect();
        atoms.sort_unstable_by_key(|a| a.to_usize());
        atoms.dedup();
        let mut prems = Vec::new();
        for a in atoms {
            let t = target(a);
            if a != t {
                let p = self.prove(a, t)?;
                prems.push(p);
            }
        }
        let (nx, ny) = (self.node(x), self.node(y));
        let f = self.eg.ops.info(op).name.clone();
        let mut s = format!("cong {f} {nx} {ny}");
        for p in prems {
            let _ = write!(s, " {p}");
        }
        Some(self.step(s))
    }

    /// The certificate node of a term as written.
    fn client_node(&mut self, t: &ClientTerm<Cfg::G>) -> Option<usize> {
        Some(match t {
            ClientTerm::Node(g) => {
                if g.to_usize() >= self.eg.len() {
                    return None;
                }
                self.node(*g)
            }
            ClientTerm::Lit(v) => {
                self.add_node((format!("#lit {v}"), Vec::new()), format!("l {v}"))
            }
            ClientTerm::App(f, kids) => {
                let mut ids = Vec::with_capacity(kids.len());
                for k in kids {
                    ids.push(self.client_node(k)?);
                }
                let mut line = format!("a {f}");
                for c in &ids {
                    let _ = write!(line, " {c}");
                }
                self.add_node((f.clone(), ids), line)
            }
        })
    }

    /// The arguments certificate node `c` flattens to under `f`.
    fn cview(&self, f: &str, c: usize, out: &mut Vec<usize>) {
        match &self.table[c] {
            (Some(g), kids) if g == f && !kids.is_empty() => {
                for &k in kids {
                    self.cview(f, k, out);
                }
            }
            _ => out.push(c),
        }
    }

    /// A step proving certificate nodes `c1 = c2` by congruence alone (no
    /// forest edge): `Some(None)` when they are the same node.
    fn link(&mut self, c1: usize, c2: usize) -> Option<Option<usize>> {
        if c1 == c2 {
            return Some(None);
        }
        let (o1, k1) = self.table[c1].clone();
        let (o2, k2) = self.table[c2].clone();
        let f = o1.clone().or(o2.clone())?;
        let (kind, unit) = self
            .kinds
            .get(&f)
            .copied()
            .unwrap_or((LeanKind::Plain, None));
        let mut prems = Vec::new();
        match kind {
            LeanKind::Plain | LeanKind::Comm => {
                if o1.as_deref() != Some(&f) || o2.as_deref() != Some(&f) || k1.len() != k2.len() {
                    return None;
                }
                let mut order = k2.clone();
                if kind == LeanKind::Comm && k1.len() == 2 && k1[0] == k2[1] && k1[1] == k2[0] {
                    order.swap(0, 1);
                }
                for (a, b) in k1.iter().zip(&order) {
                    if let Some(p) = self.link(*a, *b)? {
                        prems.push(p);
                    }
                }
            }
            _ => {
                let norm = |w: &Self, c: usize| -> Vec<usize> {
                    let mut v = Vec::new();
                    w.cview(&f, c, &mut v);
                    v.retain(|a| Some(*a) != unit);
                    match kind {
                        LeanKind::Ac => v.sort_unstable(),
                        LeanKind::Aci => {
                            v.sort_unstable();
                            v.dedup();
                        }
                        _ => {}
                    }
                    v
                };
                if norm(self, c1) != norm(self, c2) {
                    return None;
                }
            }
        }
        let mut s = format!("cong {f} {c1} {c2}");
        for p in prems {
            let _ = write!(s, " {p}");
        }
        Some(Some(self.step(s)))
    }

    /// Joins optional steps proving `x0 = x1`, `x1 = x2`, ... by `trans`.
    fn chain(&mut self, parts: &[Option<usize>], refl_node: usize) -> usize {
        let mut acc: Option<usize> = None;
        for p in parts.iter().flatten() {
            acc = Some(match acc {
                None => *p,
                Some(a) => self.step(format!("trans {a} {p}")),
            });
        }
        acc.unwrap_or_else(|| self.step(format!("refl {refl_node}")))
    }

    /// A step proving the written term `t` (built as node `g`) equal to
    /// `g`'s node, or the reverse.
    fn written(
        &mut self,
        t: &Option<ClientTerm<Cfg::G>>,
        g: Cfg::G,
    ) -> Option<(usize, Option<usize>)> {
        let ng = self.node(g);
        let Some(t) = t else {
            return Some((ng, None));
        };
        let Some(c) = self.client_node(t) else {
            return self.miss("term not spelled").map(|_| (ng, None));
        };
        match self.link(c, ng) {
            Some(s) => Some((c, s)),
            None => self
                .miss("written term differs from its node")
                .map(|_| (ng, None)),
        }
    }
}

impl<Cfg: EGraphConfig, L: LitVal, const TRACK: bool, const PROOFS: bool>
    EGraph<Cfg, L, TRACK, PROOFS>
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
    Cfg::Policy: crate::config::StorePolicy<Cfg, TRACK>,
{
    /// Proves, into `st`, each `check-eq` of `inp.goals` not proved yet. A
    /// caller about to discard nodes (a lazy check's transaction) calls it
    /// first, then [`cert_forget`](Self::cert_forget). Requires `PROOFS`.
    pub fn cert_prove_goals(&self, st: &mut CertState<Cfg::G>, inp: &CertInputs<'_, Cfg::G>) {
        if !PROOFS {
            return;
        }
        let mut w = Writer {
            eg: self,
            st,
            unions: inp.unions,
            rule_spans: inp.rule_spans,
            globals: inp.globals,
        };
        for i in 0..self.ops.names().count() {
            let op: Cfg::O = crate::id::id_at(i);
            let kind = w.kind(op);
            let unit = self.unit_node(op).map(|u| w.node(u));
            w.kinds.insert(self.ops.info(op).name.clone(), (kind, unit));
        }
        while w.next_goal < inp.goals.len() {
            let i = w.next_goal;
            w.next_goal += 1;
            w.n_goals += 1;
            let g = &inp.goals[i];
            let Some(&off) = w.check_offsets.get(i) else {
                continue;
            };
            if g.a.to_usize() >= self.len() || g.b.to_usize() >= self.len() {
                *w.unsupported.entry("goal nodes discarded").or_default() += 1;
                continue;
            }
            let Some(s) = w.prove(g.a, g.b) else {
                continue;
            };
            let Some((ca, la)) = w.written(&g.lhs, g.a) else {
                continue;
            };
            let Some((_, lb)) = w.written(&g.rhs, g.b) else {
                continue;
            };
            let lb = lb.map(|s| w.step(format!("symm {s}")));
            let s = w.chain(&[la, Some(s), lb], ca);
            w.n_proved += 1;
            let _ = writeln!(w.lines, "g {off} {s}");
        }
    }

    /// Drops what `st` keyed by a node id at or above the current length,
    /// after a restore discarded those nodes (their ids may be reused).
    pub fn cert_forget(&self, st: &mut CertState<Cfg::G>) {
        let len = self.len();
        st.node_of.retain(|&id, _| id < len);
        st.proved
            .retain(|&(a, b), r| a < len && b < len && r.is_some());
        st.in_progress.clear();
    }

    /// Writes a certificate (`proofs/checker`, format `semper-cert 1`) proving
    /// `inp.goals[i]` for the `i`-th `check-eq` form of `inp.src`, with the
    /// axioms as the `union` forms of the source in order. Requires `PROOFS`.
    pub fn write_certificate<W: std::io::Write>(
        &self,
        inp: &CertInputs<'_, Cfg::G>,
        out: W,
    ) -> std::io::Result<CertStats> {
        if !PROOFS {
            return Err(std::io::Error::new(
                std::io::ErrorKind::InvalidInput,
                "a certificate requires an EGraph with PROOFS=true",
            ));
        }
        let mut st = CertState::new(inp.src);
        self.cert_prove_goals(&mut st, inp);
        st.finish(out)
    }
}
