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
//! An edge the writer cannot express (a rule application, cancellation, an
//! assumption, a law the kernel does not model) leaves its goal unproved; the
//! writer counts it by kind.

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

struct Writer<'a, Cfg: EGraphConfig, L: LitVal, const TRACK: bool, const PROOFS: bool>
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
    Cfg::Policy: crate::config::StorePolicy<Cfg, TRACK>,
{
    eg: &'a EGraph<Cfg, L, TRACK, PROOFS>,
    nodes: String,
    steps: String,
    n_nodes: usize,
    n_steps: usize,
    node_of: HashMap<usize, usize>,
    key_of: HashMap<(String, Vec<usize>), usize>,
    proved: HashMap<(usize, usize), Option<usize>>,
    in_progress: HashSet<(usize, usize)>,
    axiom_offsets: Vec<usize>,
    unions: &'a [CertGoal<Cfg::G>],
    /// Each certificate node: its operator (`None` for a literal) and children.
    table: Vec<(Option<String>, Vec<usize>)>,
    kinds: HashMap<String, (LeanKind, Option<usize>)>,
    unsupported: BTreeMap<&'static str, usize>,
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
            let v = v.to_string();
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
            Justification::Rewrite { .. } => self.miss("rewrite"),
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
    /// Writes a certificate (`proofs/checker`, format `semper-cert 1`) proving
    /// `goals[i]` for the `i`-th `check-eq` form of `src`, and the axioms as
    /// the `union` forms of `src` in order. Requires `PROOFS`.
    pub fn write_certificate<W: std::io::Write>(
        &self,
        src: &str,
        goals: &[CertGoal<Cfg::G>],
        unions: &[CertGoal<Cfg::G>],
        mut out: W,
    ) -> std::io::Result<CertStats> {
        if !PROOFS {
            return Err(std::io::Error::new(
                std::io::ErrorKind::InvalidInput,
                "a certificate requires an EGraph with PROOFS=true",
            ));
        }
        let check_offsets = form_offsets(src, "check-eq");
        let mut w = Writer {
            eg: self,
            nodes: String::new(),
            steps: String::new(),
            n_nodes: 0,
            n_steps: 0,
            node_of: HashMap::new(),
            key_of: HashMap::new(),
            proved: HashMap::new(),
            in_progress: HashSet::new(),
            axiom_offsets: form_offsets(src, "union"),
            unions,
            table: Vec::new(),
            kinds: HashMap::new(),
            unsupported: BTreeMap::new(),
        };
        for i in 0..self.ops.names().count() {
            let op: Cfg::O = crate::id::id_at(i);
            let kind = w.kind(op);
            let unit = self.unit_node(op).map(|u| w.node(u));
            w.kinds.insert(self.ops.info(op).name.clone(), (kind, unit));
        }
        let mut lines = String::new();
        let mut stats = CertStats {
            goals: goals.len(),
            ..CertStats::default()
        };
        for (i, g) in goals.iter().enumerate() {
            let Some(&off) = check_offsets.get(i) else {
                break;
            };
            // A lazy check's transaction discards the nodes it built.
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
            stats.proved += 1;
            let _ = writeln!(lines, "g {off} {s}");
        }
        writeln!(out, "semper-cert 1")?;
        out.write_all(w.nodes.as_bytes())?;
        out.write_all(w.steps.as_bytes())?;
        out.write_all(lines.as_bytes())?;
        stats.nodes = w.n_nodes;
        stats.steps = w.n_steps;
        stats.unsupported = w.unsupported;
        Ok(stats)
    }
}
