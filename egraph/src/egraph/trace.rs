// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! The replay stream (`--trace`): one line per event, written when the event
//! happens, for the replayer of `proofs/checker` to check in order against its
//! own classes. `proofs/checker/REPLAY.md` specifies the lines and the checks.
//!
//! A line carries the witnesses the engine has in hand at the event and the
//! replayer could only find by search: the node a pattern application matched,
//! the nodes a right-hand side evaluated to, the class member a build spliced.
//! Nothing here reads the e-graph after the fact except a node's original
//! children, which proof mode never changes.

use super::*;
use std::fmt::Write as _;

/// One rule firing, buffered until its first merge: a firing that merges
/// nothing proves nothing, and most firings merge nothing.
struct Firing {
    /// The command's offset and whether it is a `rewrite`.
    src: (usize, bool),
    written: bool,
    /// The index, among the rule's merging actions, of the current one.
    action: usize,
    /// Rule index of the firing's first action within its command.
    base: usize,
}

#[derive(Default)]
pub struct Trace {
    /// Lines not yet written to `file`.
    out: String,
    file: Option<std::io::BufWriter<std::fs::File>>,
    /// Bytes written to `file`.
    bytes: u64,
    /// The offset of the `union` command about to merge.
    axiom_off: Option<usize>,
    /// The source of each rule, by rule id: the offset of its command, the
    /// index of its first rule within that command, and whether the command
    /// is a `rewrite` (its left side is matched) or a `rule` (both sides of
    /// its `union` actions are built).
    rule_src: Vec<Option<(usize, usize, bool)>>,
    firing: Option<Firing>,
    /// The open firing's `e` lines, unformatted: for each, its operator's
    /// index (`usize::MAX` for a literal), the matched node, the number of
    /// arguments, then the arguments. Formatting waits for the first merge;
    /// the buffer is reused across firings.
    atoms: Vec<usize>,
    /// Where, in `atoms`, the last line's argument count is.
    atom_at: usize,
    /// The nodes the open firing's current action's right-hand side evaluated
    /// to; `true` marks the node of a `let` name, which stands for the name's
    /// whole term.
    rhs: Vec<(usize, bool)>,
    /// The witnesses of the completion merge about to happen: its line's
    /// letter and the node ids after the merged pair.
    law: Option<(char, Vec<usize>)>,
    /// The offsets of the program's `union` and `check-eq` forms, in order.
    union_offsets: Vec<usize>,
    goal_offsets: Vec<usize>,
    n_unions: usize,
    n_goals: usize,
}

impl<Cfg: EGraphConfig, L: LitVal, const TRACK: bool, const PROOFS: bool>
    EGraph<Cfg, L, TRACK, PROOFS>
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
    Cfg::Policy: crate::config::StorePolicy<Cfg, TRACK>,
{
    /// Start the replay stream for the program `src`, written to `file`.
    pub fn trace_start(&mut self, src: &str, file: std::fs::File) {
        self.trace = Some(Box::new(Trace {
            file: Some(std::io::BufWriter::new(file)),
            union_offsets: cert::form_offsets(src, "union"),
            goal_offsets: cert::form_offsets(src, "check-eq"),
            ..Trace::default()
        }));
    }

    pub fn tracing(&self) -> bool {
        self.trace.is_some()
    }

    /// Write the buffered lines to the file; with `all`, whatever their
    /// size, and flush the file. Returns the bytes written so far.
    pub fn trace_flush(&mut self, all: bool) -> std::io::Result<u64> {
        use std::io::Write as _;
        let Some(t) = self.trace.as_mut() else {
            return Ok(0);
        };
        if (all || t.out.len() >= 1 << 20)
            && let Some(f) = t.file.as_mut()
        {
            f.write_all(t.out.as_bytes())?;
            t.bytes += t.out.len() as u64;
            t.out.clear();
            if all {
                f.flush()?;
            }
        }
        Ok(t.bytes)
    }

    /// `n` or `l`: node `id` was just created. Its children are the ones it
    /// was given: no re-canonization has touched it yet, so no history lookup
    /// is needed (proof mode's is a linear scan).
    pub(crate) fn trace_node(&mut self, id: Cfg::G) {
        let Some(mut t) = self.trace.take() else {
            return;
        };
        let i = id.to_usize();
        if let Some(v) = self.get_lit_val(id) {
            let srt = self.sort_name(self.node_sort(id));
            let _ = writeln!(t.out, "l {i} {srt} {}", cert::lit_spelling(v));
        } else {
            let _ = write!(t.out, "n {i} {}", self.node_op_name(id));
            let one = <Cfg::M as crate::multiplicity::MultiplicityLike>::ONE;
            self.for_each_child(id, |c, m| {
                let _ = write!(t.out, " {}", c.to_usize());
                if m != one {
                    let _ = write!(t.out, ":{m}");
                }
            });
            t.out.push('\n');
        }
        self.trace = Some(t);
    }

    /// `z`: node `unit` is the unit of `op`, written when the declaration
    /// registers it.
    pub(crate) fn trace_unit(&mut self, op: Cfg::O, unit: Cfg::G) {
        let name = self.ops.info(op).name.clone();
        if let Some(t) = self.trace.as_mut() {
            let _ = writeln!(t.out, "z {name} {}", unit.to_usize());
        }
    }

    /// `t`: the program term `op(kids)` evaluated to `id`.
    pub fn trace_term(&mut self, id: Cfg::G, op: Cfg::O, kids: &[(usize, String)]) {
        let Some(mut t) = self.trace.take() else {
            return;
        };
        let _ = write!(t.out, "t {} {}", id.to_usize(), self.ops.info(op).name);
        for (c, k) in kids {
            let _ = write!(t.out, " {c}{k}");
        }
        t.out.push('\n');
        self.trace = Some(t);
    }

    /// The next merge is the next `union` command's.
    pub fn trace_union(&mut self) {
        if let Some(t) = self.trace.as_mut() {
            t.axiom_off = t.union_offsets.get(t.n_unions).copied();
            t.n_unions += 1;
        }
    }

    /// `g`: the next `check-eq` compared `a` and `b`.
    pub fn trace_goal(&mut self, a: Cfg::G, b: Cfg::G) {
        let Some(mut t) = self.trace.take() else {
            return;
        };
        let off = t.goal_offsets.get(t.n_goals).copied();
        t.n_goals += 1;
        if let Some(off) = off {
            let _ = writeln!(t.out, "g {off} {} {}", a.to_usize(), b.to_usize());
        }
        self.trace = Some(t);
    }

    /// A `check-eq` that is not a goal of the stream (it failed, or the run
    /// stops on it): keeps the goal offsets aligned.
    pub fn trace_skip_goal(&mut self) {
        if let Some(t) = self.trace.as_mut() {
            t.n_goals += 1;
        }
    }

    /// Rule `rule` is rule `base` of the command at `off`, a `rewrite` or a
    /// `rule`.
    pub fn trace_rule_source(&mut self, rule: usize, off: usize, base: usize, rewrite: bool) {
        if let Some(t) = self.trace.as_mut() {
            if t.rule_src.len() <= rule {
                t.rule_src.resize(rule + 1, None);
            }
            t.rule_src[rule] = Some((off, base, rewrite));
        }
    }

    /// How many rules the stream already has from the command at `off`.
    pub fn trace_rules_at(&self, off: usize) -> usize {
        self.trace.as_ref().map_or(0, |t| {
            t.rule_src
                .iter()
                .flatten()
                .filter(|(o, _, _)| *o == off)
                .count()
        })
    }

    /// `r`: rule `rule` fires.
    pub(crate) fn trace_fire(&mut self, rule: usize) {
        if let Some(t) = self.trace.as_mut() {
            t.atoms.clear();
            t.rhs.clear();
            t.firing = t
                .rule_src
                .get(rule)
                .copied()
                .flatten()
                .map(|(off, base, rw)| Firing {
                    src: (off, rw),
                    written: false,
                    action: 0,
                    base,
                });
        }
    }

    /// `e`: within the firing, a pattern application of `op` (`None` for a
    /// literal) matched `node`; its arguments follow through
    /// [`trace_atom_arg`](Self::trace_atom_arg).
    #[inline]
    pub(crate) fn trace_atom(&mut self, node: Cfg::G, op: Option<Cfg::O>) {
        if let Some(t) = self.trace.as_mut()
            && t.firing.is_some()
        {
            t.atoms.push(op.map_or(usize::MAX, |o| o.to_usize()));
            t.atoms.push(node.to_usize());
            t.atoms.push(0);
            t.atom_at = t.atoms.len() - 1;
        }
    }

    /// The node the last `e` line's next argument pattern is bound to.
    #[inline]
    pub(crate) fn trace_atom_arg(&mut self, c: Cfg::G) {
        if let Some(t) = self.trace.as_mut()
            && t.firing.is_some()
        {
            t.atoms.push(c.to_usize());
            let at = t.atom_at;
            t.atoms[at] += 1;
        }
    }

    /// The firing has a part the stream cannot spell (a rest variable, a
    /// counted element): its merges are written as unchecked.
    pub(crate) fn trace_atom_opaque(&mut self) {
        if let Some(t) = self.trace.as_mut() {
            t.firing = None;
        }
    }

    /// Within the firing, a right-hand-side application evaluated to `id`.
    pub(crate) fn trace_rhs(&mut self, id: Cfg::G, global: bool) {
        if let Some(t) = self.trace.as_mut()
            && t.firing.is_some()
        {
            t.rhs.push((id.to_usize(), global));
        }
    }

    /// The firing's next action starts.
    pub(crate) fn trace_action(&mut self, merging: bool) {
        if let Some(t) = self.trace.as_mut()
            && let Some(f) = t.firing.as_mut()
        {
            t.rhs.clear();
            if merging {
                f.action += 1;
            }
        }
    }

    pub(crate) fn trace_fire_end(&mut self) {
        if let Some(t) = self.trace.as_mut() {
            t.firing = None;
        }
    }

    /// The line of the merge of `a` and `b` for the reason `just`.
    pub(crate) fn trace_merge(
        &mut self,
        a: Cfg::G,
        b: Cfg::G,
        just: Option<Justification<Cfg::G>>,
    ) {
        let Some(mut t) = self.trace.take() else {
            return;
        };
        let (x, y) = (a.to_usize(), b.to_usize());
        match just {
            Some(Justification::Axiom { .. }) => match t.axiom_off.take() {
                Some(off) => {
                    let _ = writeln!(t.out, "x {off} {x} {y}");
                }
                None => {
                    let _ = writeln!(t.out, "u axiom {x} {y}");
                }
            },
            Some(Justification::Congruence { .. }) => {
                let _ = writeln!(t.out, "c {x} {y}");
            }
            Some(j @ Justification::Build { node, .. }) => {
                let n = node.to_usize();
                let other = if n == x { y } else { x };
                if let Some(splices) = self.build_premises(j) {
                    for &(c, m) in splices {
                        let _ = writeln!(t.out, "s {} {}", c.to_usize(), m.to_usize());
                    }
                }
                let _ = writeln!(t.out, "w {n} {other}");
            }
            Some(Justification::Normalize { node, normal }) => {
                let _ = writeln!(t.out, "w {} {}", node.to_usize(), normal.to_usize());
            }
            Some(Justification::Rewrite { .. }) => match t.firing.take() {
                Some(mut f) => {
                    if !f.written {
                        let _ =
                            writeln!(t.out, "r {} {}", f.src.0, if f.src.1 { 'w' } else { 'r' });
                        let mut i = 0;
                        while i < t.atoms.len() {
                            let (op, node, k) = (t.atoms[i], t.atoms[i + 1], t.atoms[i + 2]);
                            let name = if op == usize::MAX {
                                "#lit"
                            } else {
                                self.ops.info(crate::id::id_at(op)).name.as_str()
                            };
                            let _ = write!(t.out, "e {node} {name}");
                            for j in i + 3..i + 3 + k {
                                let c = t.atoms[j];
                                let _ = write!(t.out, " {c}");
                            }
                            t.out.push('\n');
                            i += 3 + k;
                        }
                        f.written = true;
                    }
                    t.out.push('b');
                    for i in 0..t.rhs.len() {
                        let (r, global) = t.rhs[i];
                        let _ = write!(t.out, " {}{r}", if global { "g" } else { "" });
                    }
                    let j = f.base + f.action.saturating_sub(1);
                    let _ = writeln!(t.out, "\nm {j} {x} {y}");
                    t.firing = Some(f);
                }
                None => {
                    let _ = writeln!(t.out, "u rewrite {x} {y}");
                }
            },
            Some(
                Justification::ACInterReduction { .. }
                | Justification::InverseCancel { .. }
                | Justification::ACSuperposition { .. }
                | Justification::ACAxiomCP { .. }
                | Justification::Cancellative { .. },
            ) if t.law.is_some() => {
                let (kind, ids) = t.law.take().expect("checked by the guard");
                let _ = write!(t.out, "{kind} {x} {y}");
                for i in ids {
                    let _ = write!(t.out, " {i}");
                }
                t.out.push('\n');
            }
            Some(j) => {
                let kind = format!("{j:?}");
                let kind = kind.split([' ', '{', '(']).next().unwrap_or("?");
                let _ = writeln!(t.out, "u {kind} {x} {y}");
            }
            None => {
                let _ = writeln!(t.out, "u none {x} {y}");
            }
        }
        self.trace = Some(t);
        // An I/O error surfaces at the final flush.
        let _ = self.trace_flush(false);
    }

    /// A completion rule `l = r` as the stream names it: `l`, `r`, and 1 when
    /// `r`'s class is one argument of `l`'s operator (an atomic class: the
    /// rule's right side is the class itself), 0 when the right side is `r`'s
    /// own arguments (the class's minimal monomial, or the unit). The replayer
    /// cannot tell the two apart when `r` is an application of the operator.
    pub(crate) fn trace_rule(&self, (l, r): (Cfg::G, Cfg::G)) -> [Cfg::G; 3] {
        let flag = |b: bool| -> Cfg::G { crate::id::id_at(usize::from(b)) };
        if self.get_lit_val(l).is_some() || self.get_lit_val(r).is_some() {
            return [l, r, flag(true)];
        }
        let op = self.node_op(l);
        let root = self.classes.find_const(r);
        let unit = self
            .unit_node(op)
            .is_some_and(|u| self.classes.find_const(u) == root);
        let atomic = self
            .classes
            .repr_id(root)
            .is_some_and(|repr| self.classes.atomic(repr));
        [l, r, flag(!unit && (atomic || self.node_op(r) != op))]
    }

    /// The next merge is a completion merge with these witnesses: the line
    /// `kind a b ids..` replaces its `u` line. Cleared by
    /// [`trace_law_end`](Self::trace_law_end) when no merge took place.
    pub(crate) fn trace_law(&mut self, kind: char, ids: impl IntoIterator<Item = Cfg::G>) {
        if let Some(t) = self.trace.as_mut() {
            t.law = Some((kind, ids.into_iter().map(|g| g.to_usize()).collect()));
        }
    }

    pub(crate) fn trace_law_end(&mut self) {
        if let Some(t) = self.trace.as_mut() {
            t.law = None;
        }
    }

    /// `mark d`, `restore d`, `rpop d`: the engine's mark stack after the
    /// operation has depth `d`.
    pub(crate) fn trace_mark(&mut self, what: &str) {
        let depth = self.history.depth();
        if let Some(t) = self.trace.as_mut() {
            let _ = writeln!(t.out, "{what} {depth}");
            t.firing = None;
        }
    }
}
