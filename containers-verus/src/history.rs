// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Shared branch history for hard-synced vectors (`doc/design/10-shared-fork-history.md`).
//!
//! `N` vectors that always `mark`/`restore` together share one `ForkHistory` and
//! one mark depth instead of each carrying an identical copy. `History` owns the
//! genealogy and depth; it is passed `&mut` to members per call and never stored
//! inside one, so there is no shared mutable aliasing for Verus. This module is
//! the extracted genealogy type (doc 10, step 1); the history-less `Vec` and the
//! `Solo`/`SyncGroup` wrappers build on it.

// Extracted genealogy type (doc 10, step 1); wired into `Vec`/`Solo`/`SyncGroup`
// in later steps, so its methods are not yet called.
#![allow(dead_code)]

use vstd::prelude::*;
use crate::fork_history::ForkHistory;
use crate::index_like::IndexLike;
use crate::diff_store::DiffStore;
use crate::vec::Vec as SpVec;

verus! {

/// A version token for a synced group: the branch live at mark time and the mark
/// depth. Drops `VecToken`'s per-vector `container_id` — one token names the
/// whole group's version, validated once by `History`.
#[derive(Clone, Copy)]
pub(crate) struct GroupToken {
    pub(crate) branch_id: u32,
    pub(crate) depth: u32,
}

/// The shared genealogy and mark depth for a synced group. One instance backs
/// all members, so the `ForkHistory` (which grows one origin per restore and is
/// never reclaimed) is held `×1` instead of `×N`.
pub(crate) struct History {
    pub(crate) forks: ForkHistory,
    pub(crate) depth: u32,
}

impl History {
    pub open(crate) spec fn wf(self) -> bool {
        self.forks.wf()
    }

    pub open(crate) spec fn depth_spec(self) -> nat {
        self.depth as nat
    }

    /// Validity of `t` against the live branch and depth — the shared analogue of
    /// `Vec::is_token_valid_spec`, minus the container check (one history, one
    /// group).
    pub open(crate) spec fn valid_spec(self, t: GroupToken) -> bool {
        crate::fork_history::fork_valid(self.forks.origins@,
            self.forks.current_branch_id as nat,
            self.depth as nat, t.branch_id as nat, t.depth as nat)
    }

    pub(crate) fn new() -> (r: History)
        ensures
            r.wf(),
            r.depth == 0,
            r.forks.origins@.len() == 0,
    {
        History { forks: ForkHistory::new(), depth: 0 }
    }

    pub(crate) fn depth(&self) -> (d: u32)
        ensures d == self.depth,
    {
        self.depth
    }

    /// Open a new mark: the token records the branch live now and the current
    /// depth, then depth advances by one. `O(1)`, no genealogy write — the one
    /// genealogy write per group operation happens at `restore`, not `mark`.
    pub(crate) fn mark(&mut self) -> (t: GroupToken)
        requires
            old(self).wf(),
            old(self).depth < u32::MAX,
        ensures
            final(self).wf(),
            final(self).depth == old(self).depth + 1,
            final(self).forks == old(self).forks,
            t.depth == old(self).depth,
            t.branch_id == old(self).forks.current_branch_id,
    {
        let t = GroupToken { branch_id: self.forks.current_branch(), depth: self.depth };
        self.depth = self.depth + 1;
        t
    }

    /// Is `t` valid against the live branch and depth? Computed once for the
    /// whole group (versus `N` identical walks today).
    pub(crate) fn is_valid(&self, t: GroupToken) -> (r: bool)
        requires self.wf(),
        ensures r == self.valid_spec(t),
    {
        self.forks.is_valid(t.branch_id, t.depth, self.depth)
    }

    /// Restore to `t`: record the branch cut in the genealogy and set the depth
    /// to the token's. The single genealogy write per group restore (versus `N`).
    pub(crate) fn restore_to(&mut self, t: GroupToken)
        requires
            old(self).wf(),
            old(self).valid_spec(t),
            t.depth < old(self).depth,
            old(self).forks.origins@.len() + 1 <= u32::MAX,
        ensures
            final(self).wf(),
            final(self).depth == t.depth,
    {
        proof {
            // Validity ⇒ `t.branch` is reachable from the current branch ⇒ it is
            // a real branch id (`<= origins.len()`), which discharges `fork`'s
            // precondition. Same chain `Vec::restore` uses.
            crate::fork_history::lemma_fork_valid_characterization(
                self.forks.origins@, self.forks.current_branch_id as nat,
                self.depth as nat, t.branch_id as nat, t.depth as nat);
            assert(crate::fork_history::reaches(self.forks.origins@,
                self.forks.current_branch_id as nat, t.branch_id as nat));
            crate::fork_history::lemma_reaches_in_range(
                self.forks.origins@, self.forks.current_branch_id as nat,
                t.branch_id as nat);
        }
        self.forks.fork(t.branch_id, t.depth);
        self.depth = t.depth;
    }
}

/// One `Vec` bundled with its own `History`: reproduces the standalone
/// `mark`/`restore` API through the shared-history primitives (the migration
/// safety net of doc 10). A `SyncGroup` is the same shape with one `History`
/// over many members; `Solo` is the `N == 1` case and the proof that
/// `push_frame`/`restore_frame` + `History` compose to the old semantics.
pub(crate) struct Solo<T, I, S, const TRACK: bool>
where
    T: Sized + Copy,
    I: IndexLike,
    S: DiffStore<T, I, TRACK>,
{
    pub(crate) vec: SpVec<T, I, S, TRACK>,
    pub(crate) history: History,
}

impl<T, I, S, const TRACK: bool> Solo<T, I, S, TRACK>
where
    T: Sized + Copy,
    I: IndexLike,
    S: DiffStore<T, I, TRACK>,
{
    /// The group invariant: the member's frame depth tracks the shared history's
    /// depth exactly. This is the `N == 1` case of `SyncGroup`'s invariant.
    pub open(crate) spec fn wf(self) -> bool {
        &&& self.vec.wf()
        &&& self.history.wf()
        &&& self.vec.depth_spec() == self.history.depth_spec()
    }

    pub open(crate) spec fn view(self) -> Seq<T> {
        self.vec.view()
    }

    /// Open a mark: one genealogy write in `History`, one frame push in the
    /// member. Depth advances in lockstep, so the group invariant is maintained.
    pub(crate) fn mark(&mut self, shrink: crate::vec::ShrinkPolicy) -> (t: GroupToken)
        requires
            old(self).wf(),
            TRACK,
            old(self).vec.depth_spec() < u32::MAX,
            old(self).vec.view().len() < I::max_nat(),
        ensures
            final(self).wf(),
            final(self).view() == old(self).view(),
            final(self).vec.depth_spec() == old(self).vec.depth_spec() + 1,
            t.depth == old(self).history.depth,
    {
        let t = self.history.mark();
        self.vec.push_frame(shrink);
        t
    }

    /// Restore to `t`: validate once in `History`, reconstruct the member via
    /// `restore_frame`, and record the branch cut in `History`. Depth drops to
    /// `t.depth` in both, so the group invariant is maintained.
    pub(crate) fn restore(&mut self, t: GroupToken)
        where T: core::default::Default
        requires
            old(self).wf(),
            TRACK,
            old(self).history.valid_spec(t),
            (t.depth as nat) < old(self).history.depth_spec(),
            old(self).history.forks.origins@.len() + 1 <= u32::MAX,
        ensures
            final(self).wf(),
            final(self).view() == old(self).vec.snapshots_view()[t.depth as int],
            final(self).vec.depth_spec() == t.depth as nat,
    {
        self.vec.restore_frame(t.depth as usize);
        self.history.restore_to(t);
    }
}

/// One `History` shared across two heterogeneous members — the smallest true
/// `SyncGroup`. The e-graph's hard-synced set (~10 members of different
/// `T`/`I`/`S`) is this shape with more fields: one `History`, many members, each
/// carrying only its own diff state while the branch genealogy (which grows one
/// origin per restore and is otherwise duplicated per member) lives once. The
/// fan-out generalizes field-by-field; the two-member case verifies the pattern.
pub(crate) struct SyncPair<T1, I1, S1, T2, I2, S2, const TRACK: bool>
where
    T1: Sized + Copy, I1: IndexLike, S1: DiffStore<T1, I1, TRACK>,
    T2: Sized + Copy, I2: IndexLike, S2: DiffStore<T2, I2, TRACK>,
{
    pub(crate) a: SpVec<T1, I1, S1, TRACK>,
    pub(crate) b: SpVec<T2, I2, S2, TRACK>,
    pub(crate) history: History,
}

impl<T1, I1, S1, T2, I2, S2, const TRACK: bool> SyncPair<T1, I1, S1, T2, I2, S2, TRACK>
where
    T1: Sized + Copy, I1: IndexLike, S1: DiffStore<T1, I1, TRACK>,
    T2: Sized + Copy, I2: IndexLike, S2: DiffStore<T2, I2, TRACK>,
{
    /// The group invariant: every member's frame depth equals the shared
    /// history's depth. This is the fact that lets one token name the whole
    /// group's version.
    pub open(crate) spec fn wf(self) -> bool {
        &&& self.a.wf()
        &&& self.b.wf()
        &&& self.history.wf()
        &&& self.a.depth_spec() == self.history.depth_spec()
        &&& self.b.depth_spec() == self.history.depth_spec()
    }

    /// One genealogy write, then a frame push in each member. All depths advance
    /// together, so the group invariant holds.
    pub(crate) fn mark(&mut self, shrink: crate::vec::ShrinkPolicy) -> (t: GroupToken)
        requires
            old(self).wf(),
            TRACK,
            old(self).a.depth_spec() < u32::MAX,
            old(self).a.view().len() < I1::max_nat(),
            old(self).b.view().len() < I2::max_nat(),
        ensures
            final(self).wf(),
            final(self).a.view() == old(self).a.view(),
            final(self).b.view() == old(self).b.view(),
            final(self).a.depth_spec() == old(self).a.depth_spec() + 1,
    {
        let t = self.history.mark();
        self.a.push_frame(shrink);
        self.b.push_frame(shrink);
        t
    }

    /// Validate once, reconstruct each member via `restore_frame`, record the
    /// branch cut once. All depths drop to `t.depth`, so the invariant holds.
    pub(crate) fn restore(&mut self, t: GroupToken)
        where T1: core::default::Default, T2: core::default::Default
        requires
            old(self).wf(),
            TRACK,
            old(self).history.valid_spec(t),
            (t.depth as nat) < old(self).history.depth_spec(),
            old(self).history.forks.origins@.len() + 1 <= u32::MAX,
        ensures
            final(self).wf(),
            final(self).a.view() == old(self).a.snapshots_view()[t.depth as int],
            final(self).b.view() == old(self).b.snapshots_view()[t.depth as int],
            final(self).a.depth_spec() == t.depth as nat,
    {
        self.a.restore_frame(t.depth as usize);
        self.b.restore_frame(t.depth as usize);
        self.history.restore_to(t);
    }
}

} // verus!
