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

} // verus!
