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

use crate::diff_store::DiffStore;
use crate::index_like::IndexLike;
use crate::vec::Vec as SpVec;
use vstd::prelude::*;

verus! {

/// A version token for a synced group: the identity of the `History` that
/// minted it (its provenance), the generation stamp minted at mark time and the
/// mark depth. One token names the whole group's version, validated once by
/// the history that minted it: a token presented to any other history is
/// foreign and refused, whatever its numbers.
#[derive(Clone, Copy, Debug)]
pub struct GroupToken {
    pub(crate) history: crate::container_id::ContainerId,
    pub(crate) generation: u64,
    pub(crate) depth: u32,
}

impl GroupToken {
    /// The mark depth this token names (public spec accessor; the raw fields stay
    /// crate-private so a token cannot be forged field-by-field outside).
    pub open(crate) spec fn depth_spec(&self) -> nat {
        self.depth as nat
    }

    /// The same quantity under its container-side name: for a standalone
    /// container the depth of the mark IS the index of the frame it opened.
    pub open(crate) spec fn frame_idx_spec(self) -> nat {
        self.depth as nat
    }

    /// The minting manager's identity (spec accessor; the field is `pub(crate)`).
    pub open(crate) spec fn history_spec(self) -> nat {
        self.history.id()
    }

    /// Exec twin of `depth_spec`: the consumer restores every member to this
    /// depth after validating the token against the group's `History`.
    pub fn depth(&self) -> (d: u32)
        ensures d as nat == self.depth_spec(),
    {
        self.depth
    }
}

/// The shared depth-indexed generation stamps and mark depth for a synced group.
/// One instance backs all members, so the fork history is held `×1` instead of
/// `×N` — and, unlike the old append-only `origins` (which grew one entry per
/// restore, never reclaimed, O(R)), the stamp array is O(max depth): the leak fix
/// (doc 10). A token minted at depth `d` carries `stamps.mint_at(d)`, a fresh
/// stamp from a counter that only grows; a restore to `d` cuts the live length
/// to `d` (`GenStamps::cut_from`), one write that invalidates the consumed
/// token and the abandoned future together.
/// What a manager mints tokens from: its identity and the per-depth generation
/// stamps. The group `History` wraps one together with the group depth; a
/// standalone container embeds one and uses its own frame count as the depth,
/// so it is a group of one with the same token, the same validation (minting
/// manager, generation, liveness) and the same cut on restore.
pub struct Genealogy {
    /// The minting manager's identity: every token carries it, and validation
    /// refuses a token minted elsewhere.
    pub(crate) id: crate::container_id::ContainerId,
    pub(crate) stamps: crate::gen_stamps::GenStamps,
}

impl Genealogy {
    /// The minting manager's identity (spec accessor; the field is `pub(crate)`).
    pub open(crate) spec fn id_spec(&self) -> nat {
        self.id.id()
    }

    /// Number of stamp levels held (spec accessor).
    /// Live stamp depths (`GenStamps::live_len`): the depths a token can be
    /// valid at.
    pub open(crate) spec fn levels_len(&self) -> nat {
        self.stamps.live_len()
    }

    /// The next stamp this manager will hand out; every stamp it ever handed
    /// out is below it.
    pub open(crate) spec fn next_spec(&self) -> u64 {
        self.stamps.next_spec()
    }

    /// `t` was minted here and its generation is still the live stamp at its
    /// depth (O(1)).
    pub open(crate) spec fn valid_spec(self, t: GroupToken) -> bool {
        &&& t.history.id() == self.id.id()
        &&& self.stamps.valid(t.depth as nat, t.generation)
    }

    pub fn new() -> (r: Genealogy)
        ensures r.levels_len() == 0,
    {
        Genealogy {
            id: crate::container_id::ContainerId::new(),
            stamps: crate::gen_stamps::GenStamps::new(),
        }
    }

    /// Mint the token naming the frame at `depth` (growing the stamp array the
    /// first time a depth is reached). The token is immediately valid, and
    /// every token that was valid stays valid (existing stamps are untouched).
    pub(crate) fn mint(&mut self, depth: usize) -> (t: GroupToken)
        requires depth < u32::MAX,
        ensures
            t.depth_spec() == depth as nat,
            t.history_spec() == old(self).id_spec(),
            final(self).id_spec() == old(self).id_spec(),
            final(self).valid_spec(t),
            forall|u: GroupToken| old(self).valid_spec(u) ==> final(self).valid_spec(u),
            final(self).levels_len() == depth as nat + 1,
            // Freshness: the minted stamp is new, so every token this manager
            // handed out before (its stamp is below the old counter) keeps its
            // validity status — a consumed token stays consumed.
            t.generation >= old(self).next_spec(),
            final(self).next_spec() > t.generation,
            forall|u: GroupToken| u.generation < old(self).next_spec()
                ==> final(self).valid_spec(u) == old(self).valid_spec(u),
    {
        let g = self.stamps.mint_at(depth);
        GroupToken { history: self.id, generation: g, depth: depth as u32 }
    }

    pub fn is_valid(&self, t: &GroupToken) -> (b: bool)
        ensures b == self.valid_spec(*t),
    {
        self.id.eq(t.history) && self.stamps.is_valid(t.depth as usize, t.generation)
    }

    /// The cut of a restore: every token at `depth` or deeper that is valid now
    /// is dead for good (its stamp changes; stamps never return), tokens above
    /// the cut are untouched.
    /// The cut: every token at or above `depth` is dead for good (the live
    /// length drops to `depth`), tokens below keep their status, the counter
    /// is untouched. One write, whatever the deepest depth ever reached.
    pub fn cut_from(&mut self, depth: usize)
        ensures
            final(self).id_spec() == old(self).id_spec(),
            final(self).next_spec() == old(self).next_spec(),
            final(self).levels_len() == if depth < old(self).levels_len() { depth as nat } else { old(self).levels_len() },
            forall|u: GroupToken| u.depth_spec() >= depth as nat ==> !final(self).valid_spec(u),
            forall|u: GroupToken| u.depth_spec() < depth as nat
                ==> final(self).valid_spec(u) == old(self).valid_spec(u),
    {
        self.stamps.cut_from(depth);
    }
}

/// The group manager: a `Genealogy` plus the group depth.
pub struct History {
    pub(crate) genealogy: Genealogy,
    pub(crate) depth: u32,
}

impl History {
    /// Every live depth has a stamp level (so a live token's depth is in range).
    pub open(crate) spec fn wf(self) -> bool {
        self.genealogy.levels_len() >= self.depth as nat
    }

    pub open(crate) spec fn depth_spec(self) -> nat {
        self.depth as nat
    }

    /// Validity of `t`: its generation still matches the live stamp at its depth
    /// (O(1)). The shared analogue of `Vec::is_token_valid_spec`, minus the
    /// container check (one history, one group).
    pub open(crate) spec fn valid_spec(self, t: GroupToken) -> bool {
        self.genealogy.valid_spec(t)
    }

    pub fn new() -> (r: History)
        ensures
            r.wf(),
            r.depth_spec() == 0,
    {
        History { genealogy: Genealogy::new(), depth: 0 }
    }

    pub fn depth(&self) -> (d: u32)
        ensures d as nat == self.depth_spec(),
    {
        self.depth
    }

    /// Open a new mark: mint the generation for the current depth (growing the
    /// stamp array the first time a depth is reached), then depth advances by one.
    /// The token is immediately valid.
    pub fn mark(&mut self) -> (t: GroupToken)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).depth_spec() == old(self).depth_spec() + 1,
            t.depth_spec() == old(self).depth_spec(),
            final(self).valid_spec(t),
    {
        // Total: the depth ceiling is the group's documented trap, not a
        // caller obligation (the marks the engine takes are bounded by its
        // own frame budget long before).
        if !(self.depth < u32::MAX) {
            crate::guard::refuse("History::mark: frame depth at u32 ceiling");
        }
        let d = self.depth;
        let t = self.genealogy.mint(d as usize);
        self.depth = d + 1;
        t
    }

    /// Is `t` valid — does its generation still match the live stamp at its depth?
    /// Computed once for the whole group (versus `N` identical walks today), O(1).
    pub fn is_valid(&self, t: GroupToken) -> (r: bool)
        requires self.wf(),
        ensures r == self.valid_spec(t),
    {
        self.genealogy.is_valid(&t)
    }

    /// Restore to `t`: cut the genealogy at `t.depth` (the consumed token and
    /// every token minted after it die for good; `t`'s ancestors stay valid)
    /// and set the depth to the token's. One write, no per-restore growth, no
    /// overflow precondition: the stamp counter only grows and refuses at its
    /// ceiling.
    pub fn restore_to(&mut self, t: GroupToken)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).depth_spec() == t.depth_spec(),
    {
        // Total: a stale or reused token, or one at or above the live depth,
        // is the documented trap (production's expect messages).
        if !self.is_valid(t) {
            crate::guard::refuse("History::restore_to: token is stale (its frame was cut)");
        }
        if !(t.depth < self.depth) {
            crate::guard::refuse("History::restore_to: token depth is not below the live depth");
        }
        // The cut starts AT the target depth: this restore removes frame
        // `t.depth` itself, so the token that named it is consumed for good
        // (a later mark at that depth mints a fresh generation) and every
        // deeper token is the abandoned future. Bumping from `t.depth + 1`
        // would let the consumed token alias the next frame at its depth.
        self.genealogy.cut_from(t.depth as usize);
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

// Byte reporter — OUTSIDE the verified perimeter (stratified; see
// `diagnostics.rs`).
impl History {
    /// Heap bytes of the generation-stamp array (read-only).
    pub fn heap_bytes(&self) -> usize {
        crate::diagnostics::HeapBytes::heap_bytes(&self.genealogy.stamps)
    }
}

// Value equality on the whole token (minting manager, generation, depth):
// what tests compare. Outside `verus!` (trait impl on a verified struct; the
// verifier does not need it).
impl PartialEq for GroupToken {
    #[inline(always)]
    fn eq(&self, other: &Self) -> bool {
        self.history == other.history
            && self.generation == other.generation
            && self.depth == other.depth
    }
}
impl Eq for GroupToken {}
