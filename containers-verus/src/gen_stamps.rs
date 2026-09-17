// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Depth-indexed generation stamps: the O(max-depth) reclamation core for fork
//! history (`doc/design/10-shared-fork-history.md`, "Dense alternative").
//!
//! `ForkHistory.origins` grows one entry per restore and is never reclaimed, so
//! its size is O(R) (lifetime restore count) — an unbounded leak on SMT's
//! millions of backjumps, even in the shared copy. The fix is the trail-solver
//! level-stamp trick: keep one generation counter per depth, `levels[d]`. A token
//! minted at depth `d` carries `levels[d]` at mark time; a restore that diverges
//! at depth `d` bumps `levels[d..]`, so every token from the abandoned future
//! (`depth >= d`) fails the O(1) check `token.gen == levels[token.depth]` while
//! shallower tokens stay valid. Size is O(max depth), not O(R).
//!
//! This module is the standalone, verified stamp array; wiring it into
//! `ForkHistory` (replacing the append-only `origins` walk) is the follow-on that
//! actually bounds the live size.

use vstd::prelude::*;

verus! {

pub struct GenStamps {
    /// `levels[d]` is the live generation at depth `d`. Stamps start at 1 so 0 is
    /// a reserved "never minted / always invalid" sentinel.
    pub levels: Vec<u64>,
}

impl GenStamps {
    /// Validity: a token minted at `depth` with generation `g` is live iff `depth`
    /// is in range and its stamp still matches. O(1) — a single array read.
    pub open spec fn valid(&self, depth: nat, g: u64) -> bool {
        depth < self.levels@.len() && self.levels@[depth as int] == g
    }

    /// A fresh stamp array for depths `[0, max_depth)`, all at generation 1.
    pub fn new(max_depth: usize) -> (r: GenStamps)
        ensures
            r.levels@.len() == max_depth,
            forall|d: int| 0 <= d < max_depth ==> r.levels@[d] == 1,
    {
        let mut levels: Vec<u64> = Vec::new();
        let mut d: usize = 0;
        while d < max_depth
            invariant
                d <= max_depth,
                levels@.len() == d,
                forall|k: int| 0 <= k < d ==> levels@[k] == 1,
            decreases max_depth - d,
        {
            levels.push(1u64);
            d += 1;
        }
        GenStamps { levels }
    }

    pub fn depth_capacity(&self) -> (n: usize)
        ensures n == self.levels@.len(),
    {
        self.levels.len()
    }

    /// Extend by one depth level at generation 1 (a depth reached for the first
    /// time). The array grows only to the max depth ever marked — O(max depth),
    /// the bound that fixes the O(R) `origins` leak.
    pub fn push_level(&mut self)
        ensures
            final(self).levels@.len() == old(self).levels@.len() + 1,
            forall|d: int| 0 <= d < old(self).levels@.len()
                ==> final(self).levels@[d] == old(self).levels@[d],
            final(self).levels@[old(self).levels@.len() as int] == 1,
    {
        self.levels.push(1u64);
    }

    /// Mint: the current generation at `depth`, to store in a token.
    pub fn stamp(&self, depth: usize) -> (g: u64)
        ensures depth < self.levels@.len() ==> g == self.levels@[depth as int],
    {
        // Total: an unreached depth is the documented trap.
        if !(depth < self.levels.len()) {
            crate::guard::refuse("GenStamps::stamp: depth has no stamp yet");
        }
        self.levels[depth]
    }

    /// Fork-history mint: the generation for a mark at frame depth `depth`,
    /// growing the array by one level the first time a depth is reached. The
    /// returned generation is immediately valid; older levels are preserved. This
    /// is the "mark" side of the reclaimed fork history (`cut` = `bump_from` is
    /// the "restore" side); `GenStamps` IS the fork history, no wrapper needed.
    pub fn stamp_at(&mut self, depth: usize) -> (g: u64)
        ensures
            final(self).levels@.len() >= old(self).levels@.len(),
            depth < final(self).levels@.len(),
            forall|d: int| 0 <= d < old(self).levels@.len()
                ==> final(self).levels@[d] == old(self).levels@[d],
            g == final(self).levels@[depth as int],
            final(self).valid(depth as nat, g),
    {
        // Total: the depth ceiling is the documented trap.
        if !(depth < usize::MAX) {
            crate::guard::refuse("GenStamps::stamp_at: depth at the usize ceiling");
        }
        // Grow to cover `depth` (a depth reached for the first time may be beyond
        // the current array, e.g. after a member used the genealogy-free
        // `push_frame` without minting through this array).
        while self.levels.len() <= depth
            invariant
                depth < usize::MAX,
                forall|d: int| 0 <= d < old(self).levels@.len()
                    ==> self.levels@[d] == old(self).levels@[d],
                self.levels@.len() >= old(self).levels@.len(),
            decreases depth as int + 1 - self.levels@.len(),
        {
            self.push_level();
        }
        self.stamp(depth)
    }

    /// Heap bytes of the stamp array (diagnostic; no spec content). O(max depth).
    #[verifier::external_body]
    pub fn heap_bytes(&self) -> usize {
        self.levels.capacity() * core::mem::size_of::<u64>()
    }

    /// The O(1) validity check for a token `(depth, g)`.
    pub fn is_valid(&self, depth: usize, g: u64) -> (b: bool)
        ensures b == self.valid(depth as nat, g),
    {
        if depth < self.levels.len() {
            self.levels[depth] == g
        } else {
            false
        }
    }

    /// A restore diverging at `depth` abandons every future at depth `>= depth`:
    /// bump `levels[depth..]` so their tokens no longer match, while
    /// `levels[0..depth]` (the surviving spine) is untouched. Uses `wrapping_add`,
    /// which ALWAYS changes a value: `(x + 1) % 2^64 != x` for every `u64`, wrap
    /// included, PROVED below by the two-case split (no wrap: the successor
    /// differs; wrap: zero differs from `u64::MAX`). No overflow precondition
    /// threads through the container hierarchy. The only residue of wrap is ABA
    /// after 2^64 restores at ONE depth (physically unreachable), and even then
    /// frame-liveness backstops it. Discharged from the trust ledger 2026-09:
    /// formerly `external_body` trusting wrapping semantics.
    pub fn bump_from(&mut self, depth: usize)
        ensures
            final(self).levels@.len() == old(self).levels@.len(),
            forall|d: int| 0 <= d < old(self).levels@.len() && d < depth
                ==> final(self).levels@[d] == old(self).levels@[d],
            forall|d: int| depth <= d < old(self).levels@.len()
                ==> final(self).levels@[d] != old(self).levels@[d],
    {
        let n = self.levels.len();
        let mut d: usize = depth;
        while d < n
            invariant
                depth <= d,
                // A depth past the stamp array is a legal no-op call.
                d <= n || depth >= n,
                n == self.levels@.len(),
                self.levels@.len() == old(self).levels@.len(),
                forall|k: int| 0 <= k < n && k < depth
                    ==> self.levels@[k] == old(self).levels@[k],
                forall|k: int| depth <= k < d
                    ==> #[trigger] self.levels@[k] != old(self).levels@[k],
                forall|k: int| d <= k < n
                    ==> #[trigger] self.levels@[k] == old(self).levels@[k],
            decreases n - d,
        {
            let v = self.levels[d];
            let bumped = v.wrapping_add(1);
            proof {
                // wrapping_add(1) always changes a u64: either the plain
                // successor (differs by one) or the wrap to zero (differs
                // from u64::MAX).
                if v == u64::MAX {
                    assert(bumped == 0);
                } else {
                    assert(bumped == v + 1);
                }
                assert(bumped != v);
            }
            self.levels.set(d, bumped);
            d += 1;
        }
    }
}

/// Invalidation corollary: after `bump_from(cut)`, a token minted below the cut
/// (`depth >= cut`) with its old stamp is no longer valid, while a token above
/// the cut (`depth < cut`) keeps its validity. This is the soundness of dropping
/// the abandoned future — exactly what `fork_valid` would reject, now O(1).
pub proof fn lemma_bump_invalidates(old_g: GenStamps, new_g: GenStamps, cut: nat)
    requires
        new_g.levels@.len() == old_g.levels@.len(),
        forall|d: int| 0 <= d < cut ==> new_g.levels@[d] == old_g.levels@[d],
        forall|d: int| cut <= d < new_g.levels@.len() ==>
            new_g.levels@[d] != old_g.levels@[d],
    ensures
        forall|depth: nat, g: u64|
            cut <= depth < old_g.levels@.len() && old_g.valid(depth, g)
                ==> !new_g.valid(depth, g),
        forall|depth: nat, g: u64|
            depth < cut ==> old_g.valid(depth, g) == new_g.valid(depth, g),
{
    assert forall|depth: nat, g: u64|
        cut <= depth < old_g.levels@.len() && old_g.valid(depth, g)
            implies !new_g.valid(depth, g) by {
        assert(new_g.levels@[depth as int] != old_g.levels@[depth as int]);
    }
    assert forall|depth: nat, g: u64| depth < cut implies
        old_g.valid(depth, g) == new_g.valid(depth, g) by {
        if depth < old_g.levels@.len() {
            assert(new_g.levels@[depth as int] == old_g.levels@[depth as int]);
        }
    }
}

} // verus!
