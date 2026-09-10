// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! The two-stack diff log: a plain mutable top and a compressed read-only bottom
//! with an activate-on-mark compression API
//! (`doc/design/09-diff-stack-compression.md`).
//!
//! `TwoStackLog<T, I>` keeps the recent, still-mutable frames plain (`hot`, a
//! `DiffLog`) and the older, finalized frames compressed (`cold`, a
//! `CompressedStack`). Its **abstract view is the flat `Seq<(T, I)>`**
//! `cold@ ++ hot@` — the same diff sequence a single plain log would present — so
//! it is a drop-in history representation. `mark` opens a frame boundary and, if
//! the column's policy fires, flushes the cold hot-frames into the compressed
//! bottom (`flush_cold`): "when compression is activated on mark, the uncompressed
//! top frames are compressed into the compressed stack." The flush preserves the
//! flat view exactly, by the `CompressedStack` push bijection, so no diff is lost
//! or reordered across the boundary.

use vstd::prelude::*;
use crate::index_like::{IndexLike, IndexFromNat};
use crate::diff_log::DiffLog;
use crate::compressed_stack::CompressedStack;
use crate::compression_config::ColumnConfig;

verus! {

pub struct TwoStackLog<T, I> {
    /// Compressed, read-only bottom (older finalized frames).
    pub cold: CompressedStack<T, I>,
    /// Plain, mutable top (recent frames, including the active one).
    pub hot: DiffLog<T, I>,
    /// Start offset of each hot frame within `hot@`. `hot_starts[0] == 0`; the
    /// last frame is the active one, its diffs `hot@[hot_starts.last()..]`.
    pub hot_starts: Vec<usize>,
    pub config: ColumnConfig,
}

impl<T: IndexLike, I: IndexFromNat> View for TwoStackLog<T, I> {
    type V = Seq<(T, I)>;
    open spec fn view(&self) -> Seq<(T, I)> {
        self.cold@ + self.hot@
    }
}

impl<T: IndexLike, I: IndexFromNat> TwoStackLog<T, I> {
    pub open spec fn wf(&self) -> bool {
        &&& self.cold.wf()
        &&& self.hot.wf()
        // There is always at least the active frame; it opens at the hot front,
        // so the frames tile `hot@` in order.
        &&& self.hot_starts@.len() > 0
        &&& self.hot_starts@[0] == 0
        &&& forall|k: int| 0 <= k < self.hot_starts@.len() ==>
                (#[trigger] self.hot_starts@[k]) <= self.hot@.len()
        &&& forall|a: int, b: int| 0 <= a <= b < self.hot_starts@.len() ==>
                (#[trigger] self.hot_starts@[a]) <= (#[trigger] self.hot_starts@[b])
    }

    /// An empty two-stack log with the given column configuration. Seeds one
    /// (empty) active frame at offset 0, so `hot_starts` is never empty and its
    /// first element stays 0 (it is only ever extended at the end or rebased to
    /// 0 by a flush).
    pub fn new(config: ColumnConfig) -> (r: TwoStackLog<T, I>)
        ensures r.wf(), r@ == Seq::<(T, I)>::empty(),
    {
        let mut hot_starts: Vec<usize> = Vec::new();
        hot_starts.push(0);
        let r = TwoStackLog {
            cold: CompressedStack::new(),
            hot: DiffLog::new_plain(),
            hot_starts,
            config,
        };
        assert(r@ =~= Seq::<(T, I)>::empty());
        assert(r.hot_starts@[0] == 0);
        r
    }

    /// Total entries across both stacks (the flat view length).
    pub open spec fn len_spec(&self) -> nat {
        self@.len()
    }

    /// Append one diff to the active (top) frame.
    pub fn push(&mut self, t: T, idx: I)
        requires old(self).wf(),
        ensures final(self).wf(), final(self)@ == old(self)@.push((t, idx)),
    {
        self.hot.push(t, idx);
        assert(self@ =~= old(self)@.push((t, idx)));
        assert forall|k: int| 0 <= k < self.hot_starts@.len() implies
            (#[trigger] self.hot_starts@[k]) <= self.hot@.len() by {
            assert(self.hot_starts@[k] <= old(self).hot@.len());
        }
    }

    /// Number of hot (uncompressed) frames.
    pub fn num_hot_frames(&self) -> (n: usize)
        ensures n == self.hot_starts@.len(),
    {
        self.hot_starts.len()
    }

    /// Number of compressed frames.
    pub fn num_cold_frames(&self) -> (n: usize)
        ensures n == self.cold.frames@.len(),
    {
        self.cold.num_frames()
    }

    /// Open a new frame boundary at the current hot top (a `mark`). The just
    /// active frame closes; a fresh empty active frame opens.
    pub fn open_frame(&mut self)
        requires old(self).wf(),
        ensures final(self).wf(), final(self)@ == old(self)@,
    {
        let n = self.hot.len();
        self.hot_starts.push(n);
        assert(self@ =~= old(self)@);
        assert(self.hot_starts@[self.hot_starts@.len() - 1] == n as int);
        assert(self.hot_starts@[0] == old(self).hot_starts@[0]);
        assert forall|a: int, b: int| 0 <= a <= b < self.hot_starts@.len() implies
            (#[trigger] self.hot_starts@[a]) <= (#[trigger] self.hot_starts@[b]) by {
            if b < old(self).hot_starts@.len() {
                assert(self.hot_starts@[a] == old(self).hot_starts@[a]);
                assert(self.hot_starts@[b] == old(self).hot_starts@[b]);
            } else {
                // b is the new last element (== hot.len()); a is old or new.
                if a < old(self).hot_starts@.len() {
                    assert(self.hot_starts@[a] == old(self).hot_starts@[a]);
                    assert(self.hot_starts@[a] <= old(self).hot@.len());
                }
            }
        }
    }

    /// Compress the first `k` hot frames into the cold bottom and drop them from
    /// the hot top. `k` must leave at least the active frame hot. The flat view
    /// is unchanged: the `k` compressed frames' decodes tile exactly the hot
    /// prefix that is dropped.
    pub fn flush_cold(&mut self, k: usize)
        requires
            old(self).wf(),
            k < old(self).hot_starts@.len(),
        ensures
            final(self).wf(),
            final(self)@ == old(self)@,
    {
        let ghost hot0 = self.hot@;
        let ghost cold0 = self.cold@;
        let ghost starts0 = self.hot_starts@;
        // Properties of the immutable ghosts, from the entry wf; hoisted so they
        // remain available in the rebuild loop and the final wf proof.
        assert(starts0[0] == 0);
        assert(forall|j: int| 0 <= j < starts0.len() ==> #[trigger] starts0[j] <= hot0.len());
        assert(forall|a: int, b: int| 0 <= a <= b < starts0.len() ==>
            #[trigger] starts0[a] <= #[trigger] starts0[b]);
        let mut f: usize = 0;
        while f < k
            invariant
                k < self.hot_starts@.len(),
                self.hot@ == hot0,
                self.hot_starts@ == starts0,
                self.hot.wf(),
                starts0[0] == 0,
                forall|j: int| 0 <= j < starts0.len() ==> #[trigger] starts0[j] <= hot0.len(),
                forall|a: int, b: int| 0 <= a <= b < starts0.len() ==>
                    #[trigger] starts0[a] <= #[trigger] starts0[b],
                0 <= f <= k,
                self.cold.wf(),
                // Processed frames tile the hot prefix `[0, starts0[f])`.
                self.cold@ == cold0 + hot0.subrange(0, starts0[f as int] as int),
            decreases k - f,
        {
            let lo = self.hot_starts[f];
            let hi = self.hot_starts[f + 1];
            assert(lo <= hi <= hot0.len());
            let diffs = self.hot.subrange_vec(lo, hi);
            self.cold.push_frame(&diffs, self.config.scheme);
            proof {
                // cold@ == cold0 + hot0[0..lo] + hot0[lo..hi] == cold0 + hot0[0..hi]
                assert(hot0.subrange(0, lo as int) + hot0.subrange(lo as int, hi as int)
                    =~= hot0.subrange(0, hi as int));
            }
            f += 1;
        }
        // After the loop, cold@ == cold0 + hot0[0 .. starts0[k]].
        let m = self.hot_starts[k];
        assert(self.hot_starts@ == starts0);
        assert(m == starts0[k as int]);
        assert(self.cold@ == cold0 + hot0.subrange(0, m as int));
        self.hot.drop_front(m);
        assert(self.hot@ =~= hot0.subrange(m as int, hot0.len() as int));

        // Rebuild hot_starts: keep frames [k, len), rebased by `m`.
        let ghost old_starts = self.hot_starts@;
        let mut new_starts: Vec<usize> = Vec::new();
        let slen = self.hot_starts.len();
        let mut i: usize = k;
        while i < slen
            invariant
                k <= i <= slen,
                k < starts0.len(),
                slen == self.hot_starts@.len(),
                self.hot_starts@ == old_starts,
                old_starts == starts0,
                m == starts0[k as int],
                forall|a: int, b: int| 0 <= a <= b < starts0.len() ==>
                    #[trigger] starts0[a] <= #[trigger] starts0[b],
                new_starts@.len() == i - k,
                forall|j: int| 0 <= j < i - k ==>
                    #[trigger] new_starts@[j] == (starts0[k + j] - m) as int,
            decreases slen - i,
        {
            let v = self.hot_starts[i];
            proof {
                assert(v == starts0[i as int]);
                assert(starts0[k as int] <= starts0[i as int]);
                assert(v >= m);
            }
            new_starts.push(v - m);
            i += 1;
        }
        self.hot_starts = new_starts;

        proof {
            // View preserved: (cold0 + hot0[0..m]) + hot0[m..] == cold0 + hot0.
            assert(hot0.subrange(0, m as int) + hot0.subrange(m as int, hot0.len() as int)
                =~= hot0);
            assert(self@ =~= old(self)@);
            // wf for the rebuilt hot_starts.
            assert(self.hot@.len() == hot0.len() - m);
            if self.hot_starts@.len() > 0 {
                assert(self.hot_starts@[0] == (starts0[k as int] - m) as int);
                assert(starts0[k as int] == m);
            }
            assert forall|j: int| 0 <= j < self.hot_starts@.len() implies
                (#[trigger] self.hot_starts@[j]) <= self.hot@.len() by {
                assert(self.hot_starts@[j] == (starts0[k + j] - m) as int);
                assert(starts0[k + j] <= hot0.len());
            }
            assert forall|a: int, b: int| 0 <= a <= b < self.hot_starts@.len() implies
                (#[trigger] self.hot_starts@[a]) <= (#[trigger] self.hot_starts@[b]) by {
                assert(self.hot_starts@[a] == (starts0[k + a] - m) as int);
                assert(self.hot_starts@[b] == (starts0[k + b] - m) as int);
                assert(starts0[k + a] <= starts0[k + b]);
            }
        }
    }

    /// `mark`: open a frame boundary, then activate compression per the column's
    /// policy — if the trigger fires, flush the cold hot-frames (all but the
    /// `keep_hot_frames` most recent) into the compressed bottom. `uncompressed`
    /// and `base` are the byte sizes the size-fraction trigger reads. The flat
    /// view is unchanged.
    pub fn mark(&mut self, uncompressed_bytes: usize, base_bytes: usize)
        requires old(self).wf(),
        ensures final(self).wf(), final(self)@ == old(self)@,
    {
        self.open_frame();
        if self.config.should_flush(uncompressed_bytes, base_bytes) {
            let nframes = self.hot_starts.len();
            let want = self.config.frames_to_compress(nframes);
            // Never flush the active (last) frame: keep k < nframes. wf gives
            // nframes >= 1, so nframes - 1 is safe.
            let k = if want < nframes { want } else { nframes - 1 };
            if k < nframes {
                self.flush_cold(k);
            }
        }
    }

    /// Restore within the hot region: truncate the plain top to `hot_n` entries,
    /// dropping the hot frames that started above it. The common near-backtrack,
    /// which the `keep_hot_frames` floor guarantees stays plain (no decode). The
    /// flat view becomes `cold@ ++ hot@[0..hot_n]`. Deeper backtracks into the
    /// compressed region first materialize the needed frames back to the top (a
    /// later addition; `CompressedStack::pop_frame` is the primitive).
    pub fn truncate_hot(&mut self, hot_n: usize)
        requires old(self).wf(), hot_n <= old(self).hot@.len(),
        ensures
            final(self).wf(),
            final(self)@ == old(self).cold@ + old(self).hot@.subrange(0, hot_n as int),
    {
        let ghost hot0 = self.hot@;
        let ghost starts0 = self.hot_starts@;
        self.hot.truncate(hot_n);
        assert(self.hot@ =~= hot0.subrange(0, hot_n as int));
        // Keep the sorted-prefix of frame starts that are <= hot_n. Frame 0's
        // start is 0 <= hot_n, so at least one frame survives.
        let mut c: usize = self.hot_starts.len();
        while c > 0 && self.hot_starts[c - 1] > hot_n
            invariant
                0 <= c <= self.hot_starts@.len(),
                self.hot_starts@ == starts0,
                starts0[0] == 0,
                forall|a: int, b: int| 0 <= a <= b < starts0.len() ==>
                    #[trigger] starts0[a] <= #[trigger] starts0[b],
                // everything at or above c is above hot_n.
                forall|j: int| c <= j < starts0.len() ==> #[trigger] starts0[j] > hot_n,
            decreases c,
        {
            c -= 1;
        }
        proof {
            // c >= 1: index 0 has start 0 <= hot_n, so the loop cannot drop it.
            if c == 0 {
                assert(starts0[0] > hot_n);
                assert(starts0[0] == 0);
            }
        }
        self.hot_starts.truncate(c);
        proof {
            assert(self@ =~= old(self).cold@ + hot0.subrange(0, hot_n as int));
            assert(self.hot_starts@[0] == 0);
            assert forall|j: int| 0 <= j < self.hot_starts@.len() implies
                (#[trigger] self.hot_starts@[j]) <= self.hot@.len() by {
                assert(self.hot_starts@[j] == starts0[j]);
                // j < c, so starts0[j] <= hot_n == new hot len (sorted, not > hot_n).
                assert(!(starts0[j] > hot_n));
            }
            assert forall|a: int, b: int| 0 <= a <= b < self.hot_starts@.len() implies
                (#[trigger] self.hot_starts@[a]) <= (#[trigger] self.hot_starts@[b]) by {
                assert(self.hot_starts@[a] == starts0[a]);
                assert(self.hot_starts@[b] == starts0[b]);
            }
        }
    }

    // -- monitoring --------------------------------------------------------

    /// Heap bytes held by the uncompressed (hot) top.
    pub fn hot_bytes(&self) -> usize {
        self.hot.heap_bytes()
    }

    /// Heap bytes held by the compressed (cold) bottom.
    pub fn cold_bytes(&self) -> usize {
        self.cold.heap_bytes()
    }
}

} // verus!
