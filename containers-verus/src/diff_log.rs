// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! A semi-persistent vector's diff log with a runtime-selectable value
//! representation (`doc/design/09-diff-stack-compression.md`).
//!
//! `DiffLog<T, I>` stores the sequence of captured `(old_value, index)` diff
//! entries. Its **abstract view is `Seq<(T, I)>`** regardless of representation,
//! so `Vec`'s mark/restore proofs — which are stated over `diff_log@` — carry
//! unchanged when the concrete storage compresses. The index column is always a
//! contiguous `Vec<I>` (the capture-flag ops need an `&[I]` slice); the value
//! column is either stored plainly or value-major compressed, chosen per instance
//! at construction (`None` for SMT speed, `ValueDict` for the union-find value
//! columns under equality saturation).
//!
//! Value-major (`Dict`) is a two-tier value column: an ordered sequence of
//! IMMUTABLE per-frame `ValFrame`s (`dict` + narrow/bit-packed codes), the cold
//! tier, followed by a plain, still-growable hot `tail`. `push` appends to `tail`
//! in O(1); `compact_tail` (called at mark) folds the closed frame's tail values
//! into one new immutable cold frame in O(frame). Packed codes never need appending
//! because each cold frame is written once. The index column stays whole, so the
//! value compression is invisible to the capture machinery's `indices()` slice.

use vstd::prelude::*;
use crate::index_like::IndexLike;
use crate::diff_compress::ValFrame;

verus! {

/// The concatenated value sequence of the cold frames, in order (mirrors
/// `compressed_stack::decode_all` for the value-only frames). Opaque so the `Vec`
/// wf check (which reaches it through `DiffLog::wf`/`@`) does not unfold the
/// recursion; the lemmas below `reveal_with_fuel` it where they need its definition.
#[verifier::opaque]
pub open spec fn cold_vals<T: Copy>(cold: Seq<ValFrame<T>>) -> Seq<T>
    decreases cold.len(),
{
    if cold.len() == 0 {
        Seq::empty()
    } else {
        cold[0].decode() + cold_vals(cold.subrange(1, cold.len() as int))
    }
}

/// Appending a cold frame extends the concatenation by exactly that frame's decode.
pub proof fn lemma_cold_vals_snoc<T: Copy>(cold: Seq<ValFrame<T>>, f: ValFrame<T>)
    ensures cold_vals(cold.push(f)) == cold_vals(cold) + f.decode(),
    decreases cold.len(),
{
    reveal_with_fuel(cold_vals, 2);
    if cold.len() == 0 {
        assert(cold.push(f) =~= seq![f]);
        assert(cold_vals(cold) =~= Seq::<T>::empty());
        assert(cold_vals(cold.push(f)) =~= f.decode());
    } else {
        let tail = cold.subrange(1, cold.len() as int);
        lemma_cold_vals_snoc(tail, f);
        assert(cold.push(f)[0] == cold[0]);
        assert(cold.push(f).subrange(1, cold.push(f).len() as int) =~= tail.push(f));
        let a = cold[0].decode();
        let b = cold_vals(tail);
        let c = f.decode();
        assert(a + (b + c) =~= (a + b) + c);
    }
}

/// `cold_vals(cold)[i]` is the value at offset `i - base` in the frame `k` whose
/// prefix length is `base == cold_vals(cold[0..k]).len()`. The random-access bridge
/// `index()` needs to read one cold entry.
pub proof fn lemma_cold_vals_at<T: Copy>(cold: Seq<ValFrame<T>>, k: int, i: int)
    requires
        0 <= k < cold.len(),
        cold_vals(cold.subrange(0, k)).len() <= i,
        i < cold_vals(cold.subrange(0, k)).len() + cold[k].decode().len(),
    ensures
        cold_vals(cold)[i] == cold[k].decode()[i - cold_vals(cold.subrange(0, k)).len()],
    decreases cold.len(),
{
    reveal_with_fuel(cold_vals, 2);
    let head = cold[0];
    let rest = cold.subrange(1, cold.len() as int);
    if k == 0 {
        assert(cold.subrange(0, 0) =~= Seq::<ValFrame<T>>::empty());
        // i < head.decode().len() (from the requires), and cold_vals(cold)
        // == head.decode() + cold_vals(rest), so index i is in the head.
        assert(i < head.decode().len());
        assert(cold_vals(cold) == head.decode() + cold_vals(rest));
        assert(cold_vals(cold)[i] == head.decode()[i]);
    } else {
        // Strip the head; recurse on `rest`, `k-1`, `i - head.decode().len()`.
        assert(cold.subrange(0, k).subrange(1, k) =~= rest.subrange(0, k - 1));
        // cold_vals(cold[0..k]) == head.decode() + cold_vals(rest[0..k-1]).
        assert(cold_vals(cold.subrange(0, k))
            =~= head.decode() + cold_vals(rest.subrange(0, k - 1)));
        let base = cold_vals(cold.subrange(0, k)).len();
        let hl = head.decode().len();
        assert(base == hl + cold_vals(rest.subrange(0, k - 1)).len());
        assert(i >= hl);
        lemma_cold_vals_at(rest, k - 1, i - hl);
        assert(rest[k - 1] == cold[k]);
        // i is in range: i < base + cold[k].decode().len() <= cold_vals(cold).len().
        lemma_cold_vals_split(cold, k);
        assert(cold.subrange(k, cold.len() as int)[0] == cold[k]);
        assert(cold_vals(cold.subrange(k, cold.len() as int))
            == cold[k].decode() + cold_vals(cold.subrange(k, cold.len() as int).subrange(1, cold.subrange(k, cold.len() as int).len() as int)));
        assert(i < cold_vals(cold).len());
        assert(cold_vals(cold) == head.decode() + cold_vals(rest));
        assert(cold_vals(cold)[i] == cold_vals(rest)[i - hl]);
    }
}

/// The value column: plain, or value-major (immutable cold frames + hot tail).
pub enum DiffVals<T> {
    Plain(Vec<T>),
    Dict { cold: Vec<ValFrame<T>>, tail: Vec<T> },
}

impl<T: Copy> DiffVals<T> {
    /// Number of values.
    pub open spec fn len_spec(self) -> nat {
        match self {
            DiffVals::Plain(v) => v@.len(),
            DiffVals::Dict { cold, tail } => cold_vals(cold@).len() + tail@.len(),
        }
    }

    /// The value at position `i`: cold-frame decode below the tail, direct read in it.
    pub open spec fn val_at(self, i: int) -> T {
        match self {
            DiffVals::Plain(v) => v@[i],
            DiffVals::Dict { cold, tail } =>
                if i < cold_vals(cold@).len() {
                    cold_vals(cold@)[i]
                } else {
                    tail@[i - cold_vals(cold@).len()]
                },
        }
    }

    /// Every cold frame is well-formed (its codes index its dictionary).
    pub open spec fn wf(self) -> bool {
        match self {
            DiffVals::Plain(_) => true,
            DiffVals::Dict { cold, .. } =>
                forall|k: int| 0 <= k < cold@.len() ==> (#[trigger] cold@[k]).wf(),
        }
    }
}

/// One diff log: a contiguous index column and a plain-or-value-major value column.
/// Abstract view `Seq<(T, I)>`.
pub struct DiffLog<T, I> {
    pub idxs: Vec<I>,
    pub vals: DiffVals<T>,
}

impl<T: Copy, I: IndexLike> View for DiffLog<T, I> {
    type V = Seq<(T, I)>;
    open spec fn view(&self) -> Seq<(T, I)> {
        Seq::new(self.idxs@.len(), |i: int| (self.vals.val_at(i), self.idxs@[i]))
    }
}

impl<T: Copy, I: IndexLike> DiffLog<T, I> {
    pub open spec fn wf(&self) -> bool {
        &&& self.vals.wf()
        &&& self.vals.len_spec() == self.idxs@.len()
    }

    /// A fresh empty plain log (the `None` / SMT representation).
    pub fn new_plain() -> (r: DiffLog<T, I>)
        ensures r.wf(), r@ == Seq::<(T, I)>::empty(),
    {
        let r = DiffLog { idxs: Vec::new(), vals: DiffVals::Plain(Vec::new()) };
        assert(r@ =~= Seq::<(T, I)>::empty());
        r
    }

    /// A fresh empty value-major log (the `ValueDict` representation): no cold
    /// frames yet, empty hot tail.
    pub fn new_dict() -> (r: DiffLog<T, I>)
        ensures r.wf(), r@ == Seq::<(T, I)>::empty(),
    {
        let r = DiffLog { idxs: Vec::new(), vals: DiffVals::Dict { cold: Vec::new(), tail: Vec::new() } };
        proof { reveal(cold_vals); }
        assert(cold_vals(Seq::<ValFrame<T>>::empty()) =~= Seq::<T>::empty());
        assert(r@ =~= Seq::<(T, I)>::empty());
        r
    }

    /// Number of entries. `self@.len()` is `idxs@.len()` by the view definition.
    pub fn len(&self) -> (n: usize)
        ensures n == self@.len(),
    {
        self.idxs.len()
    }

    /// The index column as a slice — what the capture-flag ops consume. Contiguous
    /// and whole regardless of the value representation (value-major keeps `idxs`).
    pub fn indices(&self) -> (s: &[I])
        ensures s@ == self.idxs@,
    {
        self.idxs.as_slice()
    }

    /// Diagnostic heap footprint (capacity-based; no spec content).
    #[verifier::external_body]
    pub fn heap_bytes(&self) -> usize {
        let vbytes = match &self.vals {
            DiffVals::Plain(v) => v.capacity() * core::mem::size_of::<T>(),
            DiffVals::Dict { cold, tail } => {
                let mut b = tail.capacity() * core::mem::size_of::<T>();
                for f in cold.iter() {
                    b += f.byte_len();
                }
                b
            }
        };
        self.idxs.capacity() * core::mem::size_of::<I>() + vbytes
    }

    /// Entry `i` = `(value, index)`. Cold reads walk the frames to locate `i`
    /// (O(cold frames); a `starts` offset array would make it O(log), a noted
    /// follow-up); tail reads are O(1).
    pub fn index(&self, i: usize) -> (e: (T, I))
        requires self.wf(), i < self@.len(),
        ensures e == self@[i as int],
    {
        let idx = self.idxs[i];
        match &self.vals {
            DiffVals::Plain(v) => (v[i], idx),
            DiffVals::Dict { cold, tail } => {
                let tl = tail.len();
                proof { reveal(cold_vals); }
                // wf: idxs.len() == cold_vals + tail, so tl <= idxs.len() and
                // cold_len == cold_vals(cold@).len().
                assert(self.vals.len_spec() == self.idxs@.len());
                let cold_len = self.idxs.len() - tl;
                assert(cold_len == cold_vals(cold@).len());
                if i < cold_len {
                    // Walk frames, carrying the remaining within-cold offset `d`
                    // (subtraction only, so no overflow). `d == i - prefix_k`.
                    let clen = cold.len();
                    let mut d: usize = i;
                    let mut k: usize = 0;
                    while cold[k].len() <= d
                        invariant
                            0 <= k <= cold@.len(),
                            k < cold@.len(),
                            cold@.len() == clen,
                            self.wf(),
                            i == d + cold_vals(cold@.subrange(0, k as int)).len(),
                            i < cold_vals(cold@).len(),
                        decreases cold@.len() - k,
                    {
                        let flen = cold[k].len();
                        proof {
                            // flen == frame k's decoded length; prefix_{k+1} == prefix_k + flen.
                            assert(flen == cold@[k as int].decode().len());
                            assert(cold@.subrange(0, k + 1)
                                =~= cold@.subrange(0, k as int).push(cold@[k as int]));
                            lemma_cold_vals_snoc(cold@.subrange(0, k as int), cold@[k as int]);
                            assert(cold_vals(cold@.subrange(0, (k + 1) as int)).len()
                                == cold_vals(cold@.subrange(0, k as int)).len() + flen);
                            assert(flen <= d);
                            // prefix_{k+1} <= i < total, so k+1 is still a valid frame.
                            assert(cold_vals(cold@.subrange(0, (k + 1) as int)).len() <= i);
                            assert(cold@.subrange(0, cold@.len() as int) =~= cold@);
                            assert(k + 1 < cold@.len());
                        }
                        d = d - flen;
                        k = k + 1;
                    }
                    proof {
                        // prefix_k <= i < prefix_k + cold[k].decode().len(); index lemma.
                        lemma_cold_vals_at(cold@, k as int, i as int);
                    }
                    (cold[k].decode_at(d), idx)
                } else {
                    (tail[i - cold_len], idx)
                }
            }
        }
    }

    /// Append `(t, idx)`. Preserves the prefix, extends the view by one. Value-major
    /// appends to the hot tail (O(1); the dedup happens at `compact_tail`).
    pub fn push(&mut self, t: T, idx: I)
        requires old(self).wf(),
        ensures final(self).wf(), final(self)@ == old(self)@.push((t, idx)),
    {
        self.idxs.push(idx);
        match &mut self.vals {
            DiffVals::Plain(v) => v.push(t),
            DiffVals::Dict { tail, .. } => tail.push(t),
        }
        assert(self@ =~= old(self)@.push((t, idx)));
    }

    /// Fold the hot tail into one new immutable cold frame (value-major only;
    /// no-op for plain). Called at mark to finalize a frame. Preserves the view:
    /// the new cold frame decodes to exactly the old tail, so `cold_vals` grows by
    /// the tail and the tail empties. Amortized O(frame).
    pub fn compact_tail(&mut self)
        where T: IndexLike
        requires old(self).wf(),
        ensures final(self).wf(), final(self)@ == old(self)@,
    {
        match &mut self.vals {
            DiffVals::Plain(_) => {}
            DiffVals::Dict { cold, tail } => {
                let ghost cold0 = cold@;
                let ghost tail0 = tail@;
                let f = ValFrame::compress(tail);
                let ghost fg = f;
                proof { lemma_cold_vals_snoc(cold0, fg); }
                cold.push(f);
                *tail = Vec::new();
                proof {
                    assert(cold@ =~= cold0.push(fg));
                    // cold_vals(cold0.push(f)) == cold_vals(cold0) + f.decode()
                    //                          == cold_vals(cold0) + tail0.
                    assert(cold_vals(cold@) =~= cold_vals(cold0) + tail0);
                }
            }
        }
        assert(self@ =~= old(self)@);
    }

    /// Capacity-only shrink (production parity). Observably inert. Shrinks the
    /// mutable columns (idxs, plain values, hot tail); cold frames are already
    /// tightly sized by `compress`.
    pub fn shrink_capacity(&mut self, factor: usize, headroom: usize)
        requires old(self).wf(),
        ensures final(self).wf(), final(self)@ == old(self)@,
    {
        crate::parallel_store::shrink_vec_capacity(&mut self.idxs, factor, headroom);
        match &mut self.vals {
            DiffVals::Plain(v) =>
                crate::parallel_store::shrink_vec_capacity(v, factor, headroom),
            DiffVals::Dict { tail, .. } =>
                crate::parallel_store::shrink_vec_capacity(tail, factor, headroom),
        }
        assert(self@ =~= old(self)@);
    }

    /// Materialize entries `[lo, hi)` as a flat `Vec<(T, I)>`.
    pub fn subrange_vec(&self, lo: usize, hi: usize) -> (r: Vec<(T, I)>)
        requires self.wf(), lo <= hi <= self@.len(),
        ensures r@ == self@.subrange(lo as int, hi as int),
    {
        let mut out: Vec<(T, I)> = Vec::new();
        let mut i: usize = lo;
        while i < hi
            invariant
                lo <= i <= hi, hi <= self@.len(), self.wf(),
                out@.len() == i - lo,
                forall|k: int| 0 <= k < i - lo ==> out@[k] == self@[lo + k],
            decreases hi - i,
        {
            out.push(self.index(i));
            i += 1;
        }
        assert(out@ =~= self@.subrange(lo as int, hi as int));
        out
    }

    /// Drop the first `n` entries, keeping the suffix. Not called by `Vec` (only by
    /// the two-stack's plain hot log); for the value-major variant it rebuilds the
    /// suffix as a fresh plain tail (no cold frames), which is correct and only used
    /// off the `Vec` path. `final@ == old@[n..]`.
    pub fn drop_front(&mut self, n: usize)
        requires old(self).wf(), n <= old(self)@.len(),
        ensures final(self).wf(), final(self)@ == old(self)@.subrange(n as int, old(self)@.len() as int),
    {
        let len = self.idxs.len();
        let mut new_idxs: Vec<I> = Vec::new();
        let mut new_vals: Vec<T> = Vec::new();
        let mut i: usize = n;
        while i < len
            invariant
                n <= i <= len,
                len == self@.len(),
                self.wf(),
                new_idxs@.len() == i - n,
                new_vals@.len() == i - n,
                forall|k: int| 0 <= k < i - n ==> new_idxs@[k] == self@[n + k].1,
                forall|k: int| 0 <= k < i - n ==> new_vals@[k] == self@[n + k].0,
            decreases len - i,
        {
            let (v, idx) = self.index(i);
            new_vals.push(v);
            new_idxs.push(idx);
            i += 1;
        }
        self.idxs = new_idxs;
        self.vals = DiffVals::Plain(new_vals);
        assert(self@ =~= old(self)@.subrange(n as int, old(self)@.len() as int));
    }

    /// Truncate to `n` entries. Keeps whole cold frames up to `n`; a partial frame
    /// (when `n` falls inside a cold frame) is decoded into a fresh plain tail, and
    /// the hot tail is truncated when `n` is in it. Preserves the kept prefix's view.
    pub fn truncate(&mut self, n: usize)
        requires old(self).wf(), n <= old(self)@.len(),
        ensures final(self).wf(), final(self)@ == old(self)@.subrange(0, n as int),
    {
        let len = self.idxs.len();
        self.idxs.truncate(n);
        // idxs.truncate did not touch vals, so cold_vals + tail == len (from old wf),
        // giving tail.len() <= len and cold_len == cold_vals below.
        proof {
            assert(self.vals == old(self).vals);
            assert(old(self).vals.len_spec() == len as nat);
        }
        match &mut self.vals {
            DiffVals::Plain(v) => {
                v.truncate(n);
                assert(self@ =~= old(self)@.subrange(0, n as int));
            }
            DiffVals::Dict { cold, tail } => {
                proof { reveal(cold_vals); }
                let cold_len = len - tail.len();
                assert(cold_len == cold_vals(cold@).len());
                if n >= cold_len {
                    // `n` is in (or at the start of) the hot tail: keep all cold.
                    tail.truncate(n - cold_len);
                    proof {
                        assert(cold_vals(cold@).len() == cold_len);
                    }
                    assert(self@ =~= old(self)@.subrange(0, n as int));
                } else {
                    // `n` is within the cold region: walk to the frame containing
                    // `n`, keep whole frames before it, decode its kept prefix into a
                    // fresh plain tail, drop the rest. (Vec restores to a frame
                    // boundary, `rem == 0`, so the decode loop is usually empty; the
                    // mid-frame `rem > 0` path is correct but off the Vec path.)
                    let ghost cold_all = cold@;
                    let clen = cold.len();
                    // Carry the remaining offset `d` (subtraction only). `d == n - prefix_k`.
                    let mut d: usize = n;
                    let mut k: usize = 0;
                    while cold[k].len() <= d
                        invariant
                            0 <= k <= cold@.len(),
                            k < cold@.len(),
                            cold@.len() == clen,
                            cold@ == cold_all,
                            forall|kk: int| 0 <= kk < cold@.len() ==> (#[trigger] cold@[kk]).wf(),
                            n == d + cold_vals(cold@.subrange(0, k as int)).len(),
                            n < cold_vals(cold@).len(),
                        decreases cold@.len() - k,
                    {
                        let flen = cold[k].len();
                        proof {
                            assert(flen == cold@[k as int].decode().len());
                            assert(cold@.subrange(0, k + 1)
                                =~= cold@.subrange(0, k as int).push(cold@[k as int]));
                            lemma_cold_vals_snoc(cold@.subrange(0, k as int), cold@[k as int]);
                            assert(cold_vals(cold@.subrange(0, (k + 1) as int)).len()
                                == cold_vals(cold@.subrange(0, k as int)).len() + flen);
                            assert(flen <= d);
                            assert(cold_vals(cold@.subrange(0, (k + 1) as int)).len() <= n);
                            assert(cold@.subrange(0, cold@.len() as int) =~= cold@);
                            assert(k + 1 < cold@.len());
                        }
                        d = d - flen;
                        k = k + 1;
                    }
                    // `d == n - prefix_k == rem`; decode frame k's kept prefix [0, d).
                    let ghost off = cold_vals(cold_all.subrange(0, k as int)).len();
                    let mut new_tail: Vec<T> = Vec::new();
                    let mut j: usize = 0;
                    while j < d
                        invariant
                            0 <= j <= d,
                            k < cold_all.len(),
                            cold@ == cold_all,
                            forall|kk: int| 0 <= kk < cold@.len() ==> (#[trigger] cold@[kk]).wf(),
                            d <= cold_all[k as int].decode().len(),
                            new_tail@.len() == j,
                            forall|t: int| 0 <= t < j ==>
                                #[trigger] new_tail@[t] == cold_all[k as int].decode()[t],
                        decreases d - j,
                    {
                        new_tail.push(cold[k].decode_at(j));
                        j += 1;
                    }
                    // Keep frames [0, k) in place (no clone), set the decoded tail.
                    cold.truncate(k);
                    *tail = new_tail;
                    proof {
                        assert(cold@ =~= cold_all.subrange(0, k as int));
                        lemma_cold_vals_split(cold_all, k as int);
                        // cold_vals(cold@) is the length-`off` prefix of cold_vals(cold_all),
                        // and n == off + d.
                        assert(cold_vals(cold@).len() == off);
                        lemma_cold_vals_at_prefix(cold_all, k as int, d as int);
                    }
                    assert(self@ =~= old(self)@.subrange(0, n as int));
                }
            }
        }
    }
}

/// For the truncate partial-frame case: the first `rem` entries of frame `k`
/// (`cold[k].decode()[0..rem]`) are exactly entries `[base, base+rem)` of the whole
/// concatenation, where `base == cold_vals(cold[0..k]).len()`.
pub proof fn lemma_cold_vals_at_prefix<T: Copy>(cold: Seq<ValFrame<T>>, k: int, rem: int)
    requires
        0 <= k < cold.len(),
        0 <= rem <= cold[k].decode().len(),
    ensures
        forall|t: int| 0 <= t < rem ==>
            cold_vals(cold)[cold_vals(cold.subrange(0, k)).len() + t] == cold[k].decode()[t],
{
    let base = cold_vals(cold.subrange(0, k)).len();
    assert forall|t: int| 0 <= t < rem implies
        cold_vals(cold)[base + t] == cold[k].decode()[t] by {
        lemma_cold_vals_at(cold, k, base + t);
    }
}

/// `cold_vals` splits at any frame boundary: the concatenation of all frames is the
/// concatenation of the first `k` followed by the rest. Gives the prefix agreement
/// `cold_vals(cold[0..k])[i] == cold_vals(cold)[i]` for `i < cold_vals(cold[0..k]).len()`.
pub proof fn lemma_cold_vals_split<T: Copy>(cold: Seq<ValFrame<T>>, k: int)
    requires 0 <= k <= cold.len(),
    ensures
        cold_vals(cold) == cold_vals(cold.subrange(0, k))
            + cold_vals(cold.subrange(k, cold.len() as int)),
    decreases cold.len(),
{
    reveal_with_fuel(cold_vals, 2);
    if cold.len() == 0 {
        assert(cold.subrange(0, k) =~= Seq::<ValFrame<T>>::empty());
        assert(cold.subrange(k, cold.len() as int) =~= Seq::<ValFrame<T>>::empty());
        assert(cold_vals(cold) =~= Seq::<T>::empty());
    } else if k == 0 {
        assert(cold.subrange(0, 0) =~= Seq::<ValFrame<T>>::empty());
        assert(cold.subrange(0, cold.len() as int) =~= cold);
    } else {
        let head = cold[0];
        let rest = cold.subrange(1, cold.len() as int);
        lemma_cold_vals_split(rest, k - 1);
        assert(cold.subrange(0, k).subrange(1, k) =~= rest.subrange(0, k - 1));
        assert(cold.subrange(0, k)[0] == head);
        // cold_vals(cold[0..k]) == head.decode() + cold_vals(rest[0..k-1]).
        assert(cold_vals(cold.subrange(0, k))
            =~= head.decode() + cold_vals(rest.subrange(0, k - 1)));
        assert(cold.subrange(k, cold.len() as int) =~= rest.subrange(k - 1, rest.len() as int));
        let a = head.decode();
        let b = cold_vals(rest.subrange(0, k - 1));
        let c = cold_vals(rest.subrange(k - 1, rest.len() as int));
        assert(a + (b + c) =~= (a + b) + c);
    }
}

} // verus!
