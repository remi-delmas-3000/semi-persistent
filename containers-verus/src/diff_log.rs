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
use crate::diff_compress::{ValFrame, RunCol};

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

/// The index-major dual of `cold_vals`: concatenate each cold `RunCol` frame's
/// index projection (`idx_seq`). A `RunCol<(), I>` frame stores only run starts and
/// zero-size values, so its `idx_seq` is the whole reconstructed index sequence, and
/// the stored index column is dropped down to one `start` per run. Opaque so the
/// `Vec` wf check does not unfold the recursion.
#[verifier::opaque]
pub open spec fn cold_idxs<I: IndexLike>(cold: Seq<RunCol<(), I>>) -> Seq<I>
    decreases cold.len(),
{
    if cold.len() == 0 {
        Seq::empty()
    } else {
        cold[0].idx_seq() + cold_idxs(cold.subrange(1, cold.len() as int))
    }
}

/// Appending a cold frame extends the concatenation by exactly that frame's `idx_seq`.
pub proof fn lemma_cold_idxs_snoc<I: IndexLike>(cold: Seq<RunCol<(), I>>, f: RunCol<(), I>)
    ensures cold_idxs(cold.push(f)) == cold_idxs(cold) + f.idx_seq(),
    decreases cold.len(),
{
    reveal_with_fuel(cold_idxs, 2);
    if cold.len() == 0 {
        assert(cold.push(f) =~= seq![f]);
        assert(cold_idxs(cold) =~= Seq::<I>::empty());
        assert(cold_idxs(cold.push(f)) =~= f.idx_seq());
    } else {
        let tail = cold.subrange(1, cold.len() as int);
        lemma_cold_idxs_snoc(tail, f);
        assert(cold.push(f)[0] == cold[0]);
        assert(cold.push(f).subrange(1, cold.push(f).len() as int) =~= tail.push(f));
        let a = cold[0].idx_seq();
        let b = cold_idxs(tail);
        let c = f.idx_seq();
        assert(a + (b + c) =~= (a + b) + c);
    }
}

/// `cold_idxs(cold)[i]` is the index at offset `i - base` in frame `k` whose prefix
/// length is `base == cold_idxs(cold[0..k]).len()`. The random-access bridge `index`.
pub proof fn lemma_cold_idxs_at<I: IndexLike>(cold: Seq<RunCol<(), I>>, k: int, i: int)
    requires
        0 <= k < cold.len(),
        cold_idxs(cold.subrange(0, k)).len() <= i,
        i < cold_idxs(cold.subrange(0, k)).len() + cold[k].idx_seq().len(),
    ensures
        cold_idxs(cold)[i] == cold[k].idx_seq()[i - cold_idxs(cold.subrange(0, k)).len()],
    decreases cold.len(),
{
    reveal_with_fuel(cold_idxs, 2);
    let head = cold[0];
    let rest = cold.subrange(1, cold.len() as int);
    if k == 0 {
        assert(cold.subrange(0, 0) =~= Seq::<RunCol<(), I>>::empty());
        assert(i < head.idx_seq().len());
        assert(cold_idxs(cold) == head.idx_seq() + cold_idxs(rest));
        assert(cold_idxs(cold)[i] == head.idx_seq()[i]);
    } else {
        assert(cold.subrange(0, k).subrange(1, k) =~= rest.subrange(0, k - 1));
        assert(cold_idxs(cold.subrange(0, k))
            =~= head.idx_seq() + cold_idxs(rest.subrange(0, k - 1)));
        let base = cold_idxs(cold.subrange(0, k)).len();
        let hl = head.idx_seq().len();
        assert(base == hl + cold_idxs(rest.subrange(0, k - 1)).len());
        assert(i >= hl);
        lemma_cold_idxs_at(rest, k - 1, i - hl);
        assert(rest[k - 1] == cold[k]);
        lemma_cold_idxs_split(cold, k);
        assert(cold.subrange(k, cold.len() as int)[0] == cold[k]);
        assert(i < cold_idxs(cold).len());
        assert(cold_idxs(cold) == head.idx_seq() + cold_idxs(rest));
        assert(cold_idxs(cold)[i] == cold_idxs(rest)[i - hl]);
    }
}

/// The first `rem` indices of frame `k` are entries `[base, base+rem)` of the whole
/// concatenation, `base == cold_idxs(cold[0..k]).len()`. For the truncate partial case.
pub proof fn lemma_cold_idxs_at_prefix<I: IndexLike>(cold: Seq<RunCol<(), I>>, k: int, rem: int)
    requires
        0 <= k < cold.len(),
        0 <= rem <= cold[k].idx_seq().len(),
    ensures
        forall|t: int| 0 <= t < rem ==>
            cold_idxs(cold)[cold_idxs(cold.subrange(0, k)).len() + t] == cold[k].idx_seq()[t],
{
    let base = cold_idxs(cold.subrange(0, k)).len();
    assert forall|t: int| 0 <= t < rem implies
        cold_idxs(cold)[base + t] == cold[k].idx_seq()[t] by {
        lemma_cold_idxs_at(cold, k, base + t);
    }
}

/// `cold_idxs` splits at any frame boundary.
pub proof fn lemma_cold_idxs_split<I: IndexLike>(cold: Seq<RunCol<(), I>>, k: int)
    requires 0 <= k <= cold.len(),
    ensures
        cold_idxs(cold) == cold_idxs(cold.subrange(0, k))
            + cold_idxs(cold.subrange(k, cold.len() as int)),
    decreases cold.len(),
{
    reveal_with_fuel(cold_idxs, 2);
    if cold.len() == 0 {
        assert(cold.subrange(0, k) =~= Seq::<RunCol<(), I>>::empty());
        assert(cold.subrange(k, cold.len() as int) =~= Seq::<RunCol<(), I>>::empty());
        assert(cold_idxs(cold) =~= Seq::<I>::empty());
    } else if k == 0 {
        assert(cold.subrange(0, 0) =~= Seq::<RunCol<(), I>>::empty());
        assert(cold.subrange(0, cold.len() as int) =~= cold);
    } else {
        let head = cold[0];
        let rest = cold.subrange(1, cold.len() as int);
        lemma_cold_idxs_split(rest, k - 1);
        assert(cold.subrange(0, k).subrange(1, k) =~= rest.subrange(0, k - 1));
        assert(cold.subrange(0, k)[0] == head);
        assert(cold_idxs(cold.subrange(0, k))
            =~= head.idx_seq() + cold_idxs(rest.subrange(0, k - 1)));
        assert(cold.subrange(k, cold.len() as int) =~= rest.subrange(k - 1, rest.len() as int));
        let a = head.idx_seq();
        let b = cold_idxs(rest.subrange(0, k - 1));
        let c = cold_idxs(rest.subrange(k - 1, rest.len() as int));
        assert(a + (b + c) =~= (a + b) + c);
    }
}

/// The index column: plain (contiguous, kept whole), or index-major (immutable cold
/// `RunCol` frames that drop the stored index column to run starts + a hot tail).
pub enum DiffIdxs<I> {
    Plain(Vec<I>),
    Runs { cold: Vec<RunCol<(), I>>, tail: Vec<I> },
}

impl<I: IndexLike> DiffIdxs<I> {
    /// Number of indices.
    pub open spec fn len_spec(self) -> nat {
        match self {
            DiffIdxs::Plain(v) => v@.len(),
            DiffIdxs::Runs { cold, tail } => cold_idxs(cold@).len() + tail@.len(),
        }
    }

    /// The index at position `i`: cold-frame reconstruct below the tail, direct in it.
    pub open spec fn idx_at(self, i: int) -> I {
        match self {
            DiffIdxs::Plain(v) => v@[i],
            DiffIdxs::Runs { cold, tail } =>
                if i < cold_idxs(cold@).len() {
                    cold_idxs(cold@)[i]
                } else {
                    tail@[i - cold_idxs(cold@).len()]
                },
        }
    }

    /// Every cold frame is well-formed (its ghost pairs match its runs by `as_nat`).
    pub open spec fn wf(self) -> bool {
        match self {
            DiffIdxs::Plain(_) => true,
            DiffIdxs::Runs { cold, .. } =>
                forall|k: int| 0 <= k < cold@.len() ==> (#[trigger] cold@[k]).wf(),
        }
    }

    /// Whether this is the run-compressed variant (for variant-preservation ensures).
    pub open spec fn is_runs(self) -> bool {
        self is Runs
    }
}

impl<I: IndexLike> DiffIdxs<I> {
    /// The index at position `i`. Plain: direct read. Runs: reconstruct from the cold
    /// frame containing `i` (walk frames by cached length), or the hot tail. Mirrors
    /// the value cold walk in `DiffVals`/`DiffLog::index`.
    pub fn idx_at_exec(&self, i: usize) -> (r: I)
        requires self.wf(), i < self.len_spec(),
        ensures r == self.idx_at(i as int),
    {
        match self {
            DiffIdxs::Plain(v) => v[i],
            DiffIdxs::Runs { cold, tail } => {
                proof { reveal(cold_idxs); }
                // Walk cold frames carrying the within-frame offset `d == i - prefix_k`,
                // stopping at the frame that contains `i` or when cold is exhausted
                // (then `i` is in the hot tail). No total length is computed.
                let mut d: usize = i;
                let mut k: usize = 0;
                while k < cold.len() && cold[k].entry_len() <= d
                    invariant
                        0 <= k <= cold@.len(),
                        self.wf(),
                        forall|kk: int| 0 <= kk < cold@.len() ==> (#[trigger] cold@[kk]).wf(),
                        i == d + cold_idxs(cold@.subrange(0, k as int)).len(),
                        i < self.len_spec(),
                    decreases cold@.len() - k,
                {
                    let flen = cold[k].entry_len();
                    proof {
                        assert(flen == cold@[k as int].idx_seq().len());
                        assert(cold@.subrange(0, k + 1)
                            =~= cold@.subrange(0, k as int).push(cold@[k as int]));
                        lemma_cold_idxs_snoc(cold@.subrange(0, k as int), cold@[k as int]);
                        assert(cold_idxs(cold@.subrange(0, (k + 1) as int)).len()
                            == cold_idxs(cold@.subrange(0, k as int)).len() + flen);
                    }
                    d = d - flen;
                    k = k + 1;
                }
                if k < cold.len() {
                    // Frame k contains i: prefix_k <= i < prefix_k + len_k.
                    proof {
                        lemma_cold_idxs_split(cold@, (k + 1) as int);
                        assert(cold@.subrange(0, k + 1)
                            =~= cold@.subrange(0, k as int).push(cold@[k as int]));
                        lemma_cold_idxs_snoc(cold@.subrange(0, k as int), cold@[k as int]);
                        // i < cold_idxs(cold@).len(), so idx_at reads the cold concatenation.
                        assert(i < cold_idxs(cold@).len());
                        lemma_cold_idxs_at(cold@, k as int, i as int);
                    }
                    cold[k].idx_at(d)
                } else {
                    // Cold exhausted: prefix_k == cold_idxs(cold@).len(), so d == i - it.
                    proof {
                        assert(cold@.subrange(0, k as int) =~= cold@);
                        // i >= cold_idxs(cold@).len(), idx_at reads tail@[i - that] == tail@[d].
                    }
                    tail[d]
                }
            }
        }
    }

    /// Append one index. Plain: push. Runs: push to the hot tail.
    pub fn push_idx(&mut self, idx: I)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self).len_spec() == old(self).len_spec() + 1,
            forall|j: int| 0 <= j < old(self).len_spec()
                ==> final(self).idx_at(j) == old(self).idx_at(j),
            final(self).idx_at(old(self).len_spec() as int) == idx,
            final(self).is_runs() == old(self).is_runs(),
    {
        match self {
            DiffIdxs::Plain(v) => {
                v.push(idx);
            }
            DiffIdxs::Runs { tail, .. } => {
                tail.push(idx);
            }
        }
    }
}

/// One diff log: an index column (plain or index-major) and a value column (plain or
/// value-major). Abstract view `Seq<(T, I)>`. At most one column compresses at a time
/// (value-major keeps indices plain; index-major keeps values plain), so `len` can
/// read whichever column is plain in O(1) without a cached length or a frame-sum walk.
pub struct DiffLog<T, I> {
    pub idxs: DiffIdxs<I>,
    pub vals: DiffVals<T>,
}

impl<T: Copy, I: IndexLike> View for DiffLog<T, I> {
    type V = Seq<(T, I)>;
    open spec fn view(&self) -> Seq<(T, I)> {
        Seq::new(self.idxs.len_spec(), |i: int| (self.vals.val_at(i), self.idxs.idx_at(i)))
    }
}

impl<T: Copy, I: IndexLike> DiffLog<T, I> {
    pub open spec fn wf(&self) -> bool {
        &&& self.vals.wf()
        &&& self.idxs.wf()
        &&& self.vals.len_spec() == self.idxs.len_spec()
        // At most one column compresses: index-major keeps values plain (so `len` can
        // read the plain value column when the index column is run-compressed).
        &&& (self.idxs is Runs ==> self.vals is Plain)
    }

    /// A fresh empty plain log (the `None` / SMT representation).
    pub fn new_plain() -> (r: DiffLog<T, I>)
        ensures r.wf(), r@ == Seq::<(T, I)>::empty(),
    {
        let r = DiffLog { idxs: DiffIdxs::Plain(Vec::new()), vals: DiffVals::Plain(Vec::new()) };
        assert(r@ =~= Seq::<(T, I)>::empty());
        r
    }

    /// A fresh empty value-major log (the `ValueDict` representation): no cold
    /// frames yet, empty hot tail. Index column stays plain.
    pub fn new_dict() -> (r: DiffLog<T, I>)
        ensures r.wf(), r@ == Seq::<(T, I)>::empty(),
    {
        let r = DiffLog {
            idxs: DiffIdxs::Plain(Vec::new()),
            vals: DiffVals::Dict { cold: Vec::new(), tail: Vec::new() },
        };
        proof { reveal(cold_vals); }
        assert(cold_vals(Seq::<ValFrame<T>>::empty()) =~= Seq::<T>::empty());
        assert(r@ =~= Seq::<(T, I)>::empty());
        r
    }

    /// A fresh empty index-major log (the `IndexRuns` representation): no cold index
    /// frames yet, empty hot index tail; value column stays plain.
    pub fn new_runs() -> (r: DiffLog<T, I>)
        ensures r.wf(), r@ == Seq::<(T, I)>::empty(),
    {
        let r = DiffLog {
            idxs: DiffIdxs::Runs { cold: Vec::new(), tail: Vec::new() },
            vals: DiffVals::Plain(Vec::new()),
        };
        proof { reveal(cold_idxs); }
        assert(cold_idxs(Seq::<RunCol<(), I>>::empty()) =~= Seq::<I>::empty());
        assert(r@ =~= Seq::<(T, I)>::empty());
        r
    }

    /// Number of entries. Reads whichever column is plain (at most one compresses).
    pub fn len(&self) -> (n: usize)
        requires self.wf(),
        ensures n == self@.len(),
    {
        match &self.idxs {
            DiffIdxs::Plain(v) => v.len(),
            DiffIdxs::Runs { .. } => match &self.vals {
                DiffVals::Plain(vv) => vv.len(),
                // Unreachable: wf gives idxs is Runs ==> vals is Plain.
                DiffVals::Dict { .. } => { assert(false); 0 }
            },
        }
    }

    /// Materialize the index column of entries `[lo, hi)` as an owned `Vec<I>` (the
    /// `.1` projection of `@[lo..hi]`). The A2 plumbing: the capture machinery needs
    /// only the active/restored frame's indices, so the caller materializes that
    /// range instead of borrowing a whole contiguous `idxs` slice. That lets a future
    /// index-major representation DROP the stored index column (reconstructing it from
    /// runs here) without changing the `DiffStore` capture interface. For the current
    /// (idxs-whole) representation it is a range copy.
    pub fn index_range(&self, lo: usize, hi: usize) -> (r: Vec<I>)
        requires self.wf(), lo <= hi <= self@.len(),
        ensures
            r@.len() == hi - lo,
            forall|k: int| 0 <= k < hi - lo ==> #[trigger] r@[k] == self@[lo + k].1,
    {
        let mut out: Vec<I> = Vec::new();
        let mut i: usize = lo;
        while i < hi
            invariant
                lo <= i <= hi, hi <= self@.len(), self.wf(),
                out@.len() == i - lo,
                forall|k: int| 0 <= k < i - lo ==> #[trigger] out@[k] == self@[lo + k].1,
            decreases hi - i,
        {
            out.push(self.index(i).1);
            i += 1;
        }
        out
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
        let ibytes = match &self.idxs {
            DiffIdxs::Plain(v) => v.capacity() * core::mem::size_of::<I>(),
            DiffIdxs::Runs { cold, tail } => {
                let mut b = tail.capacity() * core::mem::size_of::<I>();
                for f in cold.iter() {
                    b += f.byte_len();
                }
                b
            }
        };
        ibytes + vbytes
    }

    /// Entry `i` = `(value, index)`. Cold reads walk the frames to locate `i`
    /// (O(cold frames); a `starts` offset array would make it O(log), a noted
    /// follow-up); tail reads are O(1).
    pub fn index(&self, i: usize) -> (e: (T, I))
        requires self.wf(), i < self@.len(),
        ensures e == self@[i as int],
    {
        let idx = self.idxs.idx_at_exec(i);
        let total = self.len();
        match &self.vals {
            DiffVals::Plain(v) => (v[i], idx),
            DiffVals::Dict { cold, tail } => {
                let tl = tail.len();
                proof { reveal(cold_vals); }
                // wf: total == vals.len_spec() == cold_vals + tail, so tl <= total and
                // cold_len == cold_vals(cold@).len().
                assert(self.vals.len_spec() == total);
                let cold_len = total - tl;
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
        self.idxs.push_idx(idx);
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
        // Index-major fold: coalesce the hot index tail into one immutable cold
        // RunCol frame, dropping the stored index column to run starts. `idx_seq` of
        // the new frame is exactly the old tail, so `cold_idxs` grows by the tail.
        match &mut self.idxs {
            DiffIdxs::Plain(_) => {}
            DiffIdxs::Runs { cold, tail } => {
                let ghost cold0 = cold@;
                let ghost tail0 = tail@;
                // Build ((), idx) pairs from the tail for the value-free run encoder.
                let mut pairs: Vec<((), I)> = Vec::new();
                let mut j: usize = 0;
                while j < tail.len()
                    invariant
                        0 <= j <= tail@.len(),
                        pairs@.len() == j,
                        forall|k: int| 0 <= k < j ==> #[trigger] pairs@[k] == ((), tail@[k]),
                    decreases tail@.len() - j,
                {
                    pairs.push(((), tail[j]));
                    j += 1;
                }
                let f: RunCol<(), I> = RunCol::compress(&pairs);
                let ghost fg = f;
                proof {
                    // f.decode() == pairs@ == ((),tail0[.]) ⇒ f.idx_seq() == tail0.
                    assert(f.idx_seq() =~= tail0);
                    lemma_cold_idxs_snoc(cold0, fg);
                }
                cold.push(f);
                *tail = Vec::new();
                proof {
                    assert(cold@ =~= cold0.push(fg));
                    assert(cold_idxs(cold@) =~= cold_idxs(cold0) + tail0);
                }
            }
        }
        // Value-major fold: coalesce the hot value tail into one immutable cold frame.
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
        match &mut self.idxs {
            DiffIdxs::Plain(v) =>
                crate::parallel_store::shrink_vec_capacity(v, factor, headroom),
            DiffIdxs::Runs { tail, .. } =>
                crate::parallel_store::shrink_vec_capacity(tail, factor, headroom),
        }
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
        let len = self.len();
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
        self.idxs = DiffIdxs::Plain(new_idxs);
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
        let len = self.len();
        // Index side: Plain truncates in place; Runs mirrors the value partial-frame
        // logic (keep whole cold frames, decode the split frame's kept prefix).
        match &mut self.idxs {
            DiffIdxs::Plain(v) => {
                v.truncate(n);
            }
            DiffIdxs::Runs { cold, tail } => {
                proof { reveal(cold_idxs); }
                assert(cold_idxs(cold@).len() + tail@.len() == len);
                let cold_len = len - tail.len();
                assert(cold_len == cold_idxs(cold@).len());
                if n >= cold_len {
                    tail.truncate(n - cold_len);
                    proof { assert(cold_idxs(cold@).len() == cold_len); }
                } else {
                    let ghost cold_all = cold@;
                    let clen = cold.len();
                    let mut d: usize = n;
                    let mut k: usize = 0;
                    while cold[k].entry_len() <= d
                        invariant
                            0 <= k <= cold@.len(),
                            k < cold@.len(),
                            cold@.len() == clen,
                            cold@ == cold_all,
                            forall|kk: int| 0 <= kk < cold@.len() ==> (#[trigger] cold@[kk]).wf(),
                            n == d + cold_idxs(cold@.subrange(0, k as int)).len(),
                            n < cold_idxs(cold@).len(),
                        decreases cold@.len() - k,
                    {
                        let flen = cold[k].entry_len();
                        proof {
                            assert(flen == cold@[k as int].idx_seq().len());
                            assert(cold@.subrange(0, k + 1)
                                =~= cold@.subrange(0, k as int).push(cold@[k as int]));
                            lemma_cold_idxs_snoc(cold@.subrange(0, k as int), cold@[k as int]);
                            assert(cold_idxs(cold@.subrange(0, (k + 1) as int)).len()
                                == cold_idxs(cold@.subrange(0, k as int)).len() + flen);
                            assert(flen <= d);
                            assert(cold_idxs(cold@.subrange(0, (k + 1) as int)).len() <= n);
                            assert(cold@.subrange(0, cold@.len() as int) =~= cold@);
                            assert(k + 1 < cold@.len());
                        }
                        d = d - flen;
                        k = k + 1;
                    }
                    let ghost off = cold_idxs(cold_all.subrange(0, k as int)).len();
                    let mut new_tail: Vec<I> = Vec::new();
                    let mut j: usize = 0;
                    while j < d
                        invariant
                            0 <= j <= d,
                            k < cold_all.len(),
                            cold@ == cold_all,
                            forall|kk: int| 0 <= kk < cold@.len() ==> (#[trigger] cold@[kk]).wf(),
                            d <= cold_all[k as int].idx_seq().len(),
                            new_tail@.len() == j,
                            forall|t: int| 0 <= t < j ==>
                                #[trigger] new_tail@[t] == cold_all[k as int].idx_seq()[t],
                        decreases d - j,
                    {
                        new_tail.push(cold[k].idx_at(j));
                        j += 1;
                    }
                    cold.truncate(k);
                    *tail = new_tail;
                    proof {
                        assert(cold@ =~= cold_all.subrange(0, k as int));
                        lemma_cold_idxs_split(cold_all, k as int);
                        assert(cold_idxs(cold@).len() == off);
                        lemma_cold_idxs_at_prefix(cold_all, k as int, d as int);
                    }
                }
            }
        }
        // Value side: Plain truncates in place; Dict mirrors the same partial-frame
        // logic. At most one side is compressed (the other is a plain Vec truncate).
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
