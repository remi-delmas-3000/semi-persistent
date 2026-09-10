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
//! column is either stored plainly or dictionary-encoded, chosen per instance at
//! construction (`None` for SMT speed, `ValueDict` for the union-find value
//! columns under equality saturation). The dictionary uses `Eq` on `T` alone
//! (via `IndexLike::as_usize`), so it assumes no structure in `T`'s bits.

use vstd::prelude::*;
use crate::index_like::IndexLike;

verus! {

/// The value column: plain, or dictionary-encoded (`codes[t]` indexes `dict`).
pub enum DiffVals<T> {
    Plain(Vec<T>),
    Dict { dict: Vec<T>, codes: Vec<usize> },
}

impl<T> DiffVals<T> {
    /// Number of values.
    pub open spec fn len_spec(self) -> nat {
        match self {
            DiffVals::Plain(v) => v@.len(),
            DiffVals::Dict { codes, .. } => codes@.len(),
        }
    }

    /// The value at position `i`.
    pub open spec fn val_at(self, i: int) -> T {
        match self {
            DiffVals::Plain(v) => v@[i],
            DiffVals::Dict { dict, codes } => dict@[codes@[i] as int],
        }
    }

    /// Codes (if any) index the dictionary.
    pub open spec fn wf(self) -> bool {
        match self {
            DiffVals::Plain(_) => true,
            DiffVals::Dict { dict, codes } =>
                forall|t: int| 0 <= t < codes@.len() ==> (#[trigger] codes@[t]) < dict@.len(),
        }
    }
}

/// One diff log: a contiguous index column and a plain-or-dictionary value
/// column. Abstract view `Seq<(T, I)>`.
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

    /// A fresh empty dictionary log (the `ValueDict` representation).
    pub fn new_dict() -> (r: DiffLog<T, I>)
        ensures r.wf(), r@ == Seq::<(T, I)>::empty(),
    {
        let r = DiffLog { idxs: Vec::new(), vals: DiffVals::Dict { dict: Vec::new(), codes: Vec::new() } };
        assert(r@ =~= Seq::<(T, I)>::empty());
        r
    }

    /// Number of entries. `self@.len()` is `idxs@.len()` by construction, so no
    /// `wf` is needed.
    pub fn len(&self) -> (n: usize)
        ensures n == self@.len(),
    {
        self.idxs.len()
    }

    /// The index column as a slice — what the capture-flag ops (`prepare_mark`
    /// etc.) consume; they read only indices, so this stays contiguous and
    /// uncompressed regardless of the value representation.
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
            DiffVals::Dict { dict, codes } =>
                dict.capacity() * core::mem::size_of::<T>()
                    + codes.capacity() * core::mem::size_of::<usize>(),
        };
        self.idxs.capacity() * core::mem::size_of::<I>() + vbytes
    }

    /// Entry `i` = `(value, index)`.
    pub fn index(&self, i: usize) -> (e: (T, I))
        requires self.wf(), i < self@.len(),
        ensures e == self@[i as int],
    {
        let idx = self.idxs[i];
        match &self.vals {
            DiffVals::Plain(v) => (v[i], idx),
            DiffVals::Dict { dict, codes } => (dict[codes[i]], idx),
        }
    }

    /// Append `(t, idx)`. Preserves the prefix, extends the view by one.
    pub fn push(&mut self, t: T, idx: I)
        requires old(self).wf(),
        ensures final(self).wf(), final(self)@ == old(self)@.push((t, idx)),
    {
        self.idxs.push(idx);
        match &mut self.vals {
            DiffVals::Plain(v) => v.push(t),
            DiffVals::Dict { dict, codes } => {
                // Append without dedup: a fresh dictionary slot per entry, code
                // pointing at it. This keeps `push` free of any `T` equality
                // bound (so `DiffLog` is a drop-in diff log for every `Vec`
                // value type); `compact` (below, `T: IndexLike`) coalesces equal
                // values later for the value-dictionary win.
                let c = dict.len();
                dict.push(t);
                codes.push(c);
                proof {
                    assert(c < dict@.len());
                    assert(dict@[c as int] == t);
                }
            }
        }
        assert(self@ =~= old(self)@.push((t, idx)));
    }

    /// Capacity-only shrink of every backing vector (production parity: the
    /// diff log ratchets its allocation at mark time). Observably inert: each
    /// backing `@` is preserved by `shrink_vec_capacity`, so the view and `wf`
    /// are unchanged.
    pub fn shrink_capacity(&mut self, factor: usize, headroom: usize)
        requires old(self).wf(),
        ensures final(self).wf(), final(self)@ == old(self)@,
    {
        crate::parallel_store::shrink_vec_capacity(&mut self.idxs, factor, headroom);
        match &mut self.vals {
            DiffVals::Plain(v) =>
                crate::parallel_store::shrink_vec_capacity(v, factor, headroom),
            DiffVals::Dict { dict, codes } => {
                crate::parallel_store::shrink_vec_capacity(dict, factor, headroom);
                crate::parallel_store::shrink_vec_capacity(codes, factor, headroom);
            }
        }
        assert(self@ =~= old(self)@);
    }

    /// Rebuild the value column as a deduplicated dictionary, preserving the
    /// view. This is the value-dedup compression win (`ValueDict` mode): the
    /// union-find parent/rank columns store one dictionary slot per distinct
    /// value, not one per entry. `push` appends without dedup (any `T: Copy`),
    /// so `compact` is where equal values coalesce, hence the extra `IndexLike`
    /// bound (dictionary membership needs value equality via `as_usize`).
    pub fn compact(&mut self)
        where T: IndexLike
        requires old(self).wf(),
        ensures final(self).wf(), final(self)@ == old(self)@,
    {
        let mut dict: Vec<T> = Vec::new();
        let mut codes: Vec<usize> = Vec::new();
        let n = self.len();
        let mut i: usize = 0;
        while i < n
            invariant
                i <= n,
                n == self@.len(),
                self.wf(),
                codes@.len() == i,
                forall|t: int| 0 <= t < i ==> (#[trigger] codes@[t]) < dict@.len(),
                forall|t: int| 0 <= t < i ==> dict@[#[trigger] codes@[t] as int] == self@[t].0,
            decreases n - i,
        {
            let (v, _idx) = self.index(i);
            let code = match crate::diff_compress::dict_find(&dict, v) {
                Some(c) => c,
                None => {
                    let c = dict.len();
                    dict.push(v);
                    c
                }
            };
            codes.push(code);
            i += 1;
        }
        // `idxs` is untouched, so the index column is preserved; the new value
        // column reproduces every original value at the same position.
        self.vals = DiffVals::Dict { dict, codes };
        assert(self@ =~= old(self)@);
    }

    /// Materialize entries `[lo, hi)` as a flat `Vec<(T, I)>` — one hot frame's
    /// diffs, ready to hand to `compress_frame`.
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

    /// Drop the first `n` entries, keeping the suffix. This is how the two-stack
    /// removes cold frames from the plain top once they have been compressed into
    /// the bottom: the front `[0, n)` is the flushed prefix, the kept `[n, len)`
    /// is the still-hot suffix. Rebuilds the columns (front removal is not a
    /// truncate); `final@ == old@[n..]`.
    pub fn drop_front(&mut self, n: usize)
        requires old(self).wf(), n <= old(self)@.len(),
        ensures final(self).wf(), final(self)@ == old(self)@.subrange(n as int, old(self)@.len() as int),
    {
        let len = self.idxs.len();
        let mut new_idxs: Vec<I> = Vec::new();
        let mut i: usize = n;
        while i < len
            invariant
                n <= i <= len,
                len == self.idxs@.len(),
                new_idxs@.len() == i - n,
                forall|k: int| 0 <= k < i - n ==> new_idxs@[k] == self.idxs@[n + k],
            decreases len - i,
        {
            new_idxs.push(self.idxs[i]);
            i += 1;
        }
        match &self.vals {
            DiffVals::Plain(v) => {
                let mut new_vals: Vec<T> = Vec::new();
                let mut j: usize = n;
                while j < len
                    invariant
                        n <= j <= len,
                        len == self.idxs@.len(),
                        v@.len() == self.idxs@.len(),
                        new_vals@.len() == j - n,
                        forall|k: int| 0 <= k < j - n ==> new_vals@[k] == v@[n + k],
                    decreases len - j,
                {
                    new_vals.push(v[j]);
                    j += 1;
                }
                self.idxs = new_idxs;
                self.vals = DiffVals::Plain(new_vals);
            }
            DiffVals::Dict { dict, codes } => {
                let mut new_dict: Vec<T> = Vec::new();
                let mut a: usize = 0;
                let dlen = dict.len();
                while a < dlen
                    invariant
                        a <= dlen, dlen == dict@.len(),
                        new_dict@.len() == a,
                        forall|k: int| 0 <= k < a ==> new_dict@[k] == dict@[k],
                    decreases dlen - a,
                {
                    new_dict.push(dict[a]);
                    a += 1;
                }
                let mut new_codes: Vec<usize> = Vec::new();
                let mut j: usize = n;
                while j < len
                    invariant
                        n <= j <= len,
                        len == self.idxs@.len(),
                        codes@.len() == self.idxs@.len(),
                        new_codes@.len() == j - n,
                        forall|k: int| 0 <= k < j - n ==> new_codes@[k] == codes@[n + k],
                    decreases len - j,
                {
                    new_codes.push(codes[j]);
                    j += 1;
                }
                self.idxs = new_idxs;
                self.vals = DiffVals::Dict { dict: new_dict, codes: new_codes };
            }
        }
        assert(self@ =~= old(self)@.subrange(n as int, old(self)@.len() as int));
    }

    /// Truncate to `n` entries. Preserves the kept prefix's view.
    pub fn truncate(&mut self, n: usize)
        requires old(self).wf(), n <= old(self)@.len(),
        ensures final(self).wf(), final(self)@ == old(self)@.subrange(0, n as int),
    {
        self.idxs.truncate(n);
        match &mut self.vals {
            DiffVals::Plain(v) => v.truncate(n),
            DiffVals::Dict { codes, .. } => codes.truncate(n),
        }
        assert(self@ =~= old(self)@.subrange(0, n as int));
    }
}

} // verus!
