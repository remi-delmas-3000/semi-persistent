// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Value-dictionary encoding of a finalized diff frame — the value axis of
//! diff-stack compression (`doc/design/09-diff-stack-compression.md`).
//!
//! Standalone and additive: this module proves the encode/decode bijection over
//! the abstract diff sequence, independent of the `Vec` integration. It is the
//! value-axis win for repetitive columns (the union-find `parent`/`rank`
//! columns, where the captured old values are a low-cardinality multiset): store
//! `dict.len()` distinct values plus one `usize` code per entry, versus one full
//! `T` per entry. The index column is kept verbatim here; the index axis
//! (run-coalescing / Elias-Fano / delta-varint) composes on top and is a
//! separate encoder.

use vstd::prelude::*;
use crate::index_like::IndexLike;

verus! {

/// One finalized frame's diffs with the value column dictionary-encoded and the
/// index column kept verbatim. `codes[t]` indexes `dict` to entry `t`'s value;
/// `idxs[t]` is entry `t`'s original cell index.
pub struct DictFrame<T, I> {
    pub dict: Vec<T>,
    pub codes: Vec<usize>,
    pub idxs: Vec<I>,
}

impl<T: IndexLike, I: IndexLike> DictFrame<T, I> {
    /// Well-formed: the code/index columns are parallel and every code indexes
    /// the dictionary.
    pub open spec fn wf(&self) -> bool {
        &&& self.codes@.len() == self.idxs@.len()
        &&& forall|t: int| 0 <= t < self.codes@.len()
                ==> (#[trigger] self.codes@[t]) < self.dict@.len()
    }

    /// Decode back to the flat `(value, index)` diff sequence.
    pub open spec fn decode(&self) -> Seq<(T, I)> {
        Seq::new(
            self.idxs@.len(),
            |t: int| (self.dict@[self.codes@[t] as int], self.idxs@[t]),
        )
    }
}

/// Find `v` in `dict` by value, returning its position if present. Linear scan:
/// finalized frames are small, and a hashset dedup is a later optimization
/// (the bijection proof is unaffected by the search strategy).
fn dict_find<T: IndexLike>(dict: &Vec<T>, v: T) -> (r: Option<usize>)
    ensures
        match r {
            Some(c) => c < dict@.len() && dict@[c as int] == v,
            None => forall|j: int| 0 <= j < dict@.len() ==> dict@[j] != v,
        },
{
    let mut i: usize = 0;
    while i < dict.len()
        invariant
            i <= dict@.len(),
            forall|j: int| 0 <= j < i ==> dict@[j] != v,
        decreases dict@.len() - i,
    {
        let a = dict[i].as_usize();
        let b = v.as_usize();
        if a == b {
            proof { T::lemma_as_nat_injective(dict@[i as int], v); }
            return Some(i);
        }
        i += 1;
    }
    None
}

/// Compress a finalized frame's diffs by value-dictionary encoding.
/// The bijection: `decode(compress(d)) == d`.
pub fn compress<T: IndexLike, I: IndexLike>(diffs: &Vec<(T, I)>) -> (r: DictFrame<T, I>)
    ensures
        r.wf(),
        r.decode() == diffs@,
{
    let mut dict: Vec<T> = Vec::new();
    let mut codes: Vec<usize> = Vec::new();
    let mut idxs: Vec<I> = Vec::new();
    let mut i: usize = 0;
    while i < diffs.len()
        invariant
            i <= diffs@.len(),
            codes@.len() == i,
            idxs@.len() == i,
            forall|t: int| 0 <= t < i ==> (#[trigger] codes@[t]) < dict@.len(),
            forall|t: int| 0 <= t < i ==> dict@[#[trigger] codes@[t] as int] == diffs@[t].0,
            forall|t: int| 0 <= t < i ==> #[trigger] idxs@[t] == diffs@[t].1,
        decreases diffs@.len() - i,
    {
        let v = diffs[i].0;
        let idx = diffs[i].1;
        let code = match dict_find(&dict, v) {
            Some(c) => c,
            None => {
                let c = dict.len();
                dict.push(v);
                c
            }
        };
        codes.push(code);
        idxs.push(idx);
        i += 1;
    }
    let r = DictFrame { dict, codes, idxs };
    proof {
        assert forall|t: int| 0 <= t < diffs@.len()
            implies r.decode()[t] == diffs@[t] by {
            assert(r.decode()[t] == (diffs@[t].0, diffs@[t].1));
        }
        assert(r.decode() =~= diffs@);
    }
    r
}

// ---------------------------------------------------------------------------
// Index axis: run-coalescing encoder
// ---------------------------------------------------------------------------

/// Expand one run: `vals` laid at consecutive indices `start, start+1, ...`.
pub open spec fn expand_run<T>(start: nat, vals: Seq<T>) -> Seq<(T, nat)>
    decreases vals.len(),
{
    if vals.len() == 0 {
        Seq::empty()
    } else {
        seq![(vals[0], start)] + expand_run(start + 1, vals.subrange(1, vals.len() as int))
    }
}

/// Expand a run list to the flat `(value, index)` sequence.
pub open spec fn expand_runs<T>(starts: Seq<nat>, vals: Seq<Seq<T>>) -> Seq<(T, nat)>
    decreases starts.len(),
{
    if starts.len() == 0 || vals.len() == 0 {
        Seq::empty()
    } else {
        expand_run(starts[0], vals[0]) + expand_runs(
            starts.subrange(1, starts.len() as int),
            vals.subrange(1, vals.len() as int),
        )
    }
}

/// `expand_run` appends at the end: laying one more value `v` at `start +
/// vals.len()` extends the expansion by exactly `(v, start + vals.len())`.
pub proof fn lemma_expand_run_push<T>(start: nat, vals: Seq<T>, v: T)
    ensures
        expand_run(start, vals.push(v))
            == expand_run(start, vals) + seq![(v, start + vals.len())],
    decreases vals.len(),
{
    reveal_with_fuel(expand_run, 2);
    if vals.len() == 0 {
        assert(vals.push(v) =~= seq![v]);
        assert(expand_run(start, vals) =~= Seq::<(T, nat)>::empty());
        assert(expand_run(start, vals.push(v)) =~= seq![(v, start)]);
        assert(expand_run(start, vals) + seq![(v, start + vals.len())] =~= seq![(v, start)]);
    } else {
        // head stays; recurse on the tail, which is `vals[1..].push(v)`.
        let tail = vals.subrange(1, vals.len() as int);
        lemma_expand_run_push(start + 1, tail, v);
        assert(tail.len() == (vals.len() - 1) as nat);
        // unfold the LHS one step: head is `vals[0]`, tail becomes `tail.push(v)`.
        assert(vals.push(v)[0] == vals[0]);
        assert(vals.push(v).subrange(1, vals.push(v).len() as int) =~= tail.push(v));
        assert(expand_run(start, vals.push(v))
            == seq![(vals[0], start)] + expand_run(start + 1, tail.push(v)));
        // IH gives the tail expansion; the appended index reassociates to `start + vals.len()`.
        assert((start + 1) + tail.len() == start + vals.len());
        assert(expand_run(start + 1, tail.push(v))
            == expand_run(start + 1, tail) + seq![(v, start + vals.len())]);
        // unfold the RHS's `expand_run(start, vals)` one step, then reassociate the
        // three concrete sub-sequences explicitly (Verus does not reassociate `+`
        // over the recursive subterms on its own).
        let a = seq![(vals[0], start)];
        let b = expand_run(start + 1, tail);
        let c = seq![(v, start + vals.len())];
        assert(expand_run(start, vals) == a + b);
        assert(expand_run(start, vals.push(v)) == a + (b + c));
        assert(a + (b + c) =~= (a + b) + c);
        assert(expand_run(start, vals.push(v)) == expand_run(start, vals) + c);
    }
}

/// Appending a whole new run to the end of a run list appends that run's
/// expansion to the end of the flattened result.
pub proof fn lemma_expand_runs_snoc<T>(starts: Seq<nat>, vals: Seq<Seq<T>>, s: nat, vs: Seq<T>)
    requires
        starts.len() == vals.len(),
    ensures
        expand_runs(starts.push(s), vals.push(vs))
            == expand_runs(starts, vals) + expand_run(s, vs),
    decreases starts.len(),
{
    reveal_with_fuel(expand_runs, 2);
    if starts.len() == 0 {
        assert(starts.push(s) =~= seq![s]);
        assert(vals.push(vs) =~= seq![vs]);
        assert(expand_runs(starts, vals) =~= Seq::<(T, nat)>::empty());
        assert(seq![s].subrange(1, 1) =~= Seq::<nat>::empty());
        assert(seq![vs].subrange(1, 1) =~= Seq::<Seq<T>>::empty());
        assert(expand_runs(seq![s], seq![vs]) =~= expand_run(s, vs));
    } else {
        let rs = starts.subrange(1, starts.len() as int);
        let rv = vals.subrange(1, vals.len() as int);
        lemma_expand_runs_snoc(rs, rv, s, vs);
        assert(starts.push(s)[0] == starts[0]);
        assert(vals.push(vs)[0] == vals[0]);
        assert(starts.push(s).subrange(1, starts.push(s).len() as int) =~= rs.push(s));
        assert(vals.push(vs).subrange(1, vals.push(vs).len() as int) =~= rv.push(vs));
        let a = expand_run(starts[0], vals[0]);
        let b = expand_runs(rs, rv);
        let c = expand_run(s, vs);
        assert(expand_runs(starts.push(s), vals.push(vs))
            == a + expand_runs(rs.push(s), rv.push(vs)));
        assert(expand_runs(rs.push(s), rv.push(vs)) == b + c);
        assert(expand_runs(starts, vals) == a + b);
        assert(expand_runs(starts.push(s), vals.push(vs)) == a + (b + c));
        assert(a + (b + c) =~= (a + b) + c);
        assert(expand_runs(starts.push(s), vals.push(vs)) == expand_runs(starts, vals) + c);
    }
}

/// Index-major run-coalescing encoding of one finalized frame, proven bijective
/// against a sorted-strictly-ascending-by-index diff sequence at the `nat` index
/// level (`Vec` integration materializes `I` from these `usize` starts via
/// `try_from_usize`). `starts[r]` is run `r`'s first index; `vals[r]` its
/// values, laid at consecutive indices.
pub struct RunFrame<T> {
    pub starts: Vec<usize>,
    pub vals: Vec<Vec<T>>,
}

impl<T: Copy> RunFrame<T> {
    /// Run values as a `Seq<Seq<T>>`.
    pub open spec fn vals_seq(&self) -> Seq<Seq<T>> {
        Seq::new(self.vals@.len(), |r: int| self.vals@[r]@)
    }

    /// Run starts as a `Seq<nat>`.
    pub open spec fn starts_nat(&self) -> Seq<nat> {
        Seq::new(self.starts@.len(), |r: int| self.starts@[r] as nat)
    }

    pub open spec fn wf(&self) -> bool {
        self.starts@.len() == self.vals@.len()
    }

    pub open spec fn decode(&self) -> Seq<(T, nat)> {
        expand_runs(self.starts_nat(), self.vals_seq())
    }
}

/// The diff sequence with indices projected to `nat` — the abstract target the
/// run encoder reproduces.
pub open spec fn mapped_diffs<T>(d: Seq<(T, usize)>, n: nat) -> Seq<(T, nat)> {
    Seq::new(n, |t: int| (d[t as int].0, d[t as int].1 as nat))
}

/// Local run-list `starts` projected to `nat` (matches `RunFrame::starts_nat`).
pub open spec fn starts_to_nat(s: Seq<usize>) -> Seq<nat> {
    Seq::new(s.len(), |r: int| s[r] as nat)
}

/// Local run-list `vals` projected to `Seq<Seq<T>>` (matches `RunFrame::vals_seq`).
pub open spec fn vals_to_seq<T>(v: Seq<Vec<T>>) -> Seq<Seq<T>> {
    Seq::new(v.len(), |r: int| v[r]@)
}

/// `mapped_diffs` extends by one element as `n` grows.
pub proof fn lemma_mapped_push<T>(d: Seq<(T, usize)>, n: nat)
    requires
        n < d.len(),
    ensures
        mapped_diffs(d, n + 1) == mapped_diffs(d, n) + seq![(d[n as int].0, d[n as int].1 as nat)],
{
    assert(mapped_diffs(d, n + 1)
        =~= mapped_diffs(d, n) + seq![(d[n as int].0, d[n as int].1 as nat)]);
}

/// Encode a finalized frame (sorted strictly ascending by index) as run-coalesced
/// runs. The bijection: `decode(compress_runs(d)) == d` at the `nat` index level.
pub fn compress_runs<T: Copy>(diffs: &Vec<(T, usize)>) -> (r: RunFrame<T>)
    requires
        forall|a: int, b: int| 0 <= a < b < diffs@.len() ==> diffs@[a].1 < diffs@[b].1,
    ensures
        r.wf(),
        r.decode() == mapped_diffs(diffs@, diffs@.len()),
{
    let mut starts: Vec<usize> = Vec::new();
    let mut vals: Vec<Vec<T>> = Vec::new();
    let mut cur_start: usize = 0;
    let mut cur_vals: Vec<T> = Vec::new();
    let mut i: usize = 0;
    while i < diffs.len()
        invariant
            i <= diffs@.len(),
            starts@.len() == vals@.len(),
            expand_runs(starts_to_nat(starts@), vals_to_seq(vals@))
                + expand_run(cur_start as nat, cur_vals@)
                == mapped_diffs(diffs@, i as nat),
            (cur_vals@.len() == 0) <==> (i == 0),
            cur_vals@.len() > 0
                ==> cur_start as nat == diffs@[i as int - cur_vals@.len()].1 as nat,
            cur_vals@.len() > 0
                ==> cur_start as nat + cur_vals@.len() - 1 == diffs@[i as int - 1].1 as nat,
            forall|a: int, b: int| 0 <= a < b < diffs@.len() ==> diffs@[a].1 < diffs@[b].1,
        decreases diffs@.len() - i,
    {
        let v = diffs[i].0;
        let idx = diffs[i].1;
        let ghost old_starts = starts@;
        let ghost old_vals = vals@;
        let ghost old_cur_start = cur_start;
        let ghost old_cur_vals = cur_vals@;
        if cur_vals.len() == 0 {
            cur_start = idx;
            cur_vals.push(v);
            proof {
                lemma_expand_run_push(idx as nat, Seq::<T>::empty(), v);
                assert(Seq::<T>::empty().push(v) =~= cur_vals@);
                assert(expand_run(idx as nat, cur_vals@) =~= seq![(v, idx as nat)]);
                lemma_mapped_push(diffs@, i as nat);
            }
        } else if idx - cur_start == cur_vals.len() {
            proof {
                lemma_expand_run_push(cur_start as nat, cur_vals@, v);
            }
            cur_vals.push(v);
            proof {
                assert(old_cur_vals.push(v) =~= cur_vals@);
                assert(cur_start as nat + old_cur_vals.len() == idx as nat);
                let a = expand_runs(starts_to_nat(starts@), vals_to_seq(vals@));
                let b = expand_run(cur_start as nat, old_cur_vals);
                let c = seq![(v, idx as nat)];
                assert(expand_run(cur_start as nat, cur_vals@) == b + c);
                assert(a + (b + c) =~= (a + b) + c);
                lemma_mapped_push(diffs@, i as nat);
            }
        } else {
            proof {
                lemma_expand_runs_snoc(starts_to_nat(starts@), vals_to_seq(vals@),
                    cur_start as nat, cur_vals@);
            }
            starts.push(cur_start);
            vals.push(cur_vals);
            cur_start = idx;
            cur_vals = Vec::new();
            cur_vals.push(v);
            proof {
                assert(starts_to_nat(starts@) =~= starts_to_nat(old_starts).push(old_cur_start as nat));
                assert(vals_to_seq(vals@) =~= vals_to_seq(old_vals).push(old_cur_vals));
                lemma_expand_run_push(idx as nat, Seq::<T>::empty(), v);
                assert(Seq::<T>::empty().push(v) =~= cur_vals@);
                assert(expand_run(idx as nat, cur_vals@) =~= seq![(v, idx as nat)]);
                let a = expand_runs(starts_to_nat(old_starts), vals_to_seq(old_vals));
                let b = expand_run(old_cur_start as nat, old_cur_vals);
                let c = seq![(v, idx as nat)];
                assert(expand_runs(starts_to_nat(starts@), vals_to_seq(vals@)) == a + b);
                assert(a + b + c =~= (a + b) + c);
                lemma_mapped_push(diffs@, i as nat);
            }
        }
        i += 1;
    }
    // Loop exit: i == diffs.len(), so the invariant reads
    //   expand_runs(sn(starts@), vs(vals@)) + expand_run(cur_start, cur_vals@)
    //     == mapped_diffs(diffs@, diffs@.len()).
    let ghost pre_starts = starts@;
    let ghost pre_vals = vals@;
    let ghost pre_cur_start = cur_start;
    let ghost pre_cur_vals = cur_vals@;
    if cur_vals.len() > 0 {
        starts.push(cur_start);
        vals.push(cur_vals);
        proof {
            lemma_expand_runs_snoc(starts_to_nat(pre_starts), vals_to_seq(pre_vals),
                pre_cur_start as nat, pre_cur_vals);
            assert(starts_to_nat(starts@) =~= starts_to_nat(pre_starts).push(pre_cur_start as nat));
            assert(vals_to_seq(vals@) =~= vals_to_seq(pre_vals).push(pre_cur_vals));
        }
    } else {
        proof {
            // cur empty ⇒ i == 0 ⇒ diffs empty; the current-run term is empty, so
            // the flushed runs alone reproduce the (empty) mapped sequence.
            assert(expand_run(cur_start as nat, cur_vals@) =~= Seq::<(T, nat)>::empty());
        }
    }
    let r = RunFrame { starts, vals };
    proof {
        assert(r.starts_nat() =~= starts_to_nat(r.starts@));
        assert(r.vals_seq() =~= vals_to_seq(r.vals@));
    }
    r
}

/// Per-instance compression mode, selected at `Vec` construction (not a const
/// generic): one binary runs SMT with `None` (speed) and equality saturation
/// with a per-column mode (memory). Extensible; `IndexRuns` (index-major
/// run-coalescing) lands as a later variant.
#[derive(Clone, Copy)]
pub enum CompressionMode {
    None,
    ValueDict,
}

/// A finalized frame in whichever representation its column's mode selected. The
/// active frame is always uncompressed; this is what `mark` stores for a closed
/// frame, and what `restore` decodes.
pub enum FrameEncoding<T, I> {
    Plain(Vec<(T, I)>),
    Dict(DictFrame<T, I>),
}

impl<T: IndexLike, I: IndexLike> FrameEncoding<T, I> {
    pub open spec fn wf(&self) -> bool {
        match self {
            FrameEncoding::Plain(_) => true,
            FrameEncoding::Dict(d) => d.wf(),
        }
    }

    /// Decode back to the flat `(value, index)` diff sequence, mode-agnostically.
    pub open spec fn decode(&self) -> Seq<(T, I)> {
        match self {
            FrameEncoding::Plain(v) => v@,
            FrameEncoding::Dict(d) => d.decode(),
        }
    }
}

/// Encode a finalized frame in the given mode. The bijection holds for every
/// mode: `decode(compress_frame(d, mode)) == d`, so `mark` may pick any mode per
/// column at runtime and `restore` reconstructs the same diff regardless.
pub fn compress_frame<T: IndexLike, I: IndexLike>(
    diffs: &Vec<(T, I)>,
    mode: CompressionMode,
) -> (r: FrameEncoding<T, I>)
    ensures
        r.wf(),
        r.decode() == diffs@,
{
    match mode {
        CompressionMode::None => {
            let mut copy: Vec<(T, I)> = Vec::new();
            let mut i: usize = 0;
            while i < diffs.len()
                invariant
                    i <= diffs@.len(),
                    copy@ == diffs@.subrange(0, i as int),
                decreases diffs@.len() - i,
            {
                copy.push(diffs[i]);
                i += 1;
            }
            assert(copy@ =~= diffs@);
            FrameEncoding::Plain(copy)
        }
        CompressionMode::ValueDict => FrameEncoding::Dict(compress(diffs)),
    }
}

} // verus!
