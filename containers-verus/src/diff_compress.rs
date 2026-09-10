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
use crate::index_like::{IndexLike, IndexFromNat};

verus! {

/// The dictionary code column, stored at the narrowest byte width that fits the
/// dictionary size (`u8` for `D <= 256`, `u16` for `D <= 65536`, else `u32`).
/// Its abstract value is `Seq<nat>` regardless of width, so `DictFrame`'s
/// bijection is stated over `view()` and the storage is swappable: a future
/// bit-packed variant (`ceil(log2 D)` bits) drops in behind this same contract
/// without touching the frame or any caller. This is what takes value-major from
/// a loss at `usize` codes to a win (measured 0.63x byte / 0.30x bit-packed).
pub enum Codes {
    U8(Vec<u8>),
    U16(Vec<u16>),
    U32(Vec<u32>),
    Usize(Vec<usize>),
}

impl Codes {
    pub open spec fn view(&self) -> Seq<nat> {
        match self {
            Codes::U8(v) => Seq::new(v@.len(), |i: int| v@[i] as nat),
            Codes::U16(v) => Seq::new(v@.len(), |i: int| v@[i] as nat),
            Codes::U32(v) => Seq::new(v@.len(), |i: int| v@[i] as nat),
            Codes::Usize(v) => Seq::new(v@.len(), |i: int| v@[i] as nat),
        }
    }

    pub fn len(&self) -> (n: usize)
        ensures n == self.view().len(),
    {
        match self {
            Codes::U8(v) => v.len(),
            Codes::U16(v) => v.len(),
            Codes::U32(v) => v.len(),
            Codes::Usize(v) => v.len(),
        }
    }

    pub fn get(&self, i: usize) -> (c: usize)
        requires i < self.view().len(),
        ensures c as nat == self.view()[i as int],
    {
        match self {
            Codes::U8(v) => v[i] as usize,
            Codes::U16(v) => v[i] as usize,
            Codes::U32(v) => v[i] as usize,
            Codes::Usize(v) => v[i],
        }
    }

    /// Bytes of the code column (diagnostic).
    #[verifier::external_body]
    pub fn heap_bytes(&self) -> usize {
        match self {
            Codes::U8(v) => v.capacity(),
            Codes::U16(v) => v.capacity() * 2,
            Codes::U32(v) => v.capacity() * 4,
            Codes::Usize(v) => v.capacity() * 8,
        }
    }

    /// Build the narrowest-width code column from `usize` codes, given the
    /// dictionary size they index into. `view()` reproduces the codes exactly.
    pub fn from_usize(codes: &Vec<usize>, dict_len: usize) -> (r: Codes)
        requires forall|t: int| 0 <= t < codes@.len() ==> #[trigger] codes@[t] < dict_len,
        ensures
            r.view().len() == codes@.len(),
            forall|t: int| 0 <= t < codes@.len() ==> #[trigger] r.view()[t] == codes@[t] as nat,
    {
        if dict_len <= 256 {
            let mut v: Vec<u8> = Vec::new();
            let mut t: usize = 0;
            while t < codes.len()
                invariant
                    t <= codes@.len(),
                    dict_len <= 256,
                    forall|k: int| 0 <= k < codes@.len() ==> #[trigger] codes@[k] < dict_len,
                    v@.len() == t,
                    forall|k: int| 0 <= k < t ==> #[trigger] v@[k] as nat == codes@[k] as nat,
                decreases codes@.len() - t,
            {
                v.push(codes[t] as u8);
                t += 1;
            }
            let r = Codes::U8(v);
            assert forall|k: int| 0 <= k < codes@.len() implies #[trigger] r.view()[k] == codes@[k] as nat by {}
            r
        } else if dict_len <= 65536 {
            let mut v: Vec<u16> = Vec::new();
            let mut t: usize = 0;
            while t < codes.len()
                invariant
                    t <= codes@.len(),
                    dict_len <= 65536,
                    forall|k: int| 0 <= k < codes@.len() ==> #[trigger] codes@[k] < dict_len,
                    v@.len() == t,
                    forall|k: int| 0 <= k < t ==> #[trigger] v@[k] as nat == codes@[k] as nat,
                decreases codes@.len() - t,
            {
                v.push(codes[t] as u16);
                t += 1;
            }
            let r = Codes::U16(v);
            assert forall|k: int| 0 <= k < codes@.len() implies #[trigger] r.view()[k] == codes@[k] as nat by {}
            r
        } else if dict_len <= u32::MAX as usize {
            let mut v: Vec<u32> = Vec::new();
            let mut t: usize = 0;
            while t < codes.len()
                invariant
                    t <= codes@.len(),
                    dict_len <= u32::MAX as usize,
                    forall|k: int| 0 <= k < codes@.len() ==> #[trigger] codes@[k] < dict_len,
                    v@.len() == t,
                    forall|k: int| 0 <= k < t ==> #[trigger] v@[k] as nat == codes@[k] as nat,
                decreases codes@.len() - t,
            {
                v.push(codes[t] as u32);
                t += 1;
            }
            let r = Codes::U32(v);
            assert forall|k: int| 0 <= k < codes@.len() implies #[trigger] r.view()[k] == codes@[k] as nat by {}
            r
        } else {
            // Fallback: dictionary larger than 2^32 entries — keep usize codes
            // (no narrowing possible without truncation).
            let mut v: Vec<usize> = Vec::new();
            let mut t: usize = 0;
            while t < codes.len()
                invariant
                    t <= codes@.len(),
                    v@.len() == t,
                    forall|k: int| 0 <= k < t ==> #[trigger] v@[k] as nat == codes@[k] as nat,
                decreases codes@.len() - t,
            {
                v.push(codes[t]);
                t += 1;
            }
            let r = Codes::Usize(v);
            assert forall|k: int| 0 <= k < codes@.len() implies #[trigger] r.view()[k] == codes@[k] as nat by {}
            r
        }
    }
}

/// One finalized frame's diffs with the value column dictionary-encoded and the
/// index column kept verbatim. `codes[t]` indexes `dict` to entry `t`'s value;
/// `idxs[t]` is entry `t`'s original cell index.
pub struct DictFrame<T, I> {
    pub dict: Vec<T>,
    pub codes: Codes,
    pub idxs: Vec<I>,
}

impl<T: IndexLike, I: IndexLike> DictFrame<T, I> {
    /// Well-formed: the code/index columns are parallel and every code indexes
    /// the dictionary. Stated over `codes.view()`, so the code storage width is
    /// invisible here.
    pub open spec fn wf(&self) -> bool {
        &&& self.codes.view().len() == self.idxs@.len()
        &&& forall|t: int| 0 <= t < self.codes.view().len()
                ==> (#[trigger] self.codes.view()[t]) < self.dict@.len()
    }

    /// Decode back to the flat `(value, index)` diff sequence.
    pub open spec fn decode(&self) -> Seq<(T, I)> {
        Seq::new(
            self.idxs@.len(),
            |t: int| (self.dict@[self.codes.view()[t] as int], self.idxs@[t]),
        )
    }

    /// Executable decode: materialize the flat diff sequence. The two-stack
    /// `Vec` integration calls this to bring a compressed frame back to plain
    /// before a restore lands in it; the benchmark suite times it as the
    /// decompression cost. `r@ == decode()`, so it is transparent to the
    /// reconstruction proof.
    pub fn decode_exec(&self) -> (r: Vec<(T, I)>)
        requires self.wf(),
        ensures r@ == self.decode(),
    {
        let mut out: Vec<(T, I)> = Vec::new();
        let n = self.idxs.len();
        let mut t: usize = 0;
        while t < n
            invariant
                t <= n,
                n == self.idxs@.len(),
                self.wf(),
                out@.len() == t,
                forall|k: int| 0 <= k < t ==> out@[k] == self.decode()[k],
            decreases n - t,
        {
            let code = self.codes.get(t);
            let v = self.dict[code];
            let idx = self.idxs[t];
            out.push((v, idx));
            t += 1;
        }
        assert(out@ =~= self.decode());
        out
    }
}

/// Find `v` in `dict` by value, returning its position if present. Linear scan:
/// finalized frames are small, and a hashset dedup is a later optimization
/// (the bijection proof is unaffected by the search strategy).
pub(crate) fn dict_find<T: IndexLike>(dict: &Vec<T>, v: T) -> (r: Option<usize>)
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
    // Narrow the codes to the smallest width that indexes `dict` (the value-major
    // space win); `Codes::from_usize` reproduces the code sequence exactly.
    let dict_len = dict.len();
    let packed = Codes::from_usize(&codes, dict_len);
    let r = DictFrame { dict, codes: packed, idxs };
    proof {
        assert forall|t: int| 0 <= t < diffs@.len()
            implies r.decode()[t] == diffs@[t] by {
            assert(r.codes.view()[t] == codes@[t] as nat);
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

/// `expand_run` lays `vals` at consecutive indices: entry `o` is `(vals[o],
/// start + o)`, and the length is `vals.len()`. The pointwise fact the run
/// decoder needs to reconstruct each dropped index from `start + offset`.
pub proof fn lemma_expand_run_index<T>(start: nat, vals: Seq<T>)
    ensures
        expand_run(start, vals).len() == vals.len(),
        forall|o: int| 0 <= o < vals.len() ==>
            #[trigger] expand_run(start, vals)[o] == (vals[o], (start + o) as nat),
    decreases vals.len(),
{
    reveal_with_fuel(expand_run, 2);
    if vals.len() == 0 {
    } else {
        let tail = vals.subrange(1, vals.len() as int);
        lemma_expand_run_index(start + 1, tail);
        // expand_run(start, vals) == [(vals[0], start)] + expand_run(start+1, tail)
        assert forall|o: int| 0 <= o < vals.len() implies
            #[trigger] expand_run(start, vals)[o] == (vals[o], (start + o) as nat) by {
            if o == 0 {
            } else {
                assert(tail[o - 1] == vals[o]);
                assert(expand_run(start, vals)[o] == expand_run(start + 1, tail)[o - 1]);
            }
        }
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

    /// Decode to `(T, I)` diffs, reconstructing each dropped index from its `nat`
    /// via `from_nat`. Well-defined when every decoded index fits `I` (`fits`),
    /// which holds for any run frame built from real `I` indices.
    pub open spec fn decode_i<I: IndexFromNat>(&self) -> Seq<(T, I)> {
        Seq::new(
            self.decode().len(),
            |t: int| (self.decode()[t].0, I::from_nat(self.decode()[t].1)),
        )
    }

    /// Every decoded index is a valid `I` (below `max_nat`). Established at
    /// compress time: the indices came from real `I` values.
    pub open spec fn fits<I: IndexFromNat>(&self) -> bool {
        forall|t: int| 0 <= t < self.decode().len() ==> (#[trigger] self.decode()[t].1) < I::max_nat()
    }

    /// Executable decode to `(T, I)`. `external_body`: the verified reference is
    /// `compress_runs_writeorder`'s bijection (`decode() == mapped_diffs`) plus
    /// the `decode_i` spec above; this scalar decoder is checked against them by
    /// the `run_frame_roundtrip` proptest in `containers-conformance` (doc 09:
    /// verified scalar reference, exec path conformance-checked, not proved). Its
    /// walk over runs mirrors `expand_runs` exactly, laying each run's values at
    /// `from_usize(start + offset)`. Trust ledger: group B (a pure representation
    /// transform, no `unsafe`, deterministic).
    #[verifier::external_body]
    pub fn decode_exec_i<I: IndexFromNat>(&self) -> (r: Vec<(T, I)>)
        requires self.wf(), self.fits::<I>(),
        ensures r@ == self.decode_i::<I>(),
    {
        let mut out: Vec<(T, I)> = Vec::new();
        let nruns = self.starts.len();
        let mut r: usize = 0;
        while r < nruns {
            let start = self.starts[r];
            let run = &self.vals[r];
            let mut off: usize = 0;
            while off < run.len() {
                let idx = I::from_usize(start + off)
                    .expect("run index fits I (established by fits)");
                out.push((run[off], idx));
                off += 1;
            }
            r += 1;
        }
        out
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
/// `rlimit` pinned: the run-coalescing invariant carries several `expand_*`
/// sequence identities whose instantiation is near the default budget (z3-seed
/// flaky otherwise).
#[verifier::rlimit(800)]
pub fn compress_runs<T: Copy>(diffs: &Vec<(T, usize)>) -> (r: RunFrame<T>)
    requires
        forall|a: int, b: int| #![trigger diffs@[a].1, diffs@[b].1]
            0 <= a < b < diffs@.len() ==> diffs@[a].1 < diffs@[b].1,
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
            forall|a: int, b: int| #![trigger diffs@[a].1, diffs@[b].1]
                0 <= a < b < diffs@.len() ==> diffs@[a].1 < diffs@[b].1,
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

/// Write-order run-coalescing: coalesces only entries that are consecutive in
/// BOTH capture order and index (`idx == cur_start + cur_vals.len()`), so it
/// reproduces the input sequence EXACTLY — no sort, no reorder — hence
/// `decode(compress_runs_writeorder(d)) == mapped_diffs(d)` for ANY `d`. This is
/// the encoder the two-stack uses: it preserves the flat view exactly (unlike a
/// sort-first index-major encoder, which would permute the frame), so the
/// mark/restore theorems carry. It coalesces a contiguous range only when it was
/// captured in ascending order; scattered or descending captures fall back to
/// singleton runs (correct, just uncompressed). The `idx >= cur_start` guard
/// makes the run-extension test underflow-free without a sortedness precondition.
#[verifier::rlimit(800)]
pub fn compress_runs_writeorder<T: Copy>(diffs: &Vec<(T, usize)>) -> (r: RunFrame<T>)
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
        } else if idx >= cur_start && idx - cur_start == cur_vals.len() {
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

/// Sort a finalized frame ascending by index. The contract is the only thing
/// callers depend on — the multiset of writes is preserved (a permutation),
/// the result is ascending, and uniqueness carries over — so the internal
/// algorithm is swappable behind it (std introsort now; a radix pass later if a
/// bench shows it matters) without touching a single caller or proof. Soundness
/// of *using* a sorted frame is separate and already proved
/// (`vec::lemma_multiset_eq_overlay`): a permuted frame restores identically.
/// `external_body` because the sort algorithm is not the verified surface — its
/// contract is, and `sort_frame_roundtrip` (containers-conformance) checks it.
/// Trust ledger: group B (a permutation + order property, no `unsafe`).
#[verifier::external_body]
pub fn sort_frame_by_index<T: Copy, I: IndexLike>(d: &Vec<(T, I)>) -> (r: Vec<(T, I)>)
    ensures
        r@.to_multiset() == d@.to_multiset(),
        forall|a: int, b: int| 0 <= a < b < r@.len()
            ==> (#[trigger] r@[a]).1.as_nat() <= (#[trigger] r@[b]).1.as_nat(),
        unique_idx(d@) ==> unique_idx(r@),
{
    let mut r = d.clone();
    r.sort_unstable_by_key(|e| e.1.as_usize());
    r
}

/// A finalized frame has at most one write per cell (first-write-wins), so its
/// index projection is injective. Mirrors `vec::unique_idx` for the encoder side.
pub open spec fn unique_idx<T, I: IndexLike>(d: Seq<(T, I)>) -> bool {
    forall|a: int, b: int|
        0 <= a < d.len() && 0 <= b < d.len() && a != b
            ==> (#[trigger] d[a]).1.as_nat() != (#[trigger] d[b]).1.as_nat()
}

/// Sort-first index-major encoding: sort the frame by index, then run-coalesce.
/// Because sorting captures ALL index contiguity (not just capture-order runs),
/// this is the strongest index-major compressor. It is a REORDERING codec, so it
/// does not reproduce the input sequence — but it preserves the multiset of
/// writes (`decode_i().to_multiset() == diffs@.to_multiset()`), which is the whole
/// codec contract: `vec::lemma_multiset_eq_overlay` then gives identical restore.
/// Requires the frame's indices be unique (first-write-wins), which is what makes
/// the sort strictly ascending (so `compress_runs` applies) and the reorder sound.
pub fn compress_runs_sorted<T: IndexLike, I: IndexFromNat>(diffs: &Vec<(T, I)>) -> (r: RunFrame<T>)
    requires unique_idx(diffs@),
    ensures
        r.wf(),
        r.fits::<I>(),
        r.decode_i::<I>().to_multiset() == diffs@.to_multiset(),
        unique_idx(r.decode_i::<I>()),
{
    let s = sort_frame_by_index(diffs);
    // s: same multiset as diffs, sorted (<=) by index, unique indices.
    assert(unique_idx(s@));
    // Project to usize and prove strictly ascending (sorted + unique => strict).
    let mut usized: Vec<(T, usize)> = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s@.len(),
            usized@.len() == i,
            forall|t: int| #![trigger usized@[t]] 0 <= t < i ==>
                usized@[t].0 == s@[t].0
                && usized@[t].1 as nat == s@[t].1.as_nat(),
        decreases s@.len() - i,
    {
        let (v, idx) = s[i];
        usized.push((v, idx.as_usize()));
        i += 1;
    }
    proof {
        // Strictly ascending: sorted gives <=, uniqueness upgrades to <.
        assert forall|a: int, b: int| 0 <= a < b < usized@.len() implies
            usized@[a].1 < usized@[b].1 by {
            assert(s@[a].1.as_nat() <= s@[b].1.as_nat());
            assert(s@[a].1.as_nat() != s@[b].1.as_nat());
            assert(usized@[a].1 as nat == s@[a].1.as_nat());
            assert(usized@[b].1 as nat == s@[b].1.as_nat());
        }
    }
    let rf = compress_runs(&usized);
    proof {
        // rf.decode() == mapped_diffs(usized@) == the (T, nat) projection of s;
        // decode_i maps each nat back via from_nat, recovering s exactly.
        assert(usized@.len() == s@.len());
        assert forall|t: int| 0 <= t < s@.len() implies
            rf.decode()[t] == (s@[t].0, s@[t].1.as_nat()) by {
            assert(rf.decode()[t] == (usized@[t].0, usized@[t].1 as nat));
        }
        assert forall|t: int| 0 <= t < rf.decode().len() implies
            (#[trigger] rf.decode()[t].1) < I::max_nat() by {
            I::lemma_as_nat_bounded_val(s@[t].1);
        }
        assert forall|t: int| 0 <= t < s@.len() implies
            #[trigger] rf.decode_i::<I>()[t] == s@[t] by {
            I::lemma_from_as_nat(s@[t].1);
        }
        assert(rf.decode_i::<I>() =~= s@);
        // Same multiset as diffs, and uniqueness carries.
        assert(rf.decode_i::<I>().to_multiset() == s@.to_multiset());
        assert(s@.to_multiset() == diffs@.to_multiset());
    }
    rf
}

/// Per-instance compression mode, selected at `Vec` construction (not a const
/// generic): one binary runs SMT with `None` (speed) and equality saturation
/// with a per-column mode (memory). `ValueDict` is value-major (dictionary +
/// codes, for value-repetitive columns like union-find `parent`/`rank`);
/// `IndexRuns` is index-major (write-order run-coalescing, for columns with
/// contiguous batch updates — it drops the index column).
#[derive(Clone, Copy)]
pub enum CompressionMode {
    None,
    ValueDict,
    IndexRuns,
    /// Choose per frame by exact-size costing (`choose_mode`): compute the plain,
    /// run, and dictionary sizes for this frame and pick the smallest. Lets one
    /// column carry a mix of schemes — value-major frames where a value repeats,
    /// index-major frames where indices cluster — decided from the frame's own
    /// content rather than a fixed guess.
    Auto,
}

/// Exact-size cost selector: pick the cheapest scheme for this specific frame.
/// `external_body` — a heuristic with no spec content: whichever mode it returns,
/// `compress_frame`'s bijection still holds, so correctness does not depend on the
/// choice, only the size does. `R` (run count) is the scatter signal; `D`
/// (distinct values) is the value-repetition signal.
#[verifier::external_body]
pub fn choose_mode<T: IndexLike, I: IndexFromNat>(diffs: &Vec<(T, I)>) -> CompressionMode {
    // One O(N) stats pass (R runs, D distinct; no sort), then the exact-size
    // decision. `external_body` only for the `size_of`/hashset it threads
    // through; the arithmetic lives in the verified `FrameStats::best_mode`.
    let stats = crate::compression_stats::frame_stats(diffs);
    // best_mode costs each scheme at the shipped encoders' achievable widths
    // (sorted run count, narrow code width computed from D internally).
    stats.best_mode(core::mem::size_of::<T>(), core::mem::size_of::<I>())
}

/// A finalized frame in whichever representation its column's mode selected. The
/// active frame is always uncompressed; this is what `mark` stores for a closed
/// frame, and what `restore` decodes. The `Runs` arm needs `I: IndexFromNat` to
/// reconstruct the dropped index column, so the whole enum carries that bound.
pub enum FrameEncoding<T, I> {
    Plain(Vec<(T, I)>),
    Dict(DictFrame<T, I>),
    Runs(RunFrame<T>),
}

impl<T: IndexLike, I: IndexFromNat> FrameEncoding<T, I> {
    pub open spec fn wf(&self) -> bool {
        match self {
            FrameEncoding::Plain(_) => true,
            FrameEncoding::Dict(d) => d.wf(),
            FrameEncoding::Runs(rf) => rf.wf() && rf.fits::<I>(),
        }
    }

    /// Decode back to the flat `(value, index)` diff sequence, mode-agnostically.
    pub open spec fn decode(&self) -> Seq<(T, I)> {
        match self {
            FrameEncoding::Plain(v) => v@,
            FrameEncoding::Dict(d) => d.decode(),
            FrameEncoding::Runs(rf) => rf.decode_i::<I>(),
        }
    }

    /// Executable decode: materialize the flat diff sequence for a finalized
    /// frame. This is what the two-stack restore calls to bring a compressed
    /// frame back to plain. `r@ == decode()`.
    pub fn decode_exec(&self) -> (r: Vec<(T, I)>)
        requires self.wf(),
        ensures r@ == self.decode(),
    {
        match self {
            FrameEncoding::Plain(v) => {
                let mut copy: Vec<(T, I)> = Vec::new();
                let mut i: usize = 0;
                while i < v.len()
                    invariant
                        i <= v@.len(),
                        copy@ == v@.subrange(0, i as int),
                    decreases v@.len() - i,
                {
                    copy.push(v[i]);
                    i += 1;
                }
                assert(copy@ =~= v@);
                copy
            }
            FrameEncoding::Dict(d) => d.decode_exec(),
            FrameEncoding::Runs(rf) => rf.decode_exec_i::<I>(),
        }
    }
}

/// Encode a finalized frame in the given mode. The bijection holds for every
/// mode: `decode(compress_frame(d, mode)) == d`, so `mark` may pick any mode per
/// column at runtime and `restore` reconstructs the same diff regardless.
pub fn compress_frame<T: IndexLike, I: IndexFromNat>(
    diffs: &Vec<(T, I)>,
    mode: CompressionMode,
) -> (r: FrameEncoding<T, I>)
    ensures
        r.wf(),
        r.decode() == diffs@,
{
    // Resolve Auto to a concrete scheme per frame; the bijection below holds for
    // whichever concrete mode is chosen, so the choice is size-only.
    let mode = match mode {
        CompressionMode::Auto => choose_mode(diffs),
        other => other,
    };
    match mode {
        // choose_mode never returns Auto; if it somehow did, plain is safe.
        CompressionMode::Auto | CompressionMode::None => {
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
        CompressionMode::IndexRuns => {
            // Project indices to usize, run-coalesce in write order (exact-view-
            // preserving), and wrap. decode_i reconstructs each I via from_nat.
            let mut usized: Vec<(T, usize)> = Vec::new();
            let mut i: usize = 0;
            while i < diffs.len()
                invariant
                    i <= diffs@.len(),
                    usized@.len() == i,
                    forall|t: int| 0 <= t < i ==>
                        #[trigger] usized@[t].0 == diffs@[t].0
                        && usized@[t].1 as nat == diffs@[t].1.as_nat(),
                decreases diffs@.len() - i,
            {
                let (v, idx) = diffs[i];
                usized.push((v, idx.as_usize()));
                i += 1;
            }
            let rf = compress_runs_writeorder(&usized);
            // rf.decode() == mapped_diffs(usized@) == the (T, nat) projection of
            // diffs; decode_i maps each nat back to I via from_nat, recovering diffs.
            proof {
                assert(usized@.len() == diffs@.len());
                assert forall|t: int| 0 <= t < diffs@.len() implies
                    rf.decode()[t] == (diffs@[t].0, diffs@[t].1.as_nat()) by {
                    assert(rf.decode()[t] == (usized@[t].0, usized@[t].1 as nat));
                }
                // fits: every decoded index is some diffs[t].1.as_nat() < max_nat.
                assert forall|t: int| 0 <= t < rf.decode().len() implies
                    (#[trigger] rf.decode()[t].1) < I::max_nat() by {
                    I::lemma_as_nat_bounded_val(diffs@[t].1);
                }
                // decode_i recovers diffs: from_nat(diffs[t].1.as_nat()) == diffs[t].1.
                assert forall|t: int| 0 <= t < diffs@.len() implies
                    #[trigger] rf.decode_i::<I>()[t] == diffs@[t] by {
                    I::lemma_from_as_nat(diffs@[t].1);
                }
                assert(rf.decode_i::<I>() =~= diffs@);
            }
            FrameEncoding::Runs(rf)
        }
    }
}

} // verus!
