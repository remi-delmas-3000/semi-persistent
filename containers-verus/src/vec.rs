// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! `Vec<T, I, S, const TRACK: bool>`: the headline semi-persistent vector.
//!
//! The full vector — `push`, `pop` (including into a marked region), `set`,
//! `get`, `mark`, `restore` — is verified at arbitrary mark-nesting depth,
//! with fork-history branch-cut safety. After `restore(token)`,
//! `view() == snapshots[token.frame_idx]`, where `snapshots` is a ghost stack
//! of deep copies recorded at each `mark()` and reconstructed on restore from
//! the sparse diff log (it is never stored at runtime).
//!
//! The well-formedness invariant is the declarative, pointwise `frame_cell_inv`
//! (see `frame_cell_inv`): for each marked cell `j`, its snapshot value lives
//! in exactly one place — the live view if untouched since the mark, or the
//! diff log if overwritten/popped — with first-write-wins giving at most one
//! diff entry per cell per frame.
//!
//! Full narrative, theorems, and proof architecture:
//! `doc/design/01-verification-design.md`.

use vstd::prelude::*;

verus! {

use crate::diff_store::DiffStore;
use crate::frame::Frame;
use crate::index_like::IndexLike;

/// Capacity-reclamation policy applied at `mark` time (parity with
/// production). The verus model treats both variants as observationally
/// inert: shrinking is a capacity hint that never changes `view()` or any
/// tracked sequence, so it carries no spec content.
#[derive(Copy, Clone)]
pub enum ShrinkPolicy {
    Never,
    IfOverallocated { factor: usize, headroom: usize },
}

/// Opaque token returned by `mark()`.
///
/// `frame_idx` is the reconstruction coordinate (which frame `restore` rolls
/// back to). It is a STRUCTURAL handle only: branch validity and forgery
/// rejection live on the owning group's `History` (doc 10), which validates a
/// `GroupToken` once for every member; `Vec` itself no longer carries a
/// genealogy (H2). A caller that restores through a raw `VecToken` without a
/// `History` gets exactly the structural guarantee `is_restorable_spec`
/// states: the frame exists and reconstruction lands on its snapshot.
#[derive(Copy, Clone)]
pub struct VecToken {
    pub(crate) frame_idx: usize,
}

impl VecToken {
    /// The reconstruction coordinate (spec view; the exec field is
    /// `pub(crate)` — privacy closeout). Public contracts phrase frame
    /// positions through this.
    pub open(crate) spec fn frame_idx_spec(self) -> nat {
        self.frame_idx as nat
    }
}

/// Spec helper: there is some entry in `diffs` pointing at index `j`.
///
/// Used as the "captured" predicate in the declarative invariant.
pub open(crate) spec fn diff_has_index<T, I: IndexLike>(
    diffs: Seq<(T, I)>,
    j: nat,
) -> bool {
    exists|k: int| 0 <= k < diffs.len()
        && (#[trigger] diffs[k]).1.as_nat() == j
}

/// Some entry of `diffs` in `[lo, hi)` points at index `j` (range-scoped
/// `diff_has_index`; the replay loop's flag bookkeeping).
pub open(crate) spec fn diff_has_index_in<T, I: IndexLike>(
    diffs: Seq<(T, I)>,
    lo: int,
    hi: int,
    j: nat,
) -> bool {
    exists|k: int| lo <= k < hi
        && (#[trigger] diffs[k]).1.as_nat() == j
}

/// First-write-wins: each index appears at most once across the diff log.
///
/// Without this, multiple entries could disagree about a slot's marked
/// value and the invariant would be ambiguous. Production enforces this
/// via the per-slot capture flag.
pub open(crate) spec fn diffs_unique_indices<T, I: IndexLike>(
    diffs: Seq<(T, I)>,
) -> bool {
    forall|i: int, j: int|
        0 <= i < diffs.len() && 0 <= j < diffs.len() && i != j
            ==> (#[trigger] diffs[i]).1.as_nat() != (#[trigger] diffs[j]).1.as_nat()
}

/// The declarative frame invariant — your formulation.
///
/// For each cell `j` in the marked region:
///   - If no diff entry points at `j` (uncaptured): `view[j] == snap[j]`.
///     The slot was never written to since mark, so the current view
///     still holds the marked value.
///   - Else (captured): some diff entry `(old, j)` has `old == snap[j]`.
///     The diff log holds the marked value; the current view holds
///     whatever scribble has been written since.
///
/// Both arms are stated as conjuncts. They are *jointly* the meaning of
/// "snap is the snapshot at mark time of this view-plus-diff-log triple."
/// First-write-wins (above) ensures the captured arm's witness is unique.
pub open(crate) spec fn frame_inv<T, I: IndexLike>(
    view: Seq<T>,
    diffs: Seq<(T, I)>,
    snap: Seq<T>,
    saved_len: nat,
) -> bool {
    &&& snap.len() == saved_len
    &&& saved_len <= view.len()
    &&& (forall|j: int| #![trigger snap[j]]
            0 <= j < saved_len as int ==> {
                if !diff_has_index::<T, I>(diffs, j as nat) {
                    // Uncaptured arm.
                    view[j] == snap[j]
                } else {
                    // Captured arm.
                    exists|k: int| 0 <= k < diffs.len()
                        && (#[trigger] diffs[k]).1.as_nat() == j as nat
                        && diffs[k].0 == snap[j]
                }
            })
}

// ---------------------------------------------------------------------------
// `overlay` -- the spec model of the restore loop
// ---------------------------------------------------------------------------
//
// The restore loop walks the diff log from `n` down to `lo`, applying each
// entry `(old, idx)` via `restore_entry`. Entries with `idx < base.len()`
// overwrite `base[idx]`; entries beyond `base.len()` are no-ops (the
// production restore_entry guard). Because the loop walks *downward*, the
// entry with the SMALLEST index in `[lo, hi)` that hits a given cell is
// applied LAST and therefore wins.
//
// `overlay(base, diffs, lo, hi)` is the recursive spec for this: apply
// `diffs[lo]` on top of `overlay(base, diffs, lo+1, hi)`, so the lower
// index ends up outermost (winning). This is exactly the loop's result.

/// Replay `diffs[lo..hi]` over `base` in reverse-index-wins order.
// ---------------------------------------------------------------------------
// Bare-log helpers (exec-first convergence, goal doc mainline-shape-plus-
// coldstack). The hot log is a bare `std::vec::Vec<(T, I)>` again - mainline's
// field - and these free functions carry the small verified surface the
// container and stores read it through. `log_hot_slice` always succeeds now
// (there is no cold region inside the log); the Option shape is kept so the
// call sites' fallback structure survives until the cold stack lands (A2b).

pub(crate) fn log_hot_slice<'a, T: Copy, I: IndexLike>(
    d: &'a std::vec::Vec<(T, I)>, lo: usize, hi: usize,
) -> (r: Option<&'a [(T, I)]>)
    requires lo <= hi <= d@.len(),
    ensures
        r is Some,
        r matches Some(sl) ==> sl@ == d@.subrange(lo as int, hi as int),
{
    Some(vstd::slice::slice_subrange(d.as_slice(), lo, hi))
}

pub(crate) fn log_subrange_vec<T: Copy, I: IndexLike>(
    d: &std::vec::Vec<(T, I)>, lo: usize, hi: usize,
) -> (r: std::vec::Vec<(T, I)>)
    requires lo <= hi <= d@.len(),
    ensures r@ == d@.subrange(lo as int, hi as int),
{
    let mut out: std::vec::Vec<(T, I)> = std::vec::Vec::new();
    let mut i: usize = lo;
    while i < hi
        invariant
            lo <= i <= hi,
            hi <= d@.len(),
            out@ =~= d@.subrange(lo as int, i as int),
        decreases hi - i,
    {
        out.push(d[i]);
        proof {
            assert(out@ =~= d@.subrange(lo as int, i as int + 1));
        }
        i += 1;
    }
    proof { assert(out@ =~= d@.subrange(lo as int, hi as int)); }
    out
}

pub(crate) fn log_index<T: Copy, I: IndexLike>(
    d: &std::vec::Vec<(T, I)>, i: usize,
) -> (e: (T, I))
    requires i < d@.len(),
    ensures e == d@[i as int],
{
    d[i]
}

pub(crate) fn log_index_range<T: Copy, I: IndexLike>(
    d: &std::vec::Vec<(T, I)>, lo: usize, hi: usize,
) -> (r: std::vec::Vec<I>)
    requires lo <= hi <= d@.len(),
    ensures
        r@.len() == hi - lo,
        forall|k: int| 0 <= k < r@.len() ==> #[trigger] r@[k] == d@[lo + k].1,
{
    let mut out: std::vec::Vec<I> = std::vec::Vec::new();
    let mut i: usize = lo;
    while i < hi
        invariant
            lo <= i <= hi,
            hi <= d@.len(),
            out@.len() == i - lo,
            forall|k: int| 0 <= k < i - lo ==> #[trigger] out@[k] == d@[lo + k].1,
        decreases hi - i,
    {
        let (_, idx) = d[i];
        out.push(idx);
        i += 1;
    }
    out
}

/// Diagnostic byte count of the bare log (capacity-based, mirrors the old
/// DiffLog::heap_bytes).
#[verifier::external_body]
pub(crate) fn log_heap_bytes<T: Copy, I: IndexLike>(d: &std::vec::Vec<(T, I)>) -> usize {
    d.capacity() * core::mem::size_of::<(T, I)>()
}

/// Capacity release for the bare log: shrink when capacity exceeds
/// `factor * len + headroom`. View-preserving; capacity is unmodeled.
#[verifier::external_body]
pub(crate) fn log_shrink_capacity<T: Copy, I: IndexLike>(
    d: &mut std::vec::Vec<(T, I)>, factor: usize, headroom: usize,
)
    ensures final(d)@ == old(d)@,
{
    let cap_target = d.len().saturating_mul(factor).saturating_add(headroom);
    if d.capacity() > cap_target {
        d.shrink_to(cap_target);
    }
}

/// Materialize the (value, index) pairs of cold frames [lo_f, hi_f) from
/// their runs, appended to `out`. EXEC-FIRST SCAFFOLD (inline-store flag
/// protocols only; never on the raw restore path).
#[verifier::external_body]
pub(crate) fn cold_pairs_scaffold<T: Copy, I: IndexLike>(
    cold_stack: &std::vec::Vec<crate::frame::ColdFrameHdr<I>>,
    runs: &std::vec::Vec<crate::frame::IndexRun<I>>,
    pool: &std::vec::Vec<T>,
    lo_f: usize, hi_f: usize, out: &mut std::vec::Vec<(T, I)>,
) {
    for f in lo_f..hi_f {
        let h = cold_stack[f];
        for r in h.runs_start..h.runs_start + h.runs_len {
            let run = runs[r];
            let b = run.base.as_usize();
            for q in 0..run.len {
                if let Some(ix) = I::try_from_usize(b + q) {
                    out.push((pool[run.start + q], ix));
                }
            }
        }
    }
}

/// Sorted iteration order for one frame slice, uniform for both capture
/// disciplines: keys are (index, position) with position in the low bits,
/// so an unstable sort is temporally exact and keep-first-per-cell is a
/// free adjacent compare during the walk (identity on unique input).
/// Packed u64 keys when the index width and frame length fit (measured
/// -9% unique / -20..-36% trail-shaped vs tuple sorts, normalize_bench);
/// wide indices fall back to a position sort by looked-up key. T is never
/// packed, compared, or moved here. EXEC-FIRST SCAFFOLD.
#[verifier::external_body]
pub(crate) fn frame_sort_order<T: Copy, I: IndexLike>(
    frame: &[(T, I)], keys: &mut std::vec::Vec<u64>, wide: &mut std::vec::Vec<usize>,
) -> bool {
    let n = frame.len();
    if n < u32::MAX as usize
        && <I as IndexLike>::max().as_usize() <= u32::MAX as usize
    {
        keys.clear();
        keys.extend(
            frame
                .iter()
                .enumerate()
                .map(|(j, p)| ((p.1.as_usize() as u64) << 32) | j as u64),
        );
        keys.sort_unstable();
        true
    } else {
        wide.clear();
        wide.extend(0..n);
        wide.sort_by_key(|&j| (frame[j].1.as_usize(), j));
        false
    }
}

/// Capacity release for the cold pools (ruled reclaim). EXEC-FIRST SCAFFOLD.
#[verifier::external_body]
pub(crate) fn cold_pools_shrink_scaffold<T: Copy, I: IndexLike>(
    values: &mut std::vec::Vec<T>,
    runs: &mut std::vec::Vec<crate::frame::IndexRun<I>>,
    factor: usize, headroom: usize,
) {
    let vt = values.len().saturating_mul(factor).saturating_add(headroom);
    if values.capacity() > vt {
        values.shrink_to(vt);
    }
    let rt = runs.len().saturating_mul(factor).saturating_add(headroom);
    if runs.capacity() > rt {
        runs.shrink_to(rt);
    }
}

/// Diagnostic: the index spans of the cold frames [lo_f, hi_f), expanded.
/// EXEC-FIRST SCAFFOLD.
#[verifier::external_body]
pub(crate) fn pending_cold_indices_scaffold<I: IndexLike>(
    cold_stack: &std::vec::Vec<crate::frame::ColdFrameHdr<I>>,
    runs: &std::vec::Vec<crate::frame::IndexRun<I>>,
    lo_f: usize, hi_f: usize, out: &mut std::vec::Vec<I>,
) {
    for f in lo_f..hi_f {
        let h = cold_stack[f];
        for r in h.runs_start..h.runs_start + h.runs_len {
            let run = runs[r];
            let b = run.base.as_usize();
            for q in 0..run.len {
                if let Some(ix) = I::try_from_usize(b + q) {
                    out.push(ix);
                }
            }
        }
    }
}

pub open(crate) spec fn overlay<T, I: IndexLike>(
    base: Seq<T>,
    diffs: Seq<(T, I)>,
    lo: int,
    hi: int,
) -> Seq<T>
    decreases hi - lo
{
    if lo >= hi || lo < 0 || hi > diffs.len() {
        base
    } else {
        let prev = overlay(base, diffs, lo + 1, hi);
        let d = diffs[lo];
        if d.1.as_nat() < prev.len() {
            prev.update(d.1.as_nat() as int, d.0)
        } else {
            prev
        }
    }
}

/// `overlay` preserves the base length (it only updates, never grows).
pub(crate) proof fn lemma_overlay_len<T, I: IndexLike>(
    base: Seq<T>, diffs: Seq<(T, I)>, lo: int, hi: int,
)
    ensures overlay::<T, I>(base, diffs, lo, hi).len() == base.len(),
    decreases hi - lo,
{
    if lo >= hi || lo < 0 || hi > diffs.len() {
    } else {
        lemma_overlay_len::<T, I>(base, diffs, lo + 1, hi);
    }
}

/// If no entry in `[lo, hi)` hits cell `j`, overlay leaves `base[j]` alone.
pub(crate) proof fn lemma_overlay_uncaptured<T, I: IndexLike>(
    base: Seq<T>, diffs: Seq<(T, I)>, lo: int, hi: int, j: int,
)
    requires
        0 <= j < base.len(),
        forall|k: int| lo <= k < hi && 0 <= k < diffs.len()
            ==> (#[trigger] diffs[k]).1.as_nat() != j as nat,
    ensures
        overlay::<T, I>(base, diffs, lo, hi)[j] == base[j],
    decreases hi - lo,
{
    if lo >= hi || lo < 0 || hi > diffs.len() {
    } else {
        lemma_overlay_uncaptured::<T, I>(base, diffs, lo + 1, hi, j);
        lemma_overlay_len::<T, I>(base, diffs, lo + 1, hi);
        // diffs[lo].1 != j, so the update at lo (if any) doesn't touch j.
    }
}

/// If `[lo, hi)` has unique indices and the entry at position `p` hits `j`,
/// then overlay sets `base[j]` to that entry's value — regardless of base,
/// because the winning entry is the unique one.
pub(crate) proof fn lemma_overlay_captured<T, I: IndexLike>(
    base: Seq<T>, diffs: Seq<(T, I)>, lo: int, hi: int, p: int, j: int,
)
    requires
        0 <= j < base.len(),
        lo <= p < hi,
        0 <= p < diffs.len(),
        lo >= 0,
        hi <= diffs.len(),
        diffs[p].1.as_nat() == j as nat,
        // unique within [lo, hi)
        forall|a: int, b: int|
            lo <= a < hi && lo <= b < hi && a != b
                ==> (#[trigger] diffs[a]).1.as_nat() != (#[trigger] diffs[b]).1.as_nat(),
    ensures
        overlay::<T, I>(base, diffs, lo, hi)[j] == diffs[p].0,
    decreases hi - lo,
{
    let prev = overlay::<T, I>(base, diffs, lo + 1, hi);
    lemma_overlay_len::<T, I>(base, diffs, lo + 1, hi);
    if p == lo {
        // Entry at lo wins (applied last/outermost). All entries in
        // [lo+1, hi) have different indices from j (uniqueness), so they
        // don't matter — the final update at lo sets j.
    } else {
        // p in [lo+1, hi). By IH, overlay(lo+1, hi)[j] == diffs[p].0.
        lemma_overlay_captured::<T, I>(base, diffs, lo + 1, hi, p, j);
        // The update at lo has index diffs[lo].1 != j (uniqueness, lo != p),
        // so it doesn't disturb j.
    }
}

/// Lowest-position-in-range wins. If `p` is the LOWEST position in `[lo, hi)`
/// whose entry hits `j` (entries before `p` miss `j`), then overlay sets
/// `base[j]` to `diffs[p].0` — even if higher positions in `[lo, hi)` also
/// hit `j`. This generalizes `lemma_overlay_captured` (which needs global
/// uniqueness in the range) to the cross-stratum case where the same index
/// recurs in different strata: the deepest (= lowest-position) stratum's
/// entry wins, which is exactly what reverse-replay computes.
pub(crate) proof fn lemma_overlay_lowest<T, I: IndexLike>(
    base: Seq<T>, diffs: Seq<(T, I)>, lo: int, hi: int, p: int, j: int,
)
    requires
        0 <= j < base.len(),
        lo <= p < hi,
        0 <= p < diffs.len(),
        lo >= 0,
        hi <= diffs.len(),
        diffs[p].1.as_nat() == j as nat,
        // p is the LOWEST hitter of j in [lo, hi): earlier positions miss j.
        forall|q: int| lo <= q < p ==> (#[trigger] diffs[q]).1.as_nat() != j as nat,
    ensures
        overlay::<T, I>(base, diffs, lo, hi)[j] == diffs[p].0,
    decreases hi - lo,
{
    let prev = overlay::<T, I>(base, diffs, lo + 1, hi);
    lemma_overlay_len::<T, I>(base, diffs, lo + 1, hi);
    if p == lo {
        // diffs[lo] hits j; it is applied OUTERMOST (last), so its value is
        // the final value at j regardless of what [lo+1, hi) did to prev[j].
    } else {
        // diffs[lo] does not hit j (lo < p and p is the lowest hitter).
        // p is still the lowest hitter in [lo+1, hi). By IH overlay(lo+1,hi)[j]
        // == diffs[p].0, and the outermost update at lo (index != j) leaves j.
        lemma_overlay_lowest::<T, I>(base, diffs, lo + 1, hi, p, j);
    }
}

/// A captured cell has a LOWEST hitter: walk down from any witness. The
/// min-witness `lemma_overlay_lowest` and `frame_cell_inv`'s captured arm
/// consume.
pub(crate) proof fn lemma_lowest_hitter<T, I: IndexLike>(
    diffs: Seq<(T, I)>, lo: int, hi: int, j: nat,
)
    requires
        0 <= lo,
        hi <= diffs.len(),
        captured_in_range::<T, I>(diffs, lo, hi, j),
    ensures
        exists|p: int| lo <= p < hi
            && (#[trigger] diffs[p]).1.as_nat() == j
            && first_hitter::<T, I>(diffs, lo, p, j),
    decreases hi - lo,
{
    if diffs[lo].1.as_nat() == j {
        assert(first_hitter::<T, I>(diffs, lo, lo, j));
    } else {
        let w = choose|k: int| lo <= k < hi && 0 <= k < diffs.len()
            && (#[trigger] diffs[k]).1.as_nat() == j;
        assert(captured_in_range::<T, I>(diffs, lo + 1, hi, j));
        lemma_lowest_hitter::<T, I>(diffs, lo + 1, hi, j);
        let p = choose|p: int| (lo + 1) <= p < hi
            && (#[trigger] diffs[p]).1.as_nat() == j
            && first_hitter::<T, I>(diffs, lo + 1, p, j);
        assert(first_hitter::<T, I>(diffs, lo, p, j));
    }
}

/// Restore-equivalence of dedupe-first (design doc §7, deliverable 5's
/// lemma): `overlay` applies a stratum backward, so the chronologically
/// first capture of each cell wins; dropping every later duplicate
/// preserves the result exactly.
pub(crate) proof fn lemma_overlay_dedupe_first<T, I: IndexLike>(
    base: Seq<T>, d: Seq<(T, I)>,
)
    ensures
        overlay::<T, I>(base, d, 0, d.len() as int)
            == overlay::<T, I>(
                base,
                crate::diff_compress::dedupe_first_spec(d),
                0,
                crate::diff_compress::dedupe_first_spec(d).len() as int),
{
    let r = crate::diff_compress::dedupe_first_spec(d);
    let rp = crate::diff_compress::dedupe_positions(d, d.len() as int);
    crate::diff_compress::lemma_dedupe_prefix_props::<T, I>(d, d.len() as int);
    let od = overlay::<T, I>(base, d, 0, d.len() as int);
    let or = overlay::<T, I>(base, r, 0, r.len() as int);
    lemma_overlay_len::<T, I>(base, d, 0, d.len() as int);
    lemma_overlay_len::<T, I>(base, r, 0, r.len() as int);
    assert forall|j: int| 0 <= j < base.len() implies od[j] == or[j] by {
        if captured_in_range::<T, I>(d, 0, d.len() as int, j as nat) {
            lemma_lowest_hitter::<T, I>(d, 0, d.len() as int, j as nat);
            let p = choose|p: int| 0 <= p < d.len()
                && (#[trigger] d[p]).1.as_nat() == j as nat
                && first_hitter::<T, I>(d, 0, p, j as nat);
            lemma_overlay_lowest::<T, I>(base, d, 0, d.len() as int, p, j);
            // The first hitter is kept; in `r` it is the ONLY hitter of j,
            // hence trivially the lowest.
            assert(first_hitter::<T, I>(d, 0, p, d[p].1.as_nat()));
            assert(rp.contains(p));
            let t = choose|t: int| 0 <= t < rp.len() && #[trigger] rp[t] == p;
            assert(r[t] == d[p]);
            assert forall|q: int| 0 <= q < t implies
                (#[trigger] r[q]).1.as_nat() != j as nat by {
                if r[q].1.as_nat() == j as nat {
                    assert(r[q].1.as_nat() == r[t].1.as_nat());
                }
            }
            lemma_overlay_lowest::<T, I>(base, r, 0, r.len() as int, t, j);
        } else {
            // No hitter in d, and every entry of r is some d entry, so no
            // hitter in r either.
            assert forall|q: int| 0 <= q < r.len() implies
                (#[trigger] r[q]).1.as_nat() != j as nat by {
                if r[q].1.as_nat() == j as nat {
                    let pq = rp[q];
                    assert(r[q] == d[pq]);
                    assert(captured_in_range::<T, I>(
                        d, 0, d.len() as int, j as nat));
                }
            }
            lemma_overlay_uncaptured::<T, I>(base, d, 0, d.len() as int, j);
            lemma_overlay_uncaptured::<T, I>(base, r, 0, r.len() as int, j);
        }
    }
    assert(od =~= or);
}

/// If no entry in the lower part `[lo, mid)` hits `j`, then overlaying the
/// whole `[lo, hi)` agrees at `j` with overlaying just the upper part
/// `[mid, hi)`. (The lower-part replay, applied outermost, leaves `j` alone.)
/// Used by the flat central lemma's uncaptured/recurse step.
pub(crate) proof fn lemma_overlay_uncaptured_prefix<T, I: IndexLike>(
    base: Seq<T>, diffs: Seq<(T, I)>, lo: int, mid: int, hi: int, j: int,
)
    requires
        0 <= lo <= mid <= hi <= diffs.len(),
        0 <= j < base.len(),
        forall|q: int| lo <= q < mid ==> (#[trigger] diffs[q]).1.as_nat() != j as nat,
    ensures
        overlay::<T, I>(base, diffs, lo, hi)[j]
            == overlay::<T, I>(base, diffs, mid, hi)[j],
    decreases mid - lo,
{
    lemma_overlay_len::<T, I>(base, diffs, mid, hi);
    if lo >= mid {
        // [lo, mid) empty ⇒ both sides identical.
    } else {
        // Peel lo: overlay(lo,hi) = step(diffs[lo], overlay(lo+1,hi)). By IH
        // overlay(lo+1,hi)[j] == overlay(mid,hi)[j]; diffs[lo] misses j so the
        // outermost step leaves j.
        lemma_overlay_uncaptured_prefix::<T, I>(base, diffs, lo + 1, mid, hi, j);
        lemma_overlay_len::<T, I>(base, diffs, lo + 1, hi);
    }
}

/// Every entry in the frame names a distinct index. This is the first-write-wins
/// invariant of a finalized frame, and it is what makes reordering the frame
/// sound: with unique indices, `overlay` writes each cell exactly once, so the
/// restored state depends only on the index->value map, not the entry order.
pub open(crate) spec fn unique_idx<T, I: IndexLike>(d: Seq<(T, I)>) -> bool {
    forall|a: int, b: int|
        0 <= a < d.len() && 0 <= b < d.len() && a != b
            ==> (#[trigger] d[a]).1.as_nat() != (#[trigger] d[b]).1.as_nat()
}

/// Frame `d` names index `j` somewhere. The trigger handle for the same-map
/// hypothesis of `lemma_overlay_same_map`.
pub open(crate) spec fn frame_covers<T, I: IndexLike>(d: Seq<(T, I)>, j: nat) -> bool {
    exists|k: int| 0 <= k < d.len() && (#[trigger] d[k]).1.as_nat() == j
}

/// SET-LEVEL RESTORE EQUIVALENCE. Two finalized frames with unique indices that
/// define the same index->value map (same covered indices, agreeing values)
/// overlay to the same result over any base. This is what licenses a compression
/// scheme to REORDER a frame (e.g. sort it by index for longer runs): the sorted
/// frame is a permutation of the original, so it has the same map, so it restores
/// identically. Proof is pointwise via `lemma_overlay_captured` (covered cells
/// take the unique hitter's value) and `lemma_overlay_uncaptured` (uncovered
/// cells keep the base), then extensionality.
pub(crate) proof fn lemma_overlay_same_map<T, I: IndexLike>(
    base: Seq<T>, d1: Seq<(T, I)>, d2: Seq<(T, I)>,
)
    requires
        unique_idx(d1),
        unique_idx(d2),
        // Same covered indices.
        forall|j: nat| #![trigger frame_covers(d1, j)]
            j < base.len() ==> frame_covers(d1, j) == frame_covers(d2, j),
        // Agreeing values wherever an index is shared.
        forall|k1: int, k2: int|
            0 <= k1 < d1.len() && 0 <= k2 < d2.len()
                && (#[trigger] d1[k1]).1.as_nat() == (#[trigger] d2[k2]).1.as_nat()
            ==> d1[k1].0 == d2[k2].0,
    ensures
        overlay::<T, I>(base, d1, 0, d1.len() as int)
            == overlay::<T, I>(base, d2, 0, d2.len() as int),
{
    lemma_overlay_len::<T, I>(base, d1, 0, d1.len() as int);
    lemma_overlay_len::<T, I>(base, d2, 0, d2.len() as int);
    assert forall|j: int| 0 <= j < base.len() implies
        overlay::<T, I>(base, d1, 0, d1.len() as int)[j]
            == overlay::<T, I>(base, d2, 0, d2.len() as int)[j] by {
        // Instantiate the same-covered-indices hypothesis at j.
        assert(frame_covers(d1, j as nat) == frame_covers(d2, j as nat));
        if frame_covers(d1, j as nat) {
            let k1 = choose|k1: int| 0 <= k1 < d1.len() && (#[trigger] d1[k1]).1.as_nat() == j as nat;
            let k2 = choose|k2: int| 0 <= k2 < d2.len() && (#[trigger] d2[k2]).1.as_nat() == j as nat;
            lemma_overlay_captured::<T, I>(base, d1, 0, d1.len() as int, k1, j);
            lemma_overlay_captured::<T, I>(base, d2, 0, d2.len() as int, k2, j);
            // Values agree because both entries name index j.
            assert(d1[k1].0 == d2[k2].0);
        } else {
            lemma_overlay_uncaptured::<T, I>(base, d1, 0, d1.len() as int, j);
            lemma_overlay_uncaptured::<T, I>(base, d2, 0, d2.len() as int, j);
        }
    }
    assert(overlay::<T, I>(base, d1, 0, d1.len() as int)
        =~= overlay::<T, I>(base, d2, 0, d2.len() as int));
}

/// THE CODEC CONTRACT, formalized. Two finalized frames with unique indices and
/// the SAME MULTISET OF WRITES restore identically over any base. This is the one
/// invariant every codec must preserve: `decode(encode(d))` need only carry the
/// same set of `(value, index)` writes as `d` — order is irrelevant because each
/// cell is written at most once per frame (first-write-wins), so the multiset is a
/// map and the restore is that map applied. Reduces to `lemma_overlay_same_map`
/// by deriving same-covered-indices and value-agreement from multiset equality:
/// a shared write is `contains`-equal on both sides (equal multisets ⇒ equal
/// counts ⇒ equal membership), and a shared index forces the SAME pair on both
/// sides, else the two distinct pairs at one index break `unique_idx`.
pub(crate) proof fn lemma_multiset_eq_overlay<T, I: IndexLike>(
    base: Seq<T>, d1: Seq<(T, I)>, d2: Seq<(T, I)>,
)
    requires
        unique_idx(d1),
        unique_idx(d2),
        d1.to_multiset() == d2.to_multiset(),
    ensures
        overlay::<T, I>(base, d1, 0, d1.len() as int)
            == overlay::<T, I>(base, d2, 0, d2.len() as int),
{
    // `x` present in `d1` is present in `d2` (equal multisets ⇒ equal counts ⇒
    // equal membership), and vice versa.
    assert forall|x: (T, I)| d1.contains(x) implies d2.contains(x) by {
        vstd::seq_lib::to_multiset_contains(d1, x);
        vstd::seq_lib::to_multiset_contains(d2, x);
    }
    assert forall|x: (T, I)| d2.contains(x) implies d1.contains(x) by {
        vstd::seq_lib::to_multiset_contains(d1, x);
        vstd::seq_lib::to_multiset_contains(d2, x);
    }
    // Same covered indices: a covering entry is present on both sides.
    assert forall|j: nat| #![trigger frame_covers(d1, j)]
        j < base.len() implies frame_covers(d1, j) == frame_covers(d2, j) by {
        if frame_covers(d1, j) {
            let k = choose|k: int| 0 <= k < d1.len() && (#[trigger] d1[k]).1.as_nat() == j;
            assert(d1.contains(d1[k]));
            let k2 = choose|k2: int| 0 <= k2 < d2.len() && d2[k2] == d1[k];
            assert(d2[k2].1.as_nat() == j);
        }
        if frame_covers(d2, j) {
            let k = choose|k: int| 0 <= k < d2.len() && (#[trigger] d2[k]).1.as_nat() == j;
            assert(d2.contains(d2[k]));
            let k1 = choose|k1: int| 0 <= k1 < d1.len() && d1[k1] == d2[k];
            assert(d1[k1].1.as_nat() == j);
        }
    }
    // Value agreement: if entries on the two sides share an index, they are the
    // same pair — otherwise both distinct pairs sit at that index in one frame
    // (each is present in the other, by multiset equality), breaking uniqueness.
    assert forall|k1: int, k2: int|
        0 <= k1 < d1.len() && 0 <= k2 < d2.len()
            && (#[trigger] d1[k1]).1.as_nat() == (#[trigger] d2[k2]).1.as_nat()
        implies d1[k1].0 == d2[k2].0 by {
        assert(d1.contains(d1[k1]));
        let q = choose|q: int| 0 <= q < d2.len() && d2[q] == d1[k1];
        // q and k2 both name index j in d2; uniqueness forces q == k2, so the
        // pair at k2 equals d1[k1].
        if q != k2 {
            assert(d2[q].1.as_nat() == d2[k2].1.as_nat());  // both == j
            assert(false);
        }
    }
    lemma_overlay_same_map::<T, I>(base, d1, d2);
}

/// Bridge between subrange-position existential and absolute-range
/// `captured_in_range`. If `sub == diffs.subrange(lo, hi)`, then
/// "some sub[kk] hits j" iff "some diffs[k] in [lo, hi) hits j".
pub(crate) proof fn lemma_captured_subrange<T, I: IndexLike>(
    diffs: Seq<(T, I)>, sub: Seq<(T, I)>, lo: int, hi: int, j: nat,
)
    requires
        0 <= lo <= hi <= diffs.len(),
        sub == diffs.subrange(lo, hi),
    ensures
        (exists|kk: int| 0 <= kk < sub.len()
            && (#[trigger] sub[kk]).1.as_nat() == j)
        == captured_in_range::<T, I>(diffs, lo, hi, j),
{
    if exists|kk: int| 0 <= kk < sub.len() && (#[trigger] sub[kk]).1.as_nat() == j {
        let kk = choose|kk: int| 0 <= kk < sub.len() && (#[trigger] sub[kk]).1.as_nat() == j;
        // sub[kk] == diffs[lo + kk], and lo <= lo+kk < hi.
        assert(sub[kk] == diffs[lo + kk]);
        assert(lo <= lo + kk < hi);
    }
    if captured_in_range::<T, I>(diffs, lo, hi, j) {
        let k = choose|k: int| lo <= k < hi && 0 <= k < diffs.len()
            && (#[trigger] diffs[k]).1.as_nat() == j;
        // diffs[k] == sub[k - lo], and 0 <= k-lo < sub.len().
        assert(sub[k - lo] == diffs[k]);
        assert(0 <= k - lo < sub.len());
    }
}

/// Index-column variant of `lemma_captured_subrange`. `idx_sub` is the INDEX
/// projection of the stratum `diffs[lo..hi]` (what `DiffLog::indices()` slices
/// out), so its entries are `I`s compared with `.as_nat()`, not `(T, I)` pairs.
/// Same conclusion: membership in the index slice matches `captured_in_range`.
pub(crate) proof fn lemma_captured_subrange_idx<T, I: IndexLike>(
    diffs: Seq<(T, I)>, idx_sub: Seq<I>, lo: int, hi: int, j: nat,
)
    requires
        0 <= lo <= hi <= diffs.len(),
        idx_sub.len() == hi - lo,
        forall|m: int| 0 <= m < idx_sub.len() ==> (#[trigger] idx_sub[m]) == diffs[lo + m].1,
    ensures
        (exists|kk: int| 0 <= kk < idx_sub.len()
            && (#[trigger] idx_sub[kk]).as_nat() == j)
        == captured_in_range::<T, I>(diffs, lo, hi, j),
{
    if exists|kk: int| 0 <= kk < idx_sub.len() && (#[trigger] idx_sub[kk]).as_nat() == j {
        let kk = choose|kk: int| 0 <= kk < idx_sub.len() && (#[trigger] idx_sub[kk]).as_nat() == j;
        // idx_sub[kk] == diffs[lo + kk].1, and lo <= lo+kk < hi.
        assert(idx_sub[kk] == diffs[lo + kk].1);
        assert(lo <= lo + kk < hi);
    }
    if captured_in_range::<T, I>(diffs, lo, hi, j) {
        let k = choose|k: int| lo <= k < hi && 0 <= k < diffs.len()
            && (#[trigger] diffs[k]).1.as_nat() == j;
        // idx_sub[k - lo] == diffs[k].1, and 0 <= k-lo < idx_sub.len().
        assert(idx_sub[k - lo] == diffs[k].1);
        assert(0 <= k - lo < idx_sub.len());
    }
}

/// Appending at most one entry whose index is `bound` (the popped slot) to
/// the top stratum doesn't change captured-status of any OTHER index `j`
/// (`j != bound`). Used by `pop` into the marked region: the capture append hits only the
/// popped index, so every surviving cell's bridge/captured arm is preserved.
/// `diffs` is either `old_diffs` (no-op capture) or `old_diffs.push(e)` with
/// `e.1.as_nat() == bound`.
pub(crate) proof fn lemma_captured_in_range_append_other<T, I: IndexLike>(
    old_diffs: Seq<(T, I)>, diffs: Seq<(T, I)>, lo: int, j: nat, bound: nat,
)
    requires
        j != bound,
        lo <= old_diffs.len(),
        diffs == old_diffs
            || (diffs.len() == old_diffs.len() + 1
                && diffs.subrange(0, old_diffs.len() as int) == old_diffs
                && (#[trigger] diffs[old_diffs.len() as int]).1.as_nat() == bound),
    ensures
        captured_in_range::<T, I>(diffs, lo, diffs.len() as int, j)
            == captured_in_range::<T, I>(old_diffs, lo, old_diffs.len() as int, j),
{
    if diffs == old_diffs {
        return;
    }
    let n = old_diffs.len() as int;
    // forward: a hitter in diffs is at some position p; if p == n it has
    // index bound != j, contradiction; else p < n and diffs[p]==old_diffs[p].
    if captured_in_range::<T, I>(diffs, lo, diffs.len() as int, j) {
        let p = choose|p: int| lo <= p < diffs.len() && 0 <= p < diffs.len()
            && (#[trigger] diffs[p]).1.as_nat() == j;
        if p < n {
            assert(diffs[p] == old_diffs[p]) by {
                assert(diffs.subrange(0, n)[p] == old_diffs[p]);
            }
        } else {
            assert(p == n);
            assert(diffs[p].1.as_nat() == bound);  // contradicts == j
        }
    }
    // backward: an old hitter at p < n survives at the same position.
    if captured_in_range::<T, I>(old_diffs, lo, n, j) {
        let p = choose|p: int| lo <= p < n && 0 <= p < old_diffs.len()
            && (#[trigger] old_diffs[p]).1.as_nat() == j;
        assert(diffs[p] == old_diffs[p]) by {
            assert(diffs.subrange(0, n)[p] == old_diffs[p]);
        }
    }
}

/// `frame_inv_range` over `[lo, hi)` depends only on the diff entries in
/// that range. If two diff sequences agree pointwise on `[lo, hi)` (and are
/// both long enough), the predicate holds for one iff for the other.
pub(crate) proof fn lemma_frame_inv_range_local<T, I: IndexLike>(
    above: Seq<T>, da: Seq<(T, I)>, db: Seq<(T, I)>,
    lo: int, hi: int, snap: Seq<T>, saved_len: nat,
)
    requires
        0 <= lo <= hi <= da.len(),
        hi <= db.len(),
        forall|m: int| lo <= m < hi ==> #[trigger] da[m] == db[m],
        frame_inv_range::<T, I>(above, da, lo, hi, snap, saved_len),
    ensures
        frame_inv_range::<T, I>(above, db, lo, hi, snap, saved_len),
{
    // Structural conjunct: the index-bound forall reads entries only in
    // [lo, hi), where da and db agree.
    assert forall|m: int| lo <= m < hi implies
        (#[trigger] db[m]).1.as_nat() < saved_len by { assert(da[m] == db[m]); }
    // Per-cell two-arm: frame_cell_inv reads only entries in [lo, hi) plus
    // `above`/`snap` (shared). The named predicate gives a clean function-
    // application trigger that re-assembles into frame_inv_range's forall.
    assert forall|j: int| 0 <= j < saved_len as int implies
        #[trigger] frame_cell_inv::<T, I>(above, db, lo, hi, snap, j)
    by {
        lemma_frame_cell_inv_local::<T, I>(above, da, db, lo, hi, snap, j);
    }
}

/// `frame_cell_inv` for cell `j` depends only on entries in `[lo, hi)`. If
/// `da`/`db` agree there, the per-cell invariant transfers. Isolated so the
/// quantifier instantiation is local and the equality is by function
/// congruence on `captured_in_range` + the witness entry.
pub(crate) proof fn lemma_frame_cell_inv_local<T, I: IndexLike>(
    above: Seq<T>, da: Seq<(T, I)>, db: Seq<(T, I)>,
    lo: int, hi: int, snap: Seq<T>, j: int,
)
    requires
        0 <= lo <= hi <= da.len(),
        hi <= db.len(),
        forall|m: int| lo <= m < hi ==> #[trigger] da[m] == db[m],
        frame_cell_inv::<T, I>(above, da, lo, hi, snap, j),
    ensures
        frame_cell_inv::<T, I>(above, db, lo, hi, snap, j),
{
    // captured_in_range agrees across da/db (reads entries in [lo, hi)).
    assert(captured_in_range::<T, I>(db, lo, hi, j as nat)
        == captured_in_range::<T, I>(da, lo, hi, j as nat)) by {
        if captured_in_range::<T, I>(db, lo, hi, j as nat) {
            let w = choose|k: int| lo <= k < hi && 0 <= k < db.len()
                && (#[trigger] db[k]).1.as_nat() == j as nat;
            assert(da[w] == db[w]);
        }
        if captured_in_range::<T, I>(da, lo, hi, j as nat) {
            let w = choose|k: int| lo <= k < hi && 0 <= k < da.len()
                && (#[trigger] da[k]).1.as_nat() == j as nat;
            assert(da[w] == db[w]);
        }
    }
    if captured_in_range::<T, I>(db, lo, hi, j as nat) {
        // Carry the first-hitter witness from da to db: same position, equal
        // entry, and the miss-everything-below-it forall reads only entries
        // in [lo, w) where the two sequences agree.
        let w = choose|k: int| lo <= k < hi
            && (#[trigger] da[k]).1.as_nat() == j as nat && da[k].0 == snap[j]
            && first_hitter::<T, I>(da, lo, k, j as nat);
        assert(da[w] == db[w]);
        assert forall|q: int| lo <= q < w implies
            (#[trigger] db[q]).1.as_nat() != j as nat by {
            assert(da[q] == db[q]);
        }
        assert(first_hitter::<T, I>(db, lo, w, j as nat));
    }
}

/// `overlay`'s value at `j < bound` depends only on `base`'s prefix
/// `[0, bound)` and on entries whose index is `< bound`. Concretely: if two
/// bases agree on `[0, bound)`, then their overlays agree on `[0, bound)`,
/// regardless of base values or entry indices `>= bound`.
///
/// This is what lets restore overlay onto the *truncated* base (length
/// saved_len) and still match `overlay` onto the full view on the marked
/// region: entries with idx >= saved_len are no-ops on `[0, saved_len)`.
pub(crate) proof fn lemma_overlay_prefix_agnostic<T, I: IndexLike>(
    base_a: Seq<T>, base_b: Seq<T>, diffs: Seq<(T, I)>, lo: int, hi: int, bound: int,
)
    requires
        0 <= bound <= base_a.len(),
        0 <= bound <= base_b.len(),
        forall|j: int| 0 <= j < bound ==> #[trigger] base_a[j] == base_b[j],
    ensures
        forall|j: int| 0 <= j < bound ==>
            #[trigger] overlay::<T, I>(base_a, diffs, lo, hi)[j]
                == overlay::<T, I>(base_b, diffs, lo, hi)[j],
    decreases hi - lo,
{
    lemma_overlay_len::<T, I>(base_a, diffs, lo, hi);
    lemma_overlay_len::<T, I>(base_b, diffs, lo, hi);
    if lo >= hi || lo < 0 || hi > diffs.len() {
    } else {
        lemma_overlay_prefix_agnostic::<T, I>(base_a, base_b, diffs, lo + 1, hi, bound);
        lemma_overlay_len::<T, I>(base_a, diffs, lo + 1, hi);
        lemma_overlay_len::<T, I>(base_b, diffs, lo + 1, hi);
        // The step at lo updates index diffs[lo].1 in both. For j < bound:
        // if diffs[lo].1 == j and j < both prevs' len, both get diffs[lo].0;
        // otherwise both inherit prev[j], equal by IH.
    }
}

/// `overlay` splits at any midpoint: applying `[lo, hi)` equals applying
/// the upper part `[mid, hi)` first, then the lower part `[lo, mid)` on top.
/// This is what lets us peel strata one at a time.
pub(crate) proof fn lemma_overlay_split<T, I: IndexLike>(
    base: Seq<T>, diffs: Seq<(T, I)>, lo: int, mid: int, hi: int,
)
    requires
        0 <= lo <= mid <= hi <= diffs.len(),
    ensures
        overlay::<T, I>(base, diffs, lo, hi)
            == overlay::<T, I>(overlay::<T, I>(base, diffs, mid, hi), diffs, lo, mid),
    decreases mid - lo,
{
    if lo >= mid {
        // [lo, mid) empty: RHS inner overlay is identity, so both sides
        // are overlay(base, mid, hi) == overlay(base, lo, hi) since lo==mid.
    } else {
        // Peel lo off both sides.
        //   LHS = step(diffs[lo], overlay(base, lo+1, hi))
        //   RHS = step(diffs[lo], overlay(overlay(base, mid, hi), lo+1, mid))
        // By IH on (lo+1, mid, hi): overlay(base, lo+1, hi)
        //   == overlay(overlay(base, mid, hi), lo+1, mid).
        // So the two `step` arguments coincide and the results match.
        lemma_overlay_split::<T, I>(base, diffs, lo + 1, mid, hi);
    }
}

/// Range-based "captured": some entry in `diffs[lo..hi)` hits `j`.
pub open(crate) spec fn captured_in_range<T, I: IndexLike>(
    diffs: Seq<(T, I)>, lo: int, hi: int, j: nat,
) -> bool {
    exists|k: int| lo <= k < hi && 0 <= k < diffs.len()
        && (#[trigger] diffs[k]).1.as_nat() == j
}

/// Per-cell two-arm invariant for cell `j` of stratum `[lo, hi)`.
///
/// Factored into a named predicate (rather than inlined in the forall) so
/// the `forall|j|` in `frame_inv_range` has a clean function-application
/// trigger that Verus can re-assemble reliably across diff-log changes.
///
/// Coverage-aware uncaptured arm: an uncaptured cell `j` must be *present*
/// in `above` (`j < above.len()`) and hold the snapshot value. Equivalently,
/// every cell `j` in `[above.len(), saved_len)` — popped out of `above` —
/// must be captured. That's what lets `restore` regrow the popped region with
/// `resize_default` and overwrite every filler back to `snap[j]`.
pub open(crate) spec fn frame_cell_inv<T, I: IndexLike>(
    above: Seq<T>, diffs: Seq<(T, I)>, lo: int, hi: int,
    snap: Seq<T>, j: int,
) -> bool {
    if !captured_in_range::<T, I>(diffs, lo, hi, j as nat) {
        &&& (j as nat) < above.len()
        &&& above[j] == snap[j]
    } else {
        // FIRST-hitter form: the chronologically first entry for `j` in the
        // stratum holds the snapshot value. Under the unique discipline this
        // is the old "some entry" form (the one entry is trivially first);
        // under the chronological (trail) discipline it is the load-bearing
        // strengthening: `overlay` is first-entry-wins, so reconstruction
        // needs exactly the FIRST entry pinned, and later duplicates (which
        // hold intermediate values) are inert.
        exists|k: int| lo <= k < hi
            && (#[trigger] diffs[k]).1.as_nat() == j as nat
            && diffs[k].0 == snap[j]
            && first_hitter::<T, I>(diffs, lo, k, j as nat)
    }
}

/// No entry in `[lo, k)` hits `j`: position `k`'s entry is the stratum's
/// first hitter of `j`. The witness shape `lemma_overlay_lowest` consumes.
pub open(crate) spec fn first_hitter<T, I: IndexLike>(
    diffs: Seq<(T, I)>, lo: int, k: int, j: nat,
) -> bool {
    forall|q: int| lo <= q < k ==> (#[trigger] diffs[q]).1.as_nat() != j
}

/// At most one entry per cell in `[lo, hi)`: the unique capture discipline's
/// per-stratum guarantee. Holds for every stratum of a column whose store
/// answers `unique_capture_spec()` (a `Vec::wf` clause); the sealing and
/// reordering paths require it, reconstruction does not.
pub open(crate) spec fn stratum_unique<T, I: IndexLike>(
    diffs: Seq<(T, I)>, lo: int, hi: int,
) -> bool {
    forall|a: int, b: int| lo <= a < hi && lo <= b < hi && a != b
        ==> (#[trigger] diffs[a]).1.as_nat() != (#[trigger] diffs[b]).1.as_nat()
}

/// Range-form of the two-arm frame invariant for one stratum `[lo, hi)`.
/// `above` is the layer above (snapshot[k+1] or the view); `snap` is this
/// stratum's snapshot. Stated over the diff-log range directly.
///
/// Note: no `saved_len <= above.len()` requirement — `above` (the view, for
/// the top frame) may be shorter than `saved_len` in the post-pop state. The
/// coverage clause inside `frame_cell_inv` handles the popped cells.
pub open(crate) spec fn frame_inv_range<T, I: IndexLike>(
    above: Seq<T>, diffs: Seq<(T, I)>, lo: int, hi: int,
    snap: Seq<T>, saved_len: nat,
) -> bool {
    &&& snap.len() == saved_len
    &&& (forall|k: int| lo <= k < hi ==>
            (#[trigger] diffs[k]).1.as_nat() < saved_len)
    &&& (forall|j: int| 0 <= j < saved_len as int ==>
            #[trigger] frame_cell_inv::<T, I>(above, diffs, lo, hi, snap, j))
}

/// Instantiate `frame_inv_range`'s per-cell forall at one cell `j`. The
/// forall's trigger is `frame_cell_inv(...)`, so this is just an explicit
/// hook for call sites that need the per-cell fact in hand.
pub(crate) proof fn lemma_frame_inv_arm_at<T, I: IndexLike>(
    above: Seq<T>, diffs: Seq<(T, I)>, lo: int, hi: int,
    snap: Seq<T>, saved_len: nat, j: int,
)
    requires
        frame_inv_range::<T, I>(above, diffs, lo, hi, snap, saved_len),
        0 <= j < saved_len as int,
    ensures
        frame_cell_inv::<T, I>(above, diffs, lo, hi, snap, j),
{
}

/// `stratum_unique` transfers between diff logs that agree pointwise on the
/// stratum `[lo, hi)` (covers both an extension and a truncation whose
/// surviving prefix contains the stratum).
pub(crate) proof fn lemma_stratum_unique_local<T, I: IndexLike>(
    da: Seq<(T, I)>, db: Seq<(T, I)>, lo: int, hi: int,
)
    requires
        0 <= lo <= hi,
        hi <= da.len(),
        hi <= db.len(),
        forall|q: int| lo <= q < hi ==> #[trigger] db[q] == da[q],
        stratum_unique::<T, I>(da, lo, hi),
    ensures
        stratum_unique::<T, I>(db, lo, hi),
{
    assert forall|a: int, b: int| lo <= a < hi && lo <= b < hi && a != b
        implies (#[trigger] db[a]).1.as_nat() != (#[trigger] db[b]).1.as_nat() by {
        assert(db[a] == da[a]);
        assert(db[b] == da[b]);
        assert(da[a].1.as_nat() != da[b].1.as_nat());
    }
}

/// `stratum_unique` for the top stratum extended by ONE appended entry whose
/// index has no prior hit in the stratum: the unique discipline's wf clause
/// survives a first-write capture append.
pub(crate) proof fn lemma_stratum_unique_append<T, I: IndexLike>(
    da: Seq<(T, I)>, db: Seq<(T, I)>, lo: int, jnew: nat,
)
    requires
        0 <= lo <= da.len(),
        db.len() == da.len() + 1,
        db.subrange(0, da.len() as int) == da,
        db[da.len() as int].1.as_nat() == jnew,
        !captured_in_range::<T, I>(da, lo, da.len() as int, jnew),
        stratum_unique::<T, I>(da, lo, da.len() as int),
    ensures
        stratum_unique::<T, I>(db, lo, db.len() as int),
{
    assert forall|a: int, b: int| lo <= a < db.len() && lo <= b < db.len() && a != b
        implies (#[trigger] db[a]).1.as_nat() != (#[trigger] db[b]).1.as_nat() by {
        if a < da.len() && b < da.len() {
            assert(db.subrange(0, da.len() as int)[a] == db[a]);
            assert(db.subrange(0, da.len() as int)[b] == db[b]);
            assert(da[a].1.as_nat() != da[b].1.as_nat());
        } else if a == da.len() as int {
            assert(db.subrange(0, da.len() as int)[b] == db[b]);
            // The appended index has no hit below: a hit at b would witness
            // captured_in_range on da.
            assert(da[b].1.as_nat() != jnew);
        } else {
            assert(b == da.len() as int);
            assert(db.subrange(0, da.len() as int)[a] == db[a]);
            assert(da[a].1.as_nat() != jnew);
        }
    }
}

/// `frame_inv_range` is invariant under a PERMUTATION of the diff-log range
/// `[lo, hi)`: it reads that range only through quantifiers (`forall`/`exists` over
/// `k in [lo, hi)`), never through `overlay` or a positional index, so it depends on
/// the multiset of the range, not its order. This is what lets a sorted (reordering)
/// cold flush preserve the Vec invariant: sorting a just-closed frame's captures
/// keeps that stratum's write multiset, so its `frame_inv_range` carries. `d2`'s
/// uniqueness over the range is a hypothesis (the sorted encoder preserves it via
/// `unique_idx`), so no multiplicity/count reasoning is needed.
pub(crate) proof fn lemma_frame_inv_range_multiset<T: Copy, I: IndexLike>(
    above: Seq<T>, d1: Seq<(T, I)>, d2: Seq<(T, I)>, lo: int, hi: int,
    snap: Seq<T>, saved_len: nat,
)
    requires
        frame_inv_range::<T, I>(above, d1, lo, hi, snap, saved_len),
        0 <= lo <= hi,
        hi <= d1.len(),
        hi <= d2.len(),
        d1.subrange(lo, hi).to_multiset() == d2.subrange(lo, hi).to_multiset(),
        forall|a: int, b: int| lo <= a < hi && lo <= b < hi && a != b ==>
            (#[trigger] d2[a]).1.as_nat() != (#[trigger] d2[b]).1.as_nat(),
    ensures
        frame_inv_range::<T, I>(above, d2, lo, hi, snap, saved_len),
{
    let s1 = d1.subrange(lo, hi);
    let s2 = d2.subrange(lo, hi);
    // Each entry of one range is present in the other (equal multisets).
    assert forall|x: (T, I)| s1.contains(x) implies s2.contains(x) by {
        vstd::seq_lib::to_multiset_contains(s1, x);
        vstd::seq_lib::to_multiset_contains(s2, x);
    }
    assert forall|x: (T, I)| s2.contains(x) implies s1.contains(x) by {
        vstd::seq_lib::to_multiset_contains(s1, x);
        vstd::seq_lib::to_multiset_contains(s2, x);
    }
    // Index bound: every d2 entry in the range equals some d1 entry in the range.
    assert forall|k: int| lo <= k < hi implies (#[trigger] d2[k]).1.as_nat() < saved_len by {
        assert(s2[k - lo] == d2[k]);
        assert(s2.contains(d2[k]));
        assert(s1.contains(d2[k]));
        let m = choose|m: int| 0 <= m < s1.len() && s1[m] == d2[k];
        assert(s1[m] == d1[lo + m]);
    }
    // Per-cell two-arm: captured-in-range and the covering value both transfer by
    // membership (exists over the range).
    assert forall|j: int| 0 <= j < saved_len as int implies
        #[trigger] frame_cell_inv::<T, I>(above, d2, lo, hi, snap, j) by {
        assert(frame_cell_inv::<T, I>(above, d1, lo, hi, snap, j));
        // captured_in_range(d2) <==> captured_in_range(d1) via membership.
        if captured_in_range::<T, I>(d2, lo, hi, j as nat) {
            let k = choose|k: int| lo <= k < hi && 0 <= k < d2.len()
                && (#[trigger] d2[k]).1.as_nat() == j as nat;
            assert(s2[k - lo] == d2[k]);
            assert(s2.contains(d2[k]));
            assert(s1.contains(d2[k]));
            let m = choose|m: int| 0 <= m < s1.len() && s1[m] == d2[k];
            assert(s1[m] == d1[lo + m]);
            assert(captured_in_range::<T, I>(d1, lo, hi, j as nat));
        }
        if captured_in_range::<T, I>(d1, lo, hi, j as nat) {
            let k = choose|k: int| lo <= k < hi && 0 <= k < d1.len()
                && (#[trigger] d1[k]).1.as_nat() == j as nat;
            assert(s1[k - lo] == d1[k]);
            assert(s1.contains(d1[k]));
            assert(s2.contains(d1[k]));
            let m = choose|m: int| 0 <= m < s2.len() && s2[m] == d1[k];
            assert(s2[m] == d2[lo + m]);
            assert(captured_in_range::<T, I>(d2, lo, hi, j as nat));
        }
        // Covering value arm: the covering d1 entry is present in d2's range.
        if captured_in_range::<T, I>(d1, lo, hi, j as nat) {
            let k1 = choose|k: int| lo <= k < hi
                && (#[trigger] d1[k]).1.as_nat() == j as nat && d1[k].0 == snap[j];
            assert(s1[k1 - lo] == d1[k1]);
            assert(s1.contains(d1[k1]));
            assert(s2.contains(d1[k1]));
            let m = choose|m: int| 0 <= m < s2.len() && s2[m] == d1[k1];
            assert(s2[m] == d2[lo + m]);
        }
    }
}

/// `captured_in_range` (whether some entry in `[lo, hi)` writes index `j`) depends
/// only on the range's multiset, not its order: it is an existential over the range.
/// The bridge and no-stray wf clauses read the diff log through this, so they too
/// survive a within-range permutation.
pub(crate) proof fn lemma_captured_in_range_multiset<T: Copy, I: IndexLike>(
    d1: Seq<(T, I)>, d2: Seq<(T, I)>, lo: int, hi: int, j: nat,
)
    requires
        0 <= lo <= hi,
        hi <= d1.len(),
        hi <= d2.len(),
        d1.subrange(lo, hi).to_multiset() == d2.subrange(lo, hi).to_multiset(),
    ensures
        captured_in_range::<T, I>(d1, lo, hi, j) == captured_in_range::<T, I>(d2, lo, hi, j),
{
    let s1 = d1.subrange(lo, hi);
    let s2 = d2.subrange(lo, hi);
    if captured_in_range::<T, I>(d1, lo, hi, j) {
        let k = choose|k: int| lo <= k < hi && 0 <= k < d1.len()
            && (#[trigger] d1[k]).1.as_nat() == j;
        assert(s1[k - lo] == d1[k]);
        assert(s1.contains(d1[k]));
        vstd::seq_lib::to_multiset_contains(s1, d1[k]);
        vstd::seq_lib::to_multiset_contains(s2, d1[k]);
        let m = choose|m: int| 0 <= m < s2.len() && s2[m] == d1[k];
        assert(s2[m] == d2[lo + m]);
        assert(captured_in_range::<T, I>(d2, lo, hi, j));
    }
    if captured_in_range::<T, I>(d2, lo, hi, j) {
        let k = choose|k: int| lo <= k < hi && 0 <= k < d2.len()
            && (#[trigger] d2[k]).1.as_nat() == j;
        assert(s2[k - lo] == d2[k]);
        assert(s2.contains(d2[k]));
        vstd::seq_lib::to_multiset_contains(s1, d2[k]);
        vstd::seq_lib::to_multiset_contains(s2, d2[k]);
        let m = choose|m: int| 0 <= m < s1.len() && s1[m] == d2[k];
        assert(s1[m] == d1[lo + m]);
        assert(captured_in_range::<T, I>(d1, lo, hi, j));
    }
}

/// `captured_in_range` transfers between two logs whose ranges are pointwise
/// equal up to a uniform shift.
pub(crate) proof fn lemma_captured_in_range_shift<T: Copy, I: IndexLike>(
    d1: Seq<(T, I)>, d2: Seq<(T, I)>, lo1: int, lo2: int, cnt: int, j: nat,
)
    requires
        0 <= lo1, 0 <= lo2, 0 <= cnt,
        lo1 + cnt <= d1.len(),
        lo2 + cnt <= d2.len(),
        forall|q: int| 0 <= q < cnt ==> #[trigger] d2[lo2 + q] == d1[lo1 + q],
    ensures
        captured_in_range::<T, I>(d2, lo2, lo2 + cnt, j)
            == captured_in_range::<T, I>(d1, lo1, lo1 + cnt, j),
{
    if captured_in_range::<T, I>(d1, lo1, lo1 + cnt, j) {
        let k = choose|k: int| lo1 <= k < lo1 + cnt && 0 <= k < d1.len()
            && (#[trigger] d1[k]).1.as_nat() == j;
        assert(d2[lo2 + (k - lo1)] == d1[k]);
        assert(captured_in_range::<T, I>(d2, lo2, lo2 + cnt, j));
    }
    if captured_in_range::<T, I>(d2, lo2, lo2 + cnt, j) {
        let k = choose|k: int| lo2 <= k < lo2 + cnt && 0 <= k < d2.len()
            && (#[trigger] d2[k]).1.as_nat() == j;
        assert(d2[lo2 + (k - lo2)] == d1[lo1 + (k - lo2)]);
        assert(captured_in_range::<T, I>(d1, lo1, lo1 + cnt, j));
    }
}

/// `frame_inv_range` transfers between two logs whose ranges are pointwise
/// equal up to a uniform shift: every clause quantifies within the range,
/// so relabeling positions preserves it. The dedupe frame rule's k > b case.
pub(crate) proof fn lemma_frame_inv_range_shift<T: Copy, I: IndexLike>(
    above: Seq<T>, d1: Seq<(T, I)>, d2: Seq<(T, I)>,
    lo1: int, lo2: int, cnt: int, snap: Seq<T>, saved_len: nat,
)
    requires
        0 <= lo1, 0 <= lo2, 0 <= cnt,
        lo1 + cnt <= d1.len(),
        lo2 + cnt <= d2.len(),
        forall|q: int| 0 <= q < cnt ==> #[trigger] d2[lo2 + q] == d1[lo1 + q],
        frame_inv_range::<T, I>(above, d1, lo1, lo1 + cnt, snap, saved_len),
    ensures
        frame_inv_range::<T, I>(above, d2, lo2, lo2 + cnt, snap, saved_len),
{
    assert forall|k: int| lo2 <= k < lo2 + cnt implies
        (#[trigger] d2[k]).1.as_nat() < saved_len by {
        assert(d2[lo2 + (k - lo2)] == d1[lo1 + (k - lo2)]);
    }
    assert forall|j: int| 0 <= j < saved_len as int implies
        #[trigger] frame_cell_inv::<T, I>(above, d2, lo2, lo2 + cnt, snap, j) by {
        assert(frame_cell_inv::<T, I>(above, d1, lo1, lo1 + cnt, snap, j));
        lemma_captured_in_range_shift::<T, I>(d1, d2, lo1, lo2, cnt, j as nat);
        if captured_in_range::<T, I>(d1, lo1, lo1 + cnt, j as nat) {
            let ka = choose|k: int| lo1 <= k < lo1 + cnt
                && (#[trigger] d1[k]).1.as_nat() == j as nat
                && d1[k].0 == snap[j]
                && first_hitter::<T, I>(d1, lo1, k, j as nat);
            let kb = lo2 + (ka - lo1);
            assert(d2[kb] == d1[ka]);
            assert forall|q: int| lo2 <= q < kb implies
                (#[trigger] d2[q]).1.as_nat() != j as nat by {
                assert(d2[lo2 + (q - lo2)] == d1[lo1 + (q - lo2)]);
                assert(d1[lo1 + (q - lo2)].1.as_nat() != j as nat);
            }
            assert(first_hitter::<T, I>(d2, lo2, kb, j as nat));
        }
    }
}

/// `frame_inv_range` transfers from a stratum to its dedupe-and-permute
/// replacement at the same start position: `dnew`'s stratum is a unique-
/// index permutation of `dedupe_first_spec` of `dold`'s. The captured set
/// is preserved, and the surviving entry for each cell is the old stratum's
/// FIRST hitter - which is exactly the entry `frame_cell_inv`'s captured
/// arm pins. The dedupe frame rule's k == b case.
#[verifier::rlimit(600)]
#[verifier::spinoff_prover]
pub(crate) proof fn lemma_frame_inv_range_dedupe<T: Copy, I: IndexLike>(
    above: Seq<T>, dold: Seq<(T, I)>, dnew: Seq<(T, I)>,
    lo: int, m: nat, kept: nat, snap: Seq<T>, saved_len: nat,
)
    requires
        0 <= lo,
        lo + m <= dold.len(),
        lo + kept <= dnew.len(),
        kept == crate::diff_compress::dedupe_first_spec(
            dold.subrange(lo, lo + m as int)).len(),
        dnew.subrange(lo, lo + kept as int).to_multiset()
            == crate::diff_compress::dedupe_first_spec(
                dold.subrange(lo, lo + m as int)).to_multiset(),
        crate::diff_compress::unique_idx(dnew.subrange(lo, lo + kept as int)),
        frame_inv_range::<T, I>(above, dold, lo, lo + m as int, snap, saved_len),
    ensures
        frame_inv_range::<T, I>(above, dnew, lo, lo + kept as int, snap, saved_len),
{
    broadcast use vstd::seq_lib::group_to_multiset_ensures;
    let sold = dold.subrange(lo, lo + m as int);
    let r = dnew.subrange(lo, lo + kept as int);
    let dd = crate::diff_compress::dedupe_first_spec(sold);
    let rp = crate::diff_compress::dedupe_positions(sold, sold.len() as int);
    crate::diff_compress::lemma_dedupe_prefix_props::<T, I>(sold, sold.len() as int);
    // Membership both ways between the folded stratum and the dedupe.
    assert forall|x: (T, I)| r.contains(x) implies dd.contains(x) by {
        vstd::seq_lib::to_multiset_contains(r, x);
        vstd::seq_lib::to_multiset_contains(dd, x);
    }
    assert forall|x: (T, I)| dd.contains(x) implies r.contains(x) by {
        vstd::seq_lib::to_multiset_contains(r, x);
        vstd::seq_lib::to_multiset_contains(dd, x);
    }
    // Every folded entry is an old-stratum entry (through the dedupe).
    assert forall|k: int| 0 <= k < r.len() implies exists|p: int|
        0 <= p < sold.len() && #[trigger] r[k] == sold[p]
        && first_hitter::<T, I>(sold, 0, p, sold[p].1.as_nat()) by {
        assert(r.contains(r[k]));
        assert(dd.contains(r[k]));
        let t = choose|t: int| 0 <= t < dd.len() && dd[t] == r[k];
        let p0 = rp[t];
        assert(dd[t] == sold[p0]);
        assert(first_hitter::<T, I>(sold, 0, p0, sold[p0].1.as_nat()));
    }
    // Index bound.
    assert forall|k: int| lo <= k < lo + kept implies
        (#[trigger] dnew[k]).1.as_nat() < saved_len by {
        assert(r[k - lo] == dnew[k]);
        let p = choose|p: int| 0 <= p < sold.len()
            && #[trigger] r[k - lo] == sold[p]
            && first_hitter::<T, I>(sold, 0, p, sold[p].1.as_nat());
        assert(sold[p] == dold[lo + p]);
    }
    // Per-cell two-arm transfer.
    assert forall|j: int| 0 <= j < saved_len as int implies
        #[trigger] frame_cell_inv::<T, I>(above, dnew, lo, lo + kept as int, snap, j) by {
        assert(frame_cell_inv::<T, I>(above, dold, lo, lo + m as int, snap, j));
        // Captured equivalence, new -> old.
        if captured_in_range::<T, I>(dnew, lo, lo + kept as int, j as nat) {
            let k = choose|k: int| lo <= k < lo + kept && 0 <= k < dnew.len()
                && (#[trigger] dnew[k]).1.as_nat() == j as nat;
            assert(r[k - lo] == dnew[k]);
            let p = choose|p: int| 0 <= p < sold.len()
                && #[trigger] r[k - lo] == sold[p]
                && first_hitter::<T, I>(sold, 0, p, sold[p].1.as_nat());
            assert(sold[p] == dold[lo + p]);
            assert(captured_in_range::<T, I>(dold, lo, lo + m as int, j as nat));
        }
        if captured_in_range::<T, I>(dold, lo, lo + m as int, j as nat) {
            // The old stratum's FIRST hitter of j survives the dedupe and
            // lands somewhere in the folded stratum; its pair carries the
            // covering value.
            let ko = choose|k: int| lo <= k < lo + m
                && (#[trigger] dold[k]).1.as_nat() == j as nat
                && dold[k].0 == snap[j]
                && first_hitter::<T, I>(dold, lo, k, j as nat);
            let po = ko - lo;
            assert(sold[po] == dold[ko]);
            assert forall|q: int| 0 <= q < po implies
                (#[trigger] sold[q]).1.as_nat() != j as nat by {
                assert(sold[q] == dold[lo + q]);
            }
            assert(first_hitter::<T, I>(sold, 0, po, sold[po].1.as_nat()));
            assert(rp.contains(po));
            let t = choose|t: int| 0 <= t < rp.len() && #[trigger] rp[t] == po;
            assert(dd[t] == sold[po]);
            assert(dd.contains(sold[po]));
            assert(r.contains(sold[po]));
            let kr = choose|kr: int| 0 <= kr < r.len() && r[kr] == sold[po];
            assert(dnew[lo + kr] == sold[po]);
            assert(dnew[lo + kr].1.as_nat() == j as nat);
            assert(dnew[lo + kr].0 == snap[j]);
            assert(captured_in_range::<T, I>(dnew, lo, lo + kept as int, j as nat));
            // Uniqueness makes it the first hitter in the folded stratum.
            assert forall|q: int| lo <= q < lo + kr implies
                (#[trigger] dnew[q]).1.as_nat() != j as nat by {
                assert(r[q - lo] == dnew[q]);
                if dnew[q].1.as_nat() == j as nat {
                    assert(r[q - lo].1.as_nat() == r[kr].1.as_nat());
                }
            }
            assert(first_hitter::<T, I>(dnew, lo, lo + kr, j as nat));
        }
    }
}

/// `captured_in_range` is preserved by dedupe-and-permute of a stratum:
/// the kept set writes exactly the same cells.
pub(crate) proof fn lemma_captured_in_range_dedupe<T: Copy, I: IndexLike>(
    dold: Seq<(T, I)>, dnew: Seq<(T, I)>, lo: int, m: nat, kept: nat, j: nat,
)
    requires
        0 <= lo,
        lo + m <= dold.len(),
        lo + kept <= dnew.len(),
        kept == crate::diff_compress::dedupe_first_spec(
            dold.subrange(lo, lo + m as int)).len(),
        dnew.subrange(lo, lo + kept as int).to_multiset()
            == crate::diff_compress::dedupe_first_spec(
                dold.subrange(lo, lo + m as int)).to_multiset(),
    ensures
        captured_in_range::<T, I>(dnew, lo, lo + kept as int, j)
            == captured_in_range::<T, I>(dold, lo, lo + m as int, j),
{
    broadcast use vstd::seq_lib::group_to_multiset_ensures;
    let sold = dold.subrange(lo, lo + m as int);
    let r = dnew.subrange(lo, lo + kept as int);
    let dd = crate::diff_compress::dedupe_first_spec(sold);
    let rp = crate::diff_compress::dedupe_positions(sold, sold.len() as int);
    crate::diff_compress::lemma_dedupe_prefix_props::<T, I>(
        sold, sold.len() as int);
    if captured_in_range::<T, I>(dnew, lo, lo + kept as int, j) {
        let k = choose|k: int| lo <= k < lo + kept && 0 <= k < dnew.len()
            && (#[trigger] dnew[k]).1.as_nat() == j;
        assert(r[k - lo] == dnew[k]);
        assert(r.contains(r[k - lo]));
        vstd::seq_lib::to_multiset_contains(r, r[k - lo]);
        vstd::seq_lib::to_multiset_contains(dd, r[k - lo]);
        let t = choose|t: int| 0 <= t < dd.len() && dd[t] == r[k - lo];
        let p0 = rp[t];
        assert(dd[t] == sold[p0]);
        assert(sold[p0] == dold[lo + p0]);
        assert(captured_in_range::<T, I>(dold, lo, lo + m as int, j));
    }
    if captured_in_range::<T, I>(dold, lo, lo + m as int, j) {
        let k = choose|k: int| lo <= k < lo + m && 0 <= k < dold.len()
            && (#[trigger] dold[k]).1.as_nat() == j;
        assert(sold[k - lo] == dold[k]);
        assert(captured_in_range::<T, I>(sold, 0, sold.len() as int, j));
        lemma_lowest_hitter::<T, I>(sold, 0, sold.len() as int, j);
        let p = choose|p: int| 0 <= p < sold.len()
            && (#[trigger] sold[p]).1.as_nat() == j
            && first_hitter::<T, I>(sold, 0, p, j);
        assert(first_hitter::<T, I>(sold, 0, p, sold[p].1.as_nat()));
        assert(rp.contains(p));
        let t = choose|t: int| 0 <= t < rp.len() && #[trigger] rp[t] == p;
        assert(dd[t] == sold[p]);
        assert(dd.contains(sold[p]));
        vstd::seq_lib::to_multiset_contains(r, sold[p]);
        vstd::seq_lib::to_multiset_contains(dd, sold[p]);
        let kr = choose|kr: int| 0 <= kr < r.len() && r[kr] == sold[p];
        assert(dnew[lo + kr] == sold[p]);
        assert(captured_in_range::<T, I>(dnew, lo, lo + kept as int, j));
    }
}


/// One write applied to a column: overwrite in range, drop out of range. The shared
/// step of `overlay` (which folds it backward) and `apply_all` (forward).
pub open(crate) spec fn write_step<T, I: IndexLike>(x: Seq<T>, e: (T, I)) -> Seq<T> {
    if e.1.as_nat() < x.len() {
        x.update(e.1.as_nat() as int, e.0)
    } else {
        x
    }
}

/// `apply_all` peels one element off the FRONT when the sequence has unique indices:
/// the front write touches an index no later write touches, so applying it first or
/// last is the same column. The bridge between forward and backward application.
pub(crate) proof fn lemma_apply_all_front<T, I: IndexLike>(base: Seq<T>, s: Seq<(T, I)>)
    requires
        s.len() > 0,
        crate::diff_compress::unique_idx(s),
    ensures
        crate::diff_compress::apply_all::<T, I>(base, s)
            == write_step::<T, I>(
                crate::diff_compress::apply_all::<T, I>(base, s.subrange(1, s.len() as int)),
                s[0]),
    decreases s.len(),
{
    let n = s.len() as int;
    if n == 1 {
        assert(s.subrange(0, 0) =~= Seq::<(T, I)>::empty());
        assert(s.subrange(1, 1) =~= Seq::<(T, I)>::empty());
    } else {
        let last = s[n - 1];
        let front = s.subrange(0, n - 1);
        // apply_all(s) == step(apply_all(front), last) by definition.
        assert(front[0] == s[0]);
        // front is unique (a subrange of a unique sequence).
        assert(crate::diff_compress::unique_idx(front)) by {
            assert forall|a: int, b: int|
                0 <= a < front.len() && 0 <= b < front.len() && a != b
                implies (#[trigger] front[a]).1.as_nat() != (#[trigger] front[b]).1.as_nat() by {
                assert(front[a] == s[a]);
                assert(front[b] == s[b]);
            }
        }
        lemma_apply_all_front::<T, I>(base, front);
        let mid = front.subrange(1, n - 1);
        let am = crate::diff_compress::apply_all::<T, I>(base, mid);
        // apply_all(s) == step(step(apply_all(mid), s[0]), last); the two writes hit
        // distinct indices (unique_idx), and write_step preserves length, so they
        // commute.
        crate::diff_compress::lemma_apply_all_len::<T, I>(base, mid);
        assert(s[0].1.as_nat() != last.1.as_nat());
        assert(write_step::<T, I>(write_step::<T, I>(am, s[0]), last)
            =~= write_step::<T, I>(write_step::<T, I>(am, last), s[0]));
        // Re-fold the right-hand side: step(apply_all(mid), last) == apply_all(s[1..]).
        let tail = s.subrange(1, n);
        assert(tail.subrange(0, tail.len() - 1) =~= mid);
        assert(tail[tail.len() - 1] == last);
    }
}

/// A frame with unique indices applies the same FORWARD (`apply_all`, what
/// `restore_to` implements) as BACKWARD (`overlay`, what the restore replay model
/// uses): order within the frame cannot matter when no index repeats. Stated over
/// the enclosing log's range so the caller needs no subrange re-shift.
pub(crate) proof fn lemma_apply_all_eq_overlay<T, I: IndexLike>(
    base: Seq<T>, d: Seq<(T, I)>, lo: int, hi: int,
)
    requires
        0 <= lo <= hi <= d.len(),
        crate::diff_compress::unique_idx(d.subrange(lo, hi)),
    ensures
        crate::diff_compress::apply_all::<T, I>(base, d.subrange(lo, hi))
            == overlay::<T, I>(base, d, lo, hi),
    decreases hi - lo,
{
    let s = d.subrange(lo, hi);
    if lo >= hi {
        assert(s =~= Seq::<(T, I)>::empty());
    } else {
        // overlay peels the front: overlay(lo, hi) == step(overlay(lo+1, hi), d[lo]).
        // apply_all peels the front too under uniqueness (lemma above); the tails
        // agree by induction.
        let tail_unique = d.subrange(lo + 1, hi);
        assert(s.subrange(1, s.len() as int) =~= tail_unique);
        assert(crate::diff_compress::unique_idx(tail_unique)) by {
            assert forall|a: int, b: int|
                0 <= a < tail_unique.len() && 0 <= b < tail_unique.len() && a != b
                implies (#[trigger] tail_unique[a]).1.as_nat()
                    != (#[trigger] tail_unique[b]).1.as_nat() by {
                assert(tail_unique[a] == s[a + 1]);
                assert(tail_unique[b] == s[b + 1]);
            }
        }
        lemma_apply_all_front::<T, I>(base, s);
        lemma_apply_all_eq_overlay::<T, I>(base, d, lo + 1, hi);
        assert(s[0] == d[lo]);
    }
}

/// The per-stratum bridge: if a diff-log range `[lo, hi)` satisfies the
/// two-arm `frame_inv` relative to `above` and `snap` (stated directly over
/// the range), then overlaying that range onto `above` reproduces `snap`
/// on `[0, saved_len)`.
///
/// Hypotheses mirror `frame_inv` + the structural conditions, but phrased
/// over the diff-log range rather than an extracted subrange.
pub(crate) proof fn lemma_overlay_eq_snap<T, I: IndexLike>(
    above: Seq<T>, diffs: Seq<(T, I)>, lo: int, hi: int,
    snap: Seq<T>, saved_len: nat,
)
    requires
        0 <= lo <= hi <= diffs.len(),
        // The base is already full-length (restore resizes to saved_len
        // before replay), so the overwrite-only overlay reaches every cell.
        saved_len <= above.len(),
        // Full frame_inv_range bundles snap.len, index-bound, uniqueness, and
        // the per-cell two-arm — all needed below.
        frame_inv_range::<T, I>(above, diffs, lo, hi, snap, saved_len),
    ensures
        forall|j: int| 0 <= j < saved_len as int ==>
            #[trigger] overlay::<T, I>(above, diffs, lo, hi)[j] == snap[j],
{
    lemma_overlay_len::<T, I>(above, diffs, lo, hi);
    assert forall|j: int| 0 <= j < saved_len as int implies
        #[trigger] overlay::<T, I>(above, diffs, lo, hi)[j] == snap[j]
    by {
        assert(frame_cell_inv::<T, I>(above, diffs, lo, hi, snap, j));
        if !captured_in_range::<T, I>(diffs, lo, hi, j as nat) {
            // Uncaptured: overlay leaves above[j], which == snap[j].
            assert forall|k: int| lo <= k < hi && 0 <= k < diffs.len() implies
                (#[trigger] diffs[k]).1.as_nat() != j as nat
            by {
                // else captured_in_range would hold
            }
            lemma_overlay_uncaptured::<T, I>(above, diffs, lo, hi, j);
        } else {
            // Captured: the FIRST hitter holds snap[j], and first-hitter is
            // exactly the shape lemma_overlay_lowest pins (base-independent,
            // duplicate-tolerant).
            assert(captured_in_range::<T, I>(diffs, lo, hi, j as nat));
            assert((j as nat) < above.len());  // from saved_len <= above.len()
            let p = choose|k: int| lo <= k < hi
                && (#[trigger] diffs[k]).1.as_nat() == j as nat
                && diffs[k].0 == snap[j]
                && first_hitter::<T, I>(diffs, lo, k, j as nat);
            lemma_overlay_lowest::<T, I>(above, diffs, lo, hi, p, j);
        }
    }
}

/// Semi-persistent vector parameterized by storage backend `S` and index
/// type `I`. `TRACK=false` compiles out const-gated tracking execution; the
/// generic layout still contains empty diff/frame/fork fields.
pub struct Vec<
    T,
    I,
    S,
    const TRACK: bool = true,
    VC = crate::value_compressor::NoValueCompression,
>
where
    T: Sized + Copy,
    I: IndexLike,
    S: DiffStore<T, I, TRACK>,
    VC: crate::value_compressor::ValueCompressor<T>,
{
    pub(crate) store: S,
    // Mainline's field, verbatim: the hot tier IS a bare pair vec
    // (doc/tasks/mainline-shape-plus-coldstack-goal.md). The DiffLog type
    // was the compression branch's own artifact and is retired.
    pub(crate) diff_log: std::vec::Vec<(T, I)>,
    // Ruled layout: two frame stacks. Cold frames are the OLDEST [0, k),
    // hot frames the most recent [k, n); a token's frame_idx resolves by
    // comparison with cold_stack.len(). Each tier's header carries the
    // frame's saved_len.
    pub(crate) hot_stack: std::vec::Vec<crate::frame::HotFrame<I>>,
    pub(crate) cold_stack: std::vec::Vec<crate::frame::ColdFrameHdr<I>>,
    /// All value runs of all cold frames, concatenated in frame order.
    pub(crate) cold_value_pool: std::vec::Vec<T>,
    /// All index runs of all cold frames: run lands at live[base..], values
    /// at cold_value_pool[start .. start+len].
    pub(crate) cold_index_runs: std::vec::Vec<crate::frame::IndexRun<I>>,
    /// Compression cadence: None = never compress (plain baseline columns);
    /// Some(b) = at mark, when more than b hot frames exist, pass
    /// compress=true (the buffered eviction policy).
    pub(crate) hot_buffer: Option<usize>,
    /// THE ghost diff (proof architecture, goal doc): every tracked write,
    /// in temporal order, duplicates included, regardless of the store's
    /// capture discipline. Restore correctness is stated once against this;
    /// each physical representation carries an abstraction theorem to it.
    pub(crate) full_trail: Ghost<Seq<(T, I)>>,
    /// Stratum start offsets into full_trail, one per mark.
    pub(crate) trail_frames: Ghost<Seq<nat>>,
    /// The saved_len of the topmost (active) frame, cached for the hot path.
    /// `I::min()` when the stack is empty. Mirrors production.
    pub(crate) active_saved_len: I,
    pub(crate) phantom: core::marker::PhantomData<(T, I, VC)>,
    /// Ghost stack of deep copies. `snapshots[k]` is `view()` at the
    /// moment frame `k` was pushed. Always `snapshots.len() == tf.len()`.
    pub(crate) snapshots: Ghost<Seq<Seq<T>>>,
}

impl<T, I, S, const TRACK: bool, VC: crate::value_compressor::ValueCompressor<T>> Vec<T, I, S, TRACK, VC>
where
    T: Sized + Copy,
    I: IndexLike,
    S: DiffStore<T, I, TRACK>,
{
    /// Public spec view: the abstract sequence of stored values.
    pub open(crate) spec fn view(&self) -> Seq<T> {
        self.store.data()
    }

    /// Snapshot stack (ghost).
    pub open(crate) spec fn snapshots_view(&self) -> Seq<Seq<T>> {
        self.snapshots@
    }

    /// Frame-stack depth (spec counterpart of `depth()`). Public contracts phrase
    /// frame counts through this — the `frames` field is `pub(crate)`
    /// (privacy closeout).
    pub open(crate) spec fn depth_spec(&self) -> nat {
        self.trail_frames@.len()
    }

    /// Ghost stratum bounds: frame k's writes are
    /// full_trail[g_start(k), g_end(k)).
    pub open(crate) spec fn g_start(&self, k: int) -> int {
        self.trail_frames@[k] as int
    }

    pub open(crate) spec fn g_end(&self, k: int) -> int {
        if k + 1 < self.trail_frames@.len() {
            self.trail_frames@[k + 1] as int
        } else {
            self.full_trail@.len() as int
        }
    }

    /// Frame k's saved_len, ghost form: pinned by its snapshot's length.
    pub open(crate) spec fn g_saved_len(&self, k: int) -> nat {
        self.snapshots@[k].len()
    }

    /// Diff-log length (spec counterpart of `diff_log_len()`).
    pub open(crate) spec fn diff_log_len_spec(&self) -> nat {
        self.diff_log@.len()
    }

    /// The top (open) frame's `diff_start`, or 0 when no frame is live. The sorted
    /// index-major fold's alignment: for a run-compressed log compacted at every mark,
    /// the DiffLog cold region ends exactly here (the tail is the open frame's stratum).
    pub open(crate) spec fn top_diff_start_spec(&self) -> int {
        if self.trail_frames@.len() > 0 {
            self.g_start((self.trail_frames@.len() - 1) as int)
        } else {
            0
        }
    }

    /// Structural token validity (H2): the genealogy (generation stamps,
    /// container identity) lives on the owning group's `History`, so per-vec
    /// validity reduces to frame liveness. Kept under its historical name so
    /// composite validity chains read unchanged.
    pub open(crate) spec fn is_token_valid_spec(&self, token: VecToken) -> bool {
        token.frame_idx < self.trail_frames@.len()
    }

    /// The mark-depth quantity the depth-headroom contracts are phrased over.
    /// Post-H2 the container tracks no genealogy, so this is the live frame
    /// depth (the stamp-array length it used to be lived on `GenStamps`).
    pub open(crate) spec fn fork_count_spec(&self) -> nat {
        self.trail_frames@.len()
    }

    /// "Restorable now": the full runtime-checkable STRUCTURAL precondition of
    /// `restore` — frame liveness, the TRACK gate, and the depth headroom.
    /// Branch validity (was: container identity + generation stamp) lives on
    /// the owning group's `History` (doc 10 / H2), which validates once for
    /// every member instead of once per member.
    pub open(crate) spec fn is_restorable_spec(&self, token: VecToken) -> bool {
        &&& TRACK
        &&& token.frame_idx < self.trail_frames@.len()
        &&& self.trail_frames@.len() < u32::MAX
    }

    /// The "layer above" frame `k`: snapshots[k+1] for inner frames, or the
    /// current view for the topmost frame.
    pub open(crate) spec fn layer_above_at(&self, k: int) -> Seq<T> {
        if k + 1 < self.trail_frames@.len() {
            self.snapshots@[k + 1]
        } else {
            self.view()
        }
    }

    /// End of frame `k`'s stratum.
    pub open(crate) spec fn stratum_end(&self, k: int) -> int {
        self.g_end(k)
    }

    /// Well-formedness at arbitrary stack depth.
    ///
    /// Structural:
    ///   - snapshots.len() == tf.len()
    ///   - tf.len() == 0 ==> diff_log empty
    ///   - self.g_start(0) == 0
    ///   - diff_starts monotone, last <= diff_log.len()
    ///   - saved lengths equal their snapshot lengths; they need not be
    ///     monotone and may exceed the current view length after pop
    ///   - snapshots[k].len() == frames[k].saved_len
    ///
    /// Per-frame (over each frame's stratum `[diff_start_k, stratum_end_k)`):
    ///   frame_inv_range(layer_above(k), diff_log, lo_k, hi_k,
    ///                   snapshots[k], saved_len_k)
    /// The snapshot-reconstruction core of `wf`: store well-formedness,
    /// parallel stack lengths, frame bookkeeping (monotone diff_start and
    /// snapshot lengths), and the per-frame `frame_inv_range`.
    ///
    /// Crucially this does NOT include the capture-flag bridge or the
    /// `store.captured().len() == view.len()` tie. `resize_default` (used by
    /// restore to regrow a popped view) PRESERVES `wf_for_snap` — growing the
    /// view with default fillers only touches captured cells (which the
    /// frame_inv_range captured arm ignores) — but breaks the bridge. So the
    /// central reconstruction lemma is stated over `wf_for_snap`, lettng
    /// restore invoke it on the resized (non-`wf`, but `wf_for_snap`) state.
    pub open(crate) spec fn wf_for_snap(&self) -> bool {
        let gt = self.full_trail@;
        let tf = self.trail_frames@;
        let snaps = self.snapshots@;
        let n = gt.len();

        &&& self.store.wf()
        &&& snaps.len() == tf.len()
        // Frame-count bridge: the two physical stacks tile the ghost frames.
        &&& self.cold_stack@.len() + self.hot_stack@.len() == tf.len()
        // No frames => no captures => the physical hot log is empty (and
        // by the bridge both stacks are too).
        &&& (tf.len() == 0 ==> self.diff_log@.len() == 0)
        // Frame count fits usize (the depth guards keep it below u32::MAX).
        &&& tf.len() < usize::MAX
        // TRACK=false => no frames, ever (mark, the only frame-pusher,
        // requires TRACK) - production-parity erasure.
        &&& (!TRACK ==> tf.len() == 0)
        &&& (tf.len() == 0 ==> n == 0)
        &&& (tf.len() > 0 ==> tf[0] == 0)
        &&& (tf.len() > 0 ==> tf[(tf.len() - 1) as int] <= n)
        // Ghost stratum boundaries are monotone in the ghost trail.
        &&& (forall|k: int| #![trigger tf[k]] 0 <= k && k + 1 < tf.len() ==>
                tf[k] <= tf[k + 1])
        // THE restore-correctness statement, once, against the ghost trail
        // (proof architecture: every physical representation relates to
        // full_trail by an abstraction theorem; reconstruction only ever
        // reads the ghost). frame_inv_range is Seq-level and unchanged.
        &&& (forall|k: int| 0 <= k < tf.len() ==>
                #[trigger] frame_inv_range::<T, I>(
                    self.layer_above_at(k),
                    gt,
                    self.g_start(k),
                    self.g_end(k),
                    snaps[k],
                    snaps[k].len()))
    }

    /// The physical representations' abstraction to the ghost trail (the
    /// T1-T4 theorems of the proof architecture). Opaque; maintained by the
    /// scaffolded mutators during the exec-locked phase and discharged
    /// per-theorem afterwards (goal doc, deliverables 5-6).
    pub open(crate) spec fn repr_ok(&self) -> bool {
        // Deferred to D6 (cold-frame T3/T4 clauses for restore_frame's
        // discharge). The OPEN-FRAME physical<->ghost relation push_frame's
        // prepare_mark needs is carried DIRECTLY by wf's physical capture
        // bridge (below) rather than here: prepare_mark reads the physical
        // diff_log slice, and the physical bridge names its flags. The
        // ghost/physical index-set equality is then a derived consequence of
        // the two bridges, not a separately maintained invariant.
        true
    }

    pub open(crate) spec fn wf(&self) -> bool {
        let tf = self.trail_frames@;

        &&& self.wf_for_snap()
        &&& self.repr_ok()
        // active_saved_len caches the top frame's saved_len (== its
        // snapshot's length, the ghost form).
        &&& (tf.len() == 0 ==> self.active_saved_len == I::min_spec())
        &&& (tf.len() > 0 ==>
                self.active_saved_len.as_nat()
                    == self.g_saved_len((tf.len() - 1) as int))
        // Capture-flag bridge, over the ghost trail: a set flag names a cell
        // captured in the top ghost stratum. Holds for BOTH disciplines
        // (the trail store's flags are ghost and first-capture-tracking).
        &&& self.store.captured().len() == self.view().len()
        &&& (tf.len() > 0 ==>
                forall|j: int|
                    0 <= j < self.active_saved_len.as_nat() && j < self.view().len() ==>
                    #[trigger] self.store.captured()[j]
                        == captured_in_range::<T, I>(
                            self.full_trail@,
                            self.g_start((tf.len() - 1) as int),
                            self.full_trail@.len() as int,
                            j as nat))
        // No stray flags: every set flag lies in the trackable region.
        &&& (TRACK ==> forall|j: int| 0 <= j < self.view().len()
                && #[trigger] self.store.captured()[j]
                ==> tf.len() > 0 && j < self.active_saved_len.as_nat())
    }

    /// `wf` is preserved by a change to `forks` alone. Every `wf` conjunct except
    /// `self.forks.wf()` reads only `store`/`frames`/`diff_log`/`snapshots`/
    /// `active_saved_len`; if those all match a well-formed `old_self`, those
    /// conjuncts carry, and `self.forks.wf()` supplies the last one. Used by the
    /// `restore` wrapper (and later `SyncGroup`) to re-establish `wf` across the
    /// `fork()` branch-cut without re-running `wf`'s quantifiers.
    pub(crate) proof fn lemma_forks_change_preserves_wf(&self, old_self: Self)
        requires
            old_self.wf(),
            self.store == old_self.store,
            self.trail_frames@ == old_self.trail_frames@,
            self.full_trail@ == old_self.full_trail@,
            self.diff_log == old_self.diff_log,
            self.hot_stack@ == old_self.hot_stack@,
            self.cold_stack@ == old_self.cold_stack@,
            self.snapshots@ == old_self.snapshots@,
            self.active_saved_len == old_self.active_saved_len,
        ensures
            self.wf(),
    {
        // wf_for_snap and the active/captured conjuncts read only the pinned
        // fields (store/frames/diff_log/snapshots/active); transfer them from
        // old_self.wf() instance by instance. forks.wf() is given.
        assert(self.view() == old_self.view());
        assert(self.store.captured() == old_self.store.captured());
        assert(old_self.wf_for_snap());
        // wf_for_snap's frame_inv_range forall: its args are pinned fields or the
        // helpers layer_above_at/stratum_end, which read only pinned fields.
        assert forall|k: int| 0 <= k < self.trail_frames@.len() implies
            #[trigger] frame_inv_range::<T, I>(
                self.layer_above_at(k),
                self.full_trail@,
                self.g_start(k),
                self.g_end(k),
                self.snapshots@[k],
                self.snapshots@[k].len())
        by {
            assert(self.layer_above_at(k) == old_self.layer_above_at(k));
            assert(self.g_end(k) == old_self.g_end(k));
            assert(old_self.frame_inv_range_holds(k));
        }
        assert(self.wf_for_snap());
        // diff_log.wf() transfers by structural equality with old_self.
        // wf's captured-bridge and no-stray foralls read store.captured()/view/
        // frames/active/diffs — all pinned, so they carry directly.
        assert(self.wf());
    }




    /// `stratum_end(k)` is in range: `diff_start(k) <= stratum_end(k) <= diff_log.len()`.
    pub(crate) proof fn lemma_stratum_bounds(&self, k: int)
        requires
            self.wf_for_snap(),
            0 <= k < self.trail_frames@.len(),
        ensures
            self.g_start(k) <= self.stratum_end(k),
            self.stratum_end(k) <= self.full_trail@.len(),
    {
        if k + 1 < self.trail_frames@.len() {
            self.lemma_diff_start_monotone(k, k + 1);
            self.lemma_diff_start_le_n(k + 1);
        } else {
            self.lemma_diff_start_le_n(k);
        }
    }

    /// Every frame's diff_start is `<= diff_log.len()`. Follows from
    /// monotonicity plus the top frame's bound, by upward induction.
    pub(crate) proof fn lemma_diff_start_le_n(&self, k: int)
        requires
            self.wf_for_snap(),
            0 <= k < self.trail_frames@.len(),
        ensures
            self.trail_frames@[k] <= self.full_trail@.len(),
        decreases self.trail_frames@.len() - k,
    {
        let tf = self.trail_frames@;
        if k < tf.len() - 1 {
            self.lemma_diff_start_monotone(k, (tf.len() - 1) as int);
        }
    }

    /// diff_start is monotone non-decreasing across frames: for `a <= b`,
    /// `self.g_start(a) <= self.g_start(b)`.
    pub(crate) proof fn lemma_diff_start_monotone(&self, a: int, b: int)
        requires
            self.wf_for_snap(),
            0 <= a <= b < self.trail_frames@.len(),
        ensures
            self.trail_frames@[a] <= self.trail_frames@[b],
        decreases b - a,
    {
        if a < b {
            self.lemma_diff_start_monotone(a, b - 1);
            // adjacent step (b-1, b) from wf_for_snap's monotone clause;
            // the bound makes k = b-1 an instantiation the trigger accepts.
            assert(0 <= b - 1 && (b - 1) + 1 < self.trail_frames@.len());
            assert(self.trail_frames@[b - 1] <= self.trail_frames@[b]);
        }
    }

    // NOTE (pop into marked region): `lemma_saved_len_le_active` ("top frame is the
    // longest"), `lemma_saved_len_monotone` ("saved_len non-decreasing"), and
    // `lemma_saved_len_le_view` ("every saved_len <= view.len()") were DELETED
    // here. All three are FALSE once pop can shrink the view into the marked
    // region and `mark` can record a short length. They are replaced
    // everywhere by the per-frame coverage in `frame_cell_inv`'s uncaptured
    // arm (uncaptured j ==> j < layer_above.len()), which is exactly the bound
    // those lemmas used to supply and which holds unconditionally.

    /// The central reconstruction lemma: overlaying all strata from frame `k` up to the
    /// top, onto the current view, reconstructs `snapshots[k]` (on its
    /// `[0, saved_len_k)` domain).
    ///
    /// Proved by downward induction on `k` (from the top frame to `k`).
    /// Base case k == top: the stratum is `[diff_start_top, n)`, the layer
    /// above is the view, and `frame_inv_range` + `lemma_overlay_eq_snap`
    /// give the result. Inductive step: split the range at
    /// `frames[k+1].diff_start`; the upper part reconstructs snapshots[k+1]
    /// by IH, then stratum k overlays on top to give snapshots[k].
    /// FLAT central lemma (per-cell, base-parametric, target-clamped).
    ///
    /// For a single cell `j < saved_k`, overlaying the whole tail range
    /// `[diff_start_k, n)` onto `base` reconstructs `snapshots[k][j]`. Unlike
    /// the layered `lemma_snap_eq_overlay`, this never builds intermediate
    /// snapshot sequences and never needs `saved_len` monotonicity: a cell
    /// captured at some level is pinned by `lemma_overlay_lowest` (base-
    /// independent, lowest-in-range = deepest stratum wins); an uncaptured
    /// cell recurses one frame up (coverage gives `j < layer_above.len()`),
    /// terminating at the top frame where `layer_above == view` and the base
    /// agrees with the view on `j`.
    ///
    /// `base` requirements: long enough (`j < base.len()`) and agreeing with
    /// the view on the shared prefix — exactly what `resize_default` gives
    /// restore.
    pub(crate) proof fn lemma_cell_eq_overlay(&self, base: Seq<T>, k: int, j: int)
        requires
            self.wf_for_snap(),
            0 <= k < self.trail_frames@.len(),
            0 <= j < self.g_saved_len(k) as int,
            (j as nat) < base.len(),
            // base agrees with the view on the shared prefix
            forall|m: int| 0 <= m < base.len() && m < self.view().len()
                ==> #[trigger] base[m] == self.view()[m],
        ensures
            overlay::<T, I>(
                base, self.full_trail@,
                self.g_start(k),
                self.full_trail@.len() as int)[j]
                == self.snapshots@[k][j],
        decreases self.trail_frames@.len() - k,
    {
        let tf = self.trail_frames@;
        let diffs = self.full_trail@;
        let snaps = self.snapshots@;
        let n = diffs.len() as int;
        let lo = self.g_start(k);
        let mid = self.stratum_end(k);
        let saved = self.g_saved_len(k);
        self.lemma_diff_start_le_n(k);
        // Bounds: lo <= mid <= n.
        if k + 1 < tf.len() {
            self.lemma_diff_start_le_n(k + 1);
            assert(self.g_start(k) <= self.g_start(k + 1));  // monotone (adjacent)
            assert(mid == self.g_start(k + 1));
        } else {
            assert(mid == n);
        }
        assert(lo <= mid <= n);
        // stratum k's per-cell invariant at j (from wf_for_snap).
        lemma_frame_inv_arm_at::<T, I>(
            self.layer_above_at(k), diffs, lo, mid, snaps[k], saved, j);

        // frame_inv_range for stratum k (incl. its uniqueness conjunct).
        assert(frame_inv_range::<T, I>(self.layer_above_at(k), diffs, lo, mid, snaps[k], saved));
        if captured_in_range::<T, I>(diffs, lo, mid, j as nat) {
            // Captured in stratum k. The captured arm gives an entry p in
            // [lo, mid) holding snap_k[j]. By stratum-k uniqueness, p is the
            // ONLY hitter of j in [lo, mid), hence the lowest hitter in the
            // whole tail [lo, n) (stratum k = [lo, mid) is the lowest part;
            // deeper strata [mid, n) sit above). lemma_overlay_lowest pins it.
            let p = choose|q: int| lo <= q < mid
                && (#[trigger] diffs[q]).1.as_nat() == j as nat
                && diffs[q].0 == snaps[k][j]
                && first_hitter::<T, I>(diffs, lo, q, j as nat);
            assert(lo <= p < mid && diffs[p].1.as_nat() == j as nat);
            // first_hitter IS "no earlier hitter in [lo, p)" — the exact
            // hypothesis lemma_overlay_lowest wants, no uniqueness needed.
            assert(forall|q: int| lo <= q < p ==> (#[trigger] diffs[q]).1.as_nat() != j as nat);
            lemma_overlay_lowest::<T, I>(base, diffs, lo, n, p, j);
        } else {
            // Uncaptured in stratum k. Coverage ⇒ j < layer_above.len() and
            // layer_above[j] == snap_k[j]. Recurse / terminate.
            if k + 1 < tf.len() {
                // layer_above == snaps[k+1]; recurse at k+1 over [mid, n).
                assert(self.layer_above_at(k) == snaps[k + 1]);
                assert((j as nat) < snaps[k + 1].len());
                assert(snaps[k + 1][j as int] == snaps[k][j as int]);
                assert(mid == self.g_start(k + 1));
                self.lemma_cell_eq_overlay(base, k + 1, j);
                // overlay over [mid, n) gives snap_{k+1}[j] == snap_k[j].
                // Extend to [lo, n): !captured_in_range(lo,mid,j) is exactly
                // "no q in [lo,mid) hits j", so the [lo,mid) prefix leaves j.
                assert forall|q: int| lo <= q < mid implies
                    (#[trigger] diffs[q]).1.as_nat() != j as nat by {
                    if diffs[q].1.as_nat() == j as nat {
                        assert(0 <= q < diffs.len());  // q < mid <= n
                        assert(captured_in_range::<T, I>(diffs, lo, mid, j as nat));
                    }
                }
                lemma_overlay_uncaptured_prefix::<T, I>(base, diffs, lo, mid, n, j);
            } else {
                // Top frame: layer_above == view, j < view.len(), and
                // base[j] == view[j] == snap_k[j]. No entry in [lo, n) hits j.
                assert(self.layer_above_at(k) == self.view());
                assert((j as nat) < self.view().len());
                assert(self.view()[j as int] == snaps[k][j as int]);
                assert(mid == n);
                lemma_overlay_uncaptured::<T, I>(base, diffs, lo, n, j);
            }
        }
    }


    /// "Untracked" state: no marks are live. Production compiles out tracking
    /// when `TRACK == false`; the verus model instead proves that whenever the
    /// frame stack is empty there are no live diff entries and operations have
    /// the plain sequence transitions on the view. The empty diff/frame/fork
    /// fields and runtime guards remain in the executable struct.
    pub open(crate) spec fn untracked(&self) -> bool {
        self.trail_frames@.len() == 0
    }

    /// `wf` forces an empty diff log when the frame stack is empty.
    /// This is a logical-state fact, not a layout or code-generation theorem.
    pub(crate) proof fn lemma_untracked_diff_log_empty(&self)
        requires self.wf(), self.untracked(),
        ensures self.diff_log@.len() == 0,
    {
        // Directly from wf_for_snap's `tf.len()==0 ==> diff_log.len()==0`.
    }

    /// Observational equivalence to `std::Vec` while untracked: push appends,
    /// set updates, pop drops the last element — exactly the std operations on
    /// the view — AND the vector stays untracked with no diff log. These are
    /// thin wrappers asserting the equivalence explicitly; the heavy lifting is
    /// in push/set/pop's own contracts, which hold for ALL states.
    pub fn push_untracked(&mut self, value: T)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            (old(self).untracked() && old(self).view().len() + 1 < I::max_nat()) ==> {
                &&& final(self).untracked()
                &&& final(self).view() == old(self).view().push(value)
                &&& final(self).diff_log_len_spec() == 0
            },
    {
        if !(self.depth_exec() == 0) {
            crate::guard::refuse("Vec::push_untracked: vector has live frames");
        }
        let cap = <I as crate::index_like::IndexLike>::max().as_usize();
        proof {
            <I as crate::index_like::IndexLike>::lemma_max_nat_positive();
            <I as crate::index_like::IndexLike>::lemma_max_as_nat();
            <I as crate::index_like::IndexLike>::lemma_max_nat_fits_usize();
        }
        if !(self.store.raw_len() < cap) {
            crate::guard::refuse("Vec::push_untracked: index word exhausted");
        }
        self.push(value);
        proof { self.lemma_untracked_diff_log_empty(); }
    }

    pub fn pop_untracked(&mut self) -> (r: Option<T>)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            old(self).untracked() ==> {
                &&& final(self).untracked()
                &&& (old(self).view().len() == 0
                    ==> r is None && final(self).view() == old(self).view())
                &&& (old(self).view().len() > 0
                    ==> r == Some(old(self).view().last())
                        && final(self).view() == old(self).view().drop_last())
                &&& final(self).diff_log_len_spec() == 0
            },
    {
        if !(self.depth_exec() == 0) {
            crate::guard::refuse("Vec::pop_untracked: vector has live frames");
        }
        let r = self.pop();
        proof { self.lemma_untracked_diff_log_empty(); }
        r
    }

    pub fn set_untracked(&mut self, i: I, value: T)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            (old(self).untracked() && i.as_nat() < old(self).view().len()) ==> {
                &&& final(self).untracked()
                &&& final(self).view() == old(self).view().update(i.as_nat() as int, value)
                &&& final(self).diff_log_len_spec() == 0
            },
    {
        if !(self.depth_exec() == 0) {
            crate::guard::refuse("Vec::set_untracked: vector has live frames");
        }
        if !(i.as_usize() < self.store.raw_len()) {
            crate::guard::refuse("Vec::set_untracked: index out of bounds");
        }
        self.set_index(i, value);
        proof { self.lemma_untracked_diff_log_empty(); }
    }

    #[inline(always)]
    pub fn len(&self) -> (n: I)
        requires self.wf(),
        ensures n.as_nat() == self.view().len(),
    {
        self.store.len()
    }

    #[inline(always)]
    pub fn is_empty(&self) -> (b: bool)
        requires self.wf(),
        ensures b == (self.view().len() == 0),
    {
        self.store.is_empty()
    }

    #[inline(always)]
    pub fn get_index(&self, i: I) -> (v: T)
        requires
            self.wf(),
        ensures
            i.as_nat() < self.view().len() ==> v == self.view()[i.as_nat() as int],
    {
        // Total with documented panic: the bound
        // is an explicit branch, not an erased requires — an out-of-range
        // index from an unverified caller refuses instead of whatever the
        // store does. The check is the one std indexing performed anyway.
        if !(i.as_usize() < self.store.raw_len()) {
            crate::guard::refuse("Vec::get_index: index out of bounds");
        }
        self.store.get(i)
    }

    /// Build an empty tracked vector over a freshly-empty store. Mirrors
    /// production's `with_store`. The store must be well-formed and empty
    /// (no data, no capture flags) — the concrete `new()` of each backend
    /// supplies that.
    pub(crate) fn with_store(store: S) -> (v: Self)
        requires
            store.wf(),
            store.data().len() == 0,
        ensures
            v.wf(),
            v.view().len() == 0,
            v.snapshots_view().len() == 0,
    {
        // Experiment lever (measurement instrument, not the final per-column
        // config): SEMPER_COMPRESS=auto flips default-constructed columns to the
        // per-frame-adaptive representation, so a whole binary (the e-graph under
        // Sundance) runs compressed without any constructor plumbing. Capability-
        // guarded: a store whose restore reads the replayed index slice
        // (InlineStore's sparse tag-clear) skips it, because the adaptive
        // representation's index materialization is the measured slow path there.
        // Unset, nothing changes.
        // The InlineStore path is now frame-wise too (subrange_vec fast path feeds
        // its begin_restore materialization and its replay), so the lever covers
        // every store.
        let mode = if crate::compression_config::env_compress_default() {
            crate::diff_compress::CompressionMode::Auto
        } else {
            crate::diff_compress::CompressionMode::None
        };
        Self::with_store_mode(store, mode)
    }

    /// As `with_store`, but selects the diff log's value representation at
    /// runtime (per instance, not a const generic): `None` keeps the value
    /// column plain (SMT: no compression overhead); `ValueDict` dictionary-
    /// encodes it (equality saturation: the union-find columns coalesce equal
    /// values, at the cost of a `dict_find` per capture). Both start empty and
    /// well-formed, so the constructor's contract is representation-independent.
    pub(crate) fn with_store_mode(store: S, mode: crate::diff_compress::CompressionMode)
        -> (v: Self)
        requires
            store.wf(),
            store.data().len() == 0,
        ensures
            v.wf(),
            v.view().len() == 0,
            v.snapshots_view().len() == 0,
    {
        proof { store.lemma_wf_captured_len(); }  // captured().len() == 0
        // The bare mainline log for every mode; what differs per column is
        // only the compression cadence below (ruled design).
        let diff_log: std::vec::Vec<(T, I)> = std::vec::Vec::new();
        // Cadence: a mode-None unique-capture column is the plain
        // production-parity baseline and never compresses; every other
        // column (any compressing mode, and the trail discipline whose only
        // compression path is eviction) buffers HOT_BUFFER frames.
        let tiered = !(matches!(mode, crate::diff_compress::CompressionMode::None)
            && store.unique_capture());
        let hot_buffer = if tiered { Some(8usize) } else { None };
        let v = Vec {
            store,
            diff_log,
            hot_stack: std::vec::Vec::new(),
            cold_stack: std::vec::Vec::new(),
            cold_value_pool: std::vec::Vec::new(),
            cold_index_runs: std::vec::Vec::new(),
            hot_buffer,
            full_trail: Ghost(Seq::empty()),
            trail_frames: Ghost(Seq::empty()),
            active_saved_len: <I as IndexLike>::min(),
            phantom: core::marker::PhantomData,
            snapshots: Ghost(Seq::empty()),
        };
        proof {
            I::lemma_min_as_nat();
            assert(v.active_saved_len == I::min_spec());
            assert(v.trail_frames@.len() == 0);
            assert(v.snapshots@.len() == 0);
        }
        v
    }

    /// Capacity reclamation (production parity). `Never` is a no-op;
    /// `IfOverallocated` asks the store to shrink its backing capacity. Both
    /// are observationally inert: `shrink_if` preserves `data()`/`captured()`,
    /// so `view()`, `wf`, and all tracked sequences are unchanged. (The
    /// production diff_log capacity hint is omitted — it's a pure allocator
    /// hint with no effect on `diff_log@`.)
    fn maybe_shrink(&mut self, policy: ShrinkPolicy)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self).store.unique_capture_spec()
                == old(self).store.unique_capture_spec(),
            final(self).view() == old(self).view(),
            final(self).diff_log@ == old(self).diff_log@,
            final(self).trail_frames@ == old(self).trail_frames@,
            final(self).full_trail@ == old(self).full_trail@,
            final(self).snapshots@ == old(self).snapshots@,
            final(self).active_saved_len == old(self).active_saved_len,
    {
        match policy {
            ShrinkPolicy::Never => {}
            ShrinkPolicy::IfOverallocated { factor, headroom } => {
                let ghost pre = *self;
                self.store.shrink_if(factor, headroom);
                proof {
                    // repr_ok reads diff_log@/hot_stack@/full_trail@/g_start,
                    // none of which shrink_if touches (it changes store
                    // capacity only, preserving data()/captured()).
                    assert(self.diff_log@ == pre.diff_log@);
                    assert(self.hot_stack@ == pre.hot_stack@);
                    assert(self.cold_stack@ == pre.cold_stack@);
                    assert(self.full_trail@ == pre.full_trail@);
                    // repr_ok reads only those (all pinned == pre, which
                    // satisfied it via old wf), so it carries by congruence.
                    assert(self.repr_ok());
                }
                // Production parity: the same overallocation check applies to
                // the diff log at mark time (shrink-at-mark ratcheting).
                // Observably inert (contract: element sequence unchanged).
                log_shrink_capacity(&mut self.diff_log, factor, headroom);
            }
        }
        proof {
            // shrink_if preserves data()/captured-under-TRACK; all other
            // fields untouched. Every wf conjunct that reads captured() is
            // TRACK-guarded (frames empty otherwise), so wf transfers.
            assert(self.view() == old(self).view());
            if TRACK {
                assert(self.store.captured() == old(self).store.captured());
                // no-stray-flags transfers pointwise (same flags, same frames).
                assert forall|j: int| 0 <= j < self.view().len()
                    && #[trigger] self.store.captured()[j]
                    implies self.trail_frames@.len() > 0
                        && j < self.active_saved_len.as_nat() by {
                    assert(old(self).store.captured()[j]);
                }
            } else {
                // TRACK=false: frames pinned empty by wf, so every
                // frame-quantified conjunct is vacuous; the one
                // unconditional captured() fact (its length) comes from the
                // trait's wf lemma, not from pointwise preservation.
                assert(self.trail_frames@.len() == 0);
                self.store.lemma_wf_captured_len();
            }
            assert(self.diff_log@ == old(self).diff_log@);
            assert(self.trail_frames@ == old(self).trail_frames@);
            assert(self.full_trail@ == old(self).full_trail@);
            assert(self.snapshots@ == old(self).snapshots@);
            assert forall|k: int| 0 <= k < self.trail_frames@.len() implies
                self.layer_above_at(k) == old(self).layer_above_at(k)
                && self.stratum_end(k) == old(self).stratum_end(k) by {}
            // Reconstruction forall transfers pointwise (all args pinned).
            assert forall|k: int| 0 <= k < self.trail_frames@.len() implies
                #[trigger] frame_inv_range::<T, I>(
                    self.layer_above_at(k), self.full_trail@, self.g_start(k),
                    self.g_end(k), self.snapshots@[k], self.snapshots@[k].len())
            by {
                assert(old(self).frame_inv_range_holds(k));
            }
            // Frame-count bridge and repr_ok carry (stacks/log/trail pinned).
            assert(self.cold_stack@ == old(self).cold_stack@);
            assert(self.hot_stack@ == old(self).hot_stack@);
            assert(self.repr_ok());
        }
    }

    /// Current frame-stack depth (number of live marks). Mirrors production.
    pub fn depth(&self) -> (d: usize)
        requires self.wf(),
        ensures d == self.depth_spec(),
    {
        self.depth_exec()
    }

    /// Depth over the two frame stacks: cold frames are the oldest [0, k),
    /// hot frames the most recent [k, n).
    #[inline]
    pub(crate) fn depth_exec(&self) -> (r: usize)
        requires self.wf_for_snap(),
        ensures r == self.depth_spec(),
    {
        self.cold_stack.len() + self.hot_stack.len()
    }

    /// The frame's saved_len, tier-dispatched by the split point.
    #[inline]
    pub(crate) fn frame_saved_len_exec(&self, k: usize) -> I
        requires self.wf_for_snap(), k < self.depth_spec(),
    {
        if k < self.cold_stack.len() {
            self.cold_stack[k].saved_len
        } else {
            self.hot_stack[k - self.cold_stack.len()].saved_len
        }
    }

    /// Number of entries in the diff log (production parity). The bounded-pop
    /// contract is observable through this: within a frame, first-write-wins
    /// keeps the log at most one entry per captured index, so a pop/push loop
    /// cannot grow it (see tests/compat_bounded_pop.rs).
    pub fn diff_log_len(&self) -> (n: usize)
        requires self.wf(),
        ensures n == self.diff_log_len_spec(),
    {
        self.diff_log.len()
    }

    /// Contiguous read access to the raw values when the backend stores them
    /// contiguously: `Some` for `ParallelStore`, `None` for `InlineStore`
    /// (production parity — the backend-specific fast path).
    pub fn as_slice(&self) -> (r: Option<&[T]>)
        ensures r matches Some(s) ==> s@ == self.view(),
    {
        self.store.as_slice()
    }

    /// Remaining mark-depth headroom before the `u32::MAX` frame cap.
    ///
    /// With the genealogy on the owning `History` (H2), restores no longer
    /// accumulate any per-container state; the only bound is the frame depth.
    /// (`u32::MAX ~ 4.29e9` — not a practical limit.)
    pub fn restores_remaining(&self) -> (r: usize)
        requires self.wf(),
        ensures
            self.depth_spec() < u32::MAX ==>
                r as nat == (u32::MAX - self.depth_spec()) as nat,
            self.depth_spec() >= u32::MAX ==> r == 0,
    {
        (u32::MAX as usize).saturating_sub(self.depth_exec())
    }

    /// A read-only view over the current contents (parity with production).
    pub fn view_handle(&self) -> (v: VecView<'_, T, I, S, TRACK, VC>)
        ensures v.vec_ref() == self,
    {
        VecView { vec: self }
    }

    /// Bytes consumed by diff tracking only: diff_log + frames + fork history.
    /// Diagnostic; no spec content (capacity measurement, external_body).
    /// Production formula (containers/src/vec.rs): CAPACITY-based, not
    /// len-based — this reports the actual allocation footprint.
    #[verifier::external_body]
    pub fn tracking_bytes(&self) -> usize {
        log_heap_bytes(&self.diff_log)
            + self.hot_stack.capacity() * core::mem::size_of::<crate::frame::HotFrame<I>>()
            + self.cold_stack.capacity() * core::mem::size_of::<crate::frame::ColdFrameHdr<I>>()
            + self.cold_index_runs.capacity() * core::mem::size_of::<crate::frame::IndexRun<I>>()
            + self.cold_value_pool.capacity() * core::mem::size_of::<T>()
    }

    /// Total bytes used by this Vec: struct + store backing + tracking.
    /// Diagnostic; no spec content. Production formula:
    /// `size_of::<Self>() + store.heap_bytes() + tracking_bytes()`.
    #[verifier::external_body]
    pub fn total_bytes(&self) -> usize {
        core::mem::size_of::<Self>() + self.store.heap_bytes() + self.tracking_bytes()
    }

    // ------------------------------------------------------------------
    // Total-operation shell: no `requires` beyond wf; every
    // precondition of the partial core is evaluated by a verified exec counterpart
    // and the branch discharges the core's contract as a proof obligation,
    // so the check and the contract cannot drift.
    // ------------------------------------------------------------------

    /// Exec counterpart of `push`'s capacity precondition.
    pub fn can_push(&self) -> (b: bool)
        requires self.wf(),
        ensures b == (self.view().len() + 1 < I::max_nat()),
    {
        let n = self.store.raw_len();
        let cap = <I as crate::index_like::IndexLike>::max().as_usize();
        proof {
            <I as crate::index_like::IndexLike>::lemma_max_nat_positive();
            <I as crate::index_like::IndexLike>::lemma_max_as_nat();
            <I as crate::index_like::IndexLike>::lemma_max_nat_fits_usize();
            assert(n as nat == self.view().len());
            assert(cap as nat == I::max_nat() - 1);
        }
        n < cap
    }

    /// Total push: refuses at the index word's capacity instead of the
    /// partial core's deferred trap-at-next-`len()` protocol.
    pub fn try_push(&mut self, value: T) -> (r: Result<(), crate::error::ContainerError>)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            r is Ok ==> final(self).view() == old(self).view().push(value)
                && final(self).snapshots_view() == old(self).snapshots_view(),
            r is Err ==> final(self).view() == old(self).view()
                && final(self).snapshots_view() == old(self).snapshots_view(),
            r matches Err(e) ==> e == crate::error::ContainerError::CapacityExhausted,
    {
        if self.can_push() {
            self.push(value);
            Ok(())
        } else {
            Err(crate::error::ContainerError::CapacityExhausted)
        }
    }

    /// Total batch push: ONE capacity check licenses the whole slice, the
    /// loop invariant carries the bound to each core `push` — the amortized
    /// form of `try_push` for hot loops (one branch per batch, none per
    /// element).
    pub fn try_extend(&mut self, values: &[T]) -> (r: Result<(), crate::error::ContainerError>)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            r is Ok ==> final(self).view() == old(self).view() + values@,
            r is Err ==> final(self).view() == old(self).view(),
            final(self).snapshots_view() == old(self).snapshots_view(),
            r matches Err(e) ==> e == crate::error::ContainerError::CapacityExhausted,
    {
        let n = self.store.raw_len();
        let cap = <I as crate::index_like::IndexLike>::max().as_usize();
        proof {
            <I as crate::index_like::IndexLike>::lemma_max_nat_positive();
            <I as crate::index_like::IndexLike>::lemma_max_as_nat();
            <I as crate::index_like::IndexLike>::lemma_max_nat_fits_usize();
            assert(n as nat == self.view().len());
            assert(cap as nat == I::max_nat() - 1);
        }
        // `n <= cap` first so `cap - n` cannot underflow; then the batch must
        // fit strictly under the word (`< max_nat` after every push).
        if n > cap || values.len() > cap - n {
            return Err(crate::error::ContainerError::CapacityExhausted);
        }
        let ghost old_view = self.view();
        let mut i: usize = 0;
        while i < values.len()
            invariant
                self.wf(),
                i <= values@.len(),
                self.view() == old_view + values@.subrange(0, i as int),
                self.snapshots_view() == old(self).snapshots_view(),
                old_view.len() + values@.len() < I::max_nat(),
            decreases values@.len() - i,
        {
            proof {
                assert(self.view().len() + 1 < I::max_nat());
            }
            self.push(values[i]);
            proof {
                assert(self.view() =~= old_view + values@.subrange(0, i as int + 1));
            }
            i += 1;
        }
        proof {
            assert(values@.subrange(0, values@.len() as int) =~= values@);
        }
        Ok(())
    }

    /// Exec counterpart of `mark`'s preconditions (TRACK, depth headroom, length
    /// representable in the token's saved_len).
    pub fn can_mark(&self) -> (b: bool)
        requires self.wf(),
        ensures b == (TRACK && self.depth_spec() < u32::MAX
            && self.view().len() < I::max_nat()),
    {
        let n = self.store.raw_len();
        let cap = <I as crate::index_like::IndexLike>::max().as_usize();
        proof {
            <I as crate::index_like::IndexLike>::lemma_max_nat_positive();
            <I as crate::index_like::IndexLike>::lemma_max_as_nat();
            <I as crate::index_like::IndexLike>::lemma_max_nat_fits_usize();
            assert(n as nat == self.view().len());
            assert(cap as nat == I::max_nat() - 1);
        }
        TRACK && self.depth_exec() < (u32::MAX as usize) && n <= cap
    }

    /// Total mark: the error names which precondition failed.
    pub fn try_mark(&mut self, shrink: ShrinkPolicy)
        -> (r: Result<VecToken, crate::error::ContainerError>)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            r matches Ok(token) ==> {
                &&& final(self).view() == old(self).view()
                &&& token.frame_idx_spec() == old(self).depth_spec()
                &&& final(self).depth_spec() == old(self).depth_spec() + 1
                &&& final(self).snapshots_view()
                    == old(self).snapshots_view().push(old(self).view())
            },
            r is Err ==> final(self).view() == old(self).view()
                && final(self).depth_spec() == old(self).depth_spec()
                && final(self).snapshots_view() == old(self).snapshots_view(),
    {
        if !TRACK {
            return Err(crate::error::ContainerError::Untracked);
        }
        if !(self.depth_exec() < (u32::MAX as usize)) {
            return Err(crate::error::ContainerError::DepthLimit);
        }
        proof {
            <I as crate::index_like::IndexLike>::lemma_max_nat_positive();
            <I as crate::index_like::IndexLike>::lemma_max_as_nat();
            <I as crate::index_like::IndexLike>::lemma_max_nat_fits_usize();
        }
        if !(self.store.raw_len() <= <I as crate::index_like::IndexLike>::max().as_usize()) {
            return Err(crate::error::ContainerError::CapacityExhausted);
        }
        Ok(self.mark(shrink))
    }

    /// Total restore: `is_valid_token` already answers exactly "would
    /// `restore` succeed right now" (`is_restorable_spec` is the FULL
    /// runtime-checkable precondition), so the wrapper is the check.
    pub fn try_restore(&mut self, token: VecToken)
        -> (r: Result<(), crate::error::ContainerError>)
        where T: core::default::Default
        requires old(self).wf(),
        ensures
            final(self).wf(),
            r is Ok ==> final(self).view()
                == old(self).snapshots_view()[token.frame_idx_spec() as int]
                && final(self).depth_spec() == token.frame_idx_spec()
                && final(self).snapshots_view()
                    == old(self).snapshots_view().subrange(0, token.frame_idx_spec() as int),
            r is Err ==> final(self).view() == old(self).view()
                && final(self).depth_spec() == old(self).depth_spec()
                && final(self).snapshots_view() == old(self).snapshots_view(),
    {
        if self.is_valid_token(&token) {
            self.restore(token);
            Ok(())
        } else {
            Err(crate::error::ContainerError::InvalidToken)
        }
    }

    /// The index column of the diff-log strata a `restore(token)` would pop:
    /// entries `[frames[token.frame_idx].diff_start, diff_log.len())`. Each
    /// returned index names a slot whose content the restore will roll back
    /// (first-write-wins per stratum under the unique discipline; a
    /// chronological column may repeat an index). An invalid token returns
    /// `None` and the empty case (nothing captured since that mark) returns
    /// an empty vec. Read-only: the column is unchanged.
    ///
    /// This is the map-repair enabler: an unverified associate structure
    /// keyed by slot content (the e-graph's hashcons index) reads this BEFORE
    /// a restore to remove exactly the entries whose keys are about to change,
    /// and re-inserts the same ids from restored content AFTER. The diff log
    /// already carries this set deduplicated, so no separate dirty list is
    /// needed alongside the column.
    #[verifier::external_body]
    pub fn pending_restore_indices(&self, token: &VecToken) -> (r: Option<std::vec::Vec<I>>)
        requires
            self.wf(),
        ensures
            r is Some ==> self.is_restorable_spec(*token),
    {
        if !self.is_valid_token(token) {
            return None;
        }
        let k = self.cold_stack.len();
        let mut out: std::vec::Vec<I> = std::vec::Vec::new();
        if token.frame_idx < k {
            // Cold portion: every run of frames [frame_idx, k) contributes
            // its index span. EXEC-FIRST SCAFFOLD (allocation is fine here:
            // this is a diagnostic/EDU API, not the restore path).
            pending_cold_indices_scaffold(
                &self.cold_stack, &self.cold_index_runs, token.frame_idx, k, &mut out);
            let mut q = 0;
            while q < self.diff_log.len() {
                out.push(log_index(&self.diff_log, q).1);
                q += 1;
            }
        } else {
            let hf = self.hot_stack[token.frame_idx - k];
            let mut q = hf.start;
            while q < self.diff_log.len() {
                out.push(log_index(&self.diff_log, q).1);
                q += 1;
            }
        }
        Some(out)
    }

    /// The public token-validity check: "restorable now", STRUCTURALLY.
    /// Returns exactly `is_restorable_spec(token)` — true iff `restore(token)`
    /// would succeed at this moment: TRACK on, frame still live (rejects
    /// consumed tokens), depth headroom. Branch validity and forgery rejection
    /// live on the owning group's `History` (doc 10 / H2); a raw token past a
    /// branch cut is structurally restorable to the frame now at its index.
    pub fn is_valid_token(&self, token: &VecToken) -> (b: bool)
        requires
            self.wf(),
        ensures
            b == self.is_restorable_spec(*token),
    {
        if !TRACK {
            return false;
        }
        // Frame liveness: a consumed token's frame is gone (design doc 08).
        if token.frame_idx >= self.depth_exec() {
            return false;
        }
        // Headroom (tf.len() < u32::MAX).
        if self.depth_exec() >= u32::MAX as usize {
            return false;
        }
        true
    }

    #[inline(always)]
    pub(crate) fn push(&mut self, value: T)
        requires
            old(self).wf(),
            old(self).view().len() + 1 < I::max_nat(),
        ensures
            final(self).wf(),
            final(self).view() == old(self).view().push(value),
            final(self).snapshots_view() == old(self).snapshots_view(),
    {
        let ghost old_view = self.view();
        let ghost old_self = *self;
        let old_len = self.store.len();
        // Production-compatible overflow protocol: push itself
        // carries NO runtime check — the verified `requires` still obliges
        // every verified caller to prove `view().len() + 1 < I::max_nat()`,
        // and an UNVERIFIED caller who pushes past the index capacity is
        // trapped at the next `len()` read (`"len overflow"`), exactly
        // production's `try_from_usize(..).expect` protocol. The wf invariant
        // (`data().len() < I::max_nat()`) is what the requires protects; the
        // len()-read trap is the unverified-caller backstop.
        self.store.push(value);

        // Pop-into-marked-region bookkeeping: if we are pushing back into a slot that
        // lies inside the active frame's marked region (old_len < active),
        // that slot was popped out of the marked region earlier and the pop
        // already captured snap[old_len] into the top stratum. The fresh slot
        // must therefore INHERIT the captured flag, both to keep the bridge
        // (captured() must match captured_in_range, which is true for that
        // index) and to keep the diff log bounded (a later `set` here must
        // not re-capture). When old_len >= active (the normal transient push)
        // this branch is skipped and the new slot stays uncaptured.
        // Compare via as_usize (whose spec relation to as_nat is concrete),
        // not via lt() — lt_spec is a default trait method whose body is not
        // transparent at the generic `I: IndexLike` use-site.
        // Short-circuit order matches production exactly: TRACK (const,
        // folds) → frames non-empty → the index compare. Under TRACK=false
        // the whole computation erases.
        let reentered = TRACK
            && (self.hot_stack.len() + self.cold_stack.len() > 0)
            && old_len.as_usize() < self.active_saved_len.as_usize();
        let ghost has_frame = TRACK && self.trail_frames@.len() > 0;
        let ghost in_marked = old_len.as_nat() < self.active_saved_len.as_nat();
        proof {
            // TRACK=false: wf pins frames empty, so has_frame is false either way.
            if !TRACK {
                assert(self.trail_frames@.len() == 0);
            }
        }
        proof {
            assert(in_marked == (old_len.as_nat() < self.active_saved_len.as_nat()));
            assert(has_frame == (self.trail_frames@.len() > 0));
            assert(reentered == (self.trail_frames@.len() > 0
                && old_len.as_nat() < self.active_saved_len.as_nat()));
        }
        // push appended captured()[old_len] == false (TRACK-conditional:
        // the flag facts only feed the frame invariants, which are vacuous
        // for TRACK=false since wf pins frames empty).
        proof {
            if TRACK {
                assert(self.store.captured()[old_len.as_nat() as int] == false);
            }
        }
        if reentered {
            // data().len() == old_len + 1 after push, so old_len is in bounds.
            self.store.mark_captured(old_len);
        }
        proof {
            if TRACK {
                // Merged: captured()[old_len] is exactly `reentered`; prefix
                // [0, old_len) unchanged (push appends at old_len;
                // mark_captured, if it ran, updates only old_len).
                assert(self.store.captured()[old_len.as_nat() as int] == reentered);
                assert forall|j: int| 0 <= j < old_len.as_nat() implies
                    #[trigger] self.store.captured()[j] == old_self.store.captured()[j] by {}
                // no-stray-flags: prefix flags carry the old invariant; the
                // new slot's flag is `reentered`, which by construction means
                // a live frame and old_len < active.
                assert forall|j: int| 0 <= j < self.view().len()
                    && #[trigger] self.store.captured()[j]
                    implies self.trail_frames@.len() > 0
                        && j < self.active_saved_len.as_nat() by {
                    if j < old_len.as_nat() as int {
                        assert(old_self.store.captured()[j]);
                    } else {
                        assert(j == old_len.as_nat() as int);
                        assert(reentered);
                    }
                }
            }
        }
        // diff_log, frames, snapshots all unchanged. Only `view` changed,
        // by appending one element. Inner frames' frame_inv_range references
        // snapshots (unchanged) as `above`. The TOP frame references `view`;
        // re-establish its frame_inv_range explicitly.
        proof {
            assert(self.view() == old_view.push(value));
            assert(self.trail_frames@ == old_self.trail_frames@);
            assert(self.full_trail@ == old_self.full_trail@);
            assert(self.diff_log@ == old_self.diff_log@);
            assert(self.snapshots@ == old_self.snapshots@);
            let tf = self.trail_frames@;
            let diffs = self.full_trail@;
            assert forall|k: int| 0 <= k < tf.len() implies
                #[trigger] frame_inv_range::<T, I>(
                    self.layer_above_at(k),
                    self.full_trail@,
                    self.g_start(k),
                    self.g_end(k),
                    self.snapshots@[k],
                    self.snapshots@[k].len())
            by {
                // old frame_inv_range held for old_self with same args except
                // possibly layer_above_at (which equals view for top frame).
                assert(old_self.frame_inv_range_holds(k));
                if k + 1 < tf.len() {
                    // inner frame: layer_above unchanged (snapshot).
                    assert(self.layer_above_at(k) == old_self.layer_above_at(k));
                } else {
                    // top frame: layer is view, changed by push but prefix
                    // preserved. Coverage-based (no saved_len <= view bound).
                    self.lemma_saved_len_le_view_from(old_self, k);
                }
            }
            // Bridge: store.push appended captured()[old_len]==false; if we
            // then mark_captured(old_len) it's true. For j < old_len the flag
            // and the diffs are unchanged, so the old bridge transfers; for
            // j == old_len (only relevant when old_len < active) the
            // mark_captured set it true, matching captured_in_range (snap was
            // captured by the earlier pop — coverage).
            self.store.lemma_wf_captured_len();
            if tf.len() > 0 {
                let top = (tf.len() - 1) as int;
                let ds_top = self.g_start(top);
                assert(self.active_saved_len.as_nat() == self.g_saved_len(top as int));
                assert forall|j: int|
                    0 <= j < self.active_saved_len.as_nat() && j < self.view().len() implies
                    #[trigger] self.store.captured()[j]
                        == captured_in_range::<T, I>(diffs, ds_top, diffs.len() as int, j as nat)
                by {
                    if j < old_len.as_nat() {
                        // unchanged flag, unchanged diffs ⇒ old bridge applies.
                        assert(self.store.captured()[j] == old_self.store.captured()[j]);
                        assert(j < old_self.view().len());
                        assert(old_self.store.captured()[j]
                            == captured_in_range::<T, I>(
                                old_self.full_trail@, ds_top, old_self.full_trail@.len() as int, j as nat));
                    } else {
                        // j == old_len: only present when old_len < view.len(),
                        // i.e. old_len < active (the mark_captured branch ran).
                        // captured()[old_len] == true; and the top frame's
                        // coverage arm (j < active, uncaptured ⇒ j < view.len)
                        // forces this popped cell to be captured_in_range.
                        assert(j == old_len.as_nat());
                        assert(j < self.active_saved_len.as_nat());
                        // The exec branch `old_len.lt(active)` ran (its spec is
                        // old_len.as_nat() < active.as_nat()), so mark_captured
                        // set captured()[old_len] = true.
                        assert(old_len.as_nat() < self.active_saved_len.as_nat());
                        assert(in_marked);
                        assert(has_frame);  // tf.len() > 0 (outer if)
                        assert(reentered);  // ⇒ captured()[old_len] == true
                        // old_self top frame_cell_inv at j: j < active == saved_top,
                        // and j >= old_view.len() (popped) ⇒ captured arm.
                        assert(old_self.frame_inv_range_holds(top));
                        lemma_frame_inv_arm_at::<T, I>(
                            old_self.layer_above_at(top), old_self.full_trail@, ds_top,
                            old_self.g_end(top), old_self.snapshots@[top],
                            old_self.snapshots@[top].len(), j);
                        assert(old_self.layer_above_at(top) == old_view);
                        assert(j >= old_view.len());  // old_len == old_view.len()
                        // uncaptured arm would need j < old_view.len(): false.
                        // So captured_in_range(old_diffs, ds_top, |old_diffs|, j).
                        assert(captured_in_range::<T, I>(
                            old_self.full_trail@, ds_top, old_self.full_trail@.len() as int, j as nat));
                        assert(self.store.captured()[j] == true);
                    }
                }
            }
        }
    }

    /// Helper used in proofs: assert frame_inv_range for frame k from wf.
    pub open(crate) spec fn frame_inv_range_holds(&self, k: int) -> bool {
        frame_inv_range::<T, I>(
            self.layer_above_at(k),
            self.full_trail@,
            self.g_start(k),
            self.g_end(k),
            self.snapshots@[k],
            self.g_saved_len(k))
    }

    /// Carry the top frame's `frame_inv_range` across a push (old_self had wf;
    /// the new view is the old view plus appended elements). Coverage-based:
    /// no `saved_len <= view.len()` needed — the per-cell uncaptured arm itself
    /// supplies `j < above_old.len()`, and the appended view agrees on the old
    /// prefix, so the arm transfers cell-by-cell.
    pub(crate) proof fn lemma_saved_len_le_view_from(&self, old_self: Self, k: int)
        requires
            old_self.wf(),
            self.trail_frames@ == old_self.trail_frames@,
            self.full_trail@ == old_self.full_trail@,
            self.snapshots@ == old_self.snapshots@,
            self.diff_log@ == old_self.diff_log@,
            old_self.view().len() <= self.view().len(),
            (forall|j: int| 0 <= j < old_self.view().len() ==>
                #[trigger] self.view()[j] == old_self.view()[j]),
            0 <= k < self.trail_frames@.len(),
            k + 1 == self.trail_frames@.len(),
        ensures
            self.frame_inv_range_holds(k),
    {
        assert(old_self.frame_inv_range_holds(k));
        let above_old = old_self.view();
        let above_new = self.view();
        // Reconstruction is over the ghost trail; self.full_trail@ ==
        // old_self.full_trail@ (requires), so `diffs` is the old stratum.
        let diffs = self.full_trail@;
        let lo = self.g_start(k);
        let hi = self.g_end(k);
        let snap = self.snapshots@[k];
        let sl = snap.len();
        assert(self.layer_above_at(k) == above_new);
        assert(old_self.layer_above_at(k) == above_old);
        assert(self.g_end(k) == old_self.g_end(k));
        // Per-cell transfer: same diffs/snap; view prefix preserved & longer.
        assert forall|j: int| 0 <= j < sl as int implies
            #[trigger] frame_cell_inv::<T, I>(above_new, diffs, lo, hi, snap, j)
        by {
            lemma_frame_inv_arm_at::<T, I>(above_old, diffs, lo, hi, snap, sl, j);
            // captured arm is layer-independent; uncaptured arm: old gave
            // j < above_old.len() && above_old[j]==snap[j], and above_new is
            // longer and agrees on the old prefix — so j < above_new.len()
            // and above_new[j]==snap[j]. No saved_len<=view bound required.
        }
    }

    /// Pop the last element (FAITHFUL: may pop into a frame's marked region).
    ///
    /// If the removed slot lies inside the active frame's marked region
    /// (`old_len - 1 < active_saved_len`), it is first CAPTURED into the top
    /// stratum (first-write-wins), so the now-absent cell still satisfies the
    /// frame invariant via the captured arm — this is exactly the coverage
    /// obligation. Conditional capture (not production's unconditional
    /// force_capture) keeps the diff log bounded: at most one entry per index
    /// per stratum. `restore` later regrows the popped region with
    /// `resize_default` and overwrites each filler back from these captures.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(300)]
    #[inline(always)]
    pub fn pop(&mut self) -> (r: Option<T>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            old(self).view().len() == 0 ==> r is None && final(self).view() == old(self).view(),
            old(self).view().len() > 0 ==> {
                &&& r is Some
                &&& r->Some_0 == old(self).view()[old(self).view().len() - 1]
                &&& final(self).view() == old(self).view().drop_last()
            },
            final(self).snapshots_view() == old(self).snapshots_view(),
    {
        let ghost old_view = self.view();
        let ghost old_diffs = self.diff_log@;
        let ghost old_tf = self.trail_frames@;
        let ghost old_ft = self.full_trail@;

        // Capture the cell we are about to remove, if it falls inside the
        // active marked region. Must happen BEFORE store.pop while data[last]
        // is still readable; capture's first-write-wins logs (data[last], last)
        // == (snap[last], last) only if it was uncaptured, else no-ops.
        let len = self.store.len();
        let ghost old_store_captured = self.store.captured();
        let ghost captured_marked = false;
        let ghost last_g: int = 0;
        // data_last == value of the slot being removed (defined when nonempty).
        let ghost data_last: T = old(self).store.data()[
            if old_view.len() > 0 { old_view.len() - 1 } else { 0 } as int];
        if TRACK && self.depth_exec() > 0 && len.as_usize() > 0
            && len.as_usize() - 1 < self.active_saved_len.as_usize()
        {
            let last = len.as_usize() - 1;
            proof { len.lemma_as_nat_bounded(); }  // last < len.as_nat() < max_nat
            let last_i = match I::try_from_usize(last) {
                Some(x) => x,
                None => { assert(false); return None; },
            };
            let active = self.active_saved_len;
            proof {
                captured_marked = true;
                last_g = last as int;
                assert(last_i.as_nat() == last as nat);
                assert(last_i.as_nat() < active.as_nat());
                assert(self.store.data()[last as int] == data_last);
            }
            let ghost old_full_p = self.full_trail@;
            self.store.capture(last_i, active, &mut self.diff_log);
            proof {
                // Ghost trail records the reentered-slot capture.
                if (last as int) < active.as_nat() as int {
                    self.full_trail@ = old_full_p.push((data_last, last_i));
                }
                // capture's outcome at index `last`, by discipline:
                //  - if !old.captured[last]: appended (data_last, last_i);
                //  - else, unique store: no-op;
                //  - else, chronological store: appended the duplicate.
                // All three ways the result diff log relates to old_diffs by
                // "append-one-at-index-last or identity".
                if !old_store_captured[last as int] {
                    assert(self.diff_log@ == old_diffs.push((data_last, last_i)));
                    assert(self.diff_log@[old_diffs.len() as int].1.as_nat() == last as nat);
                } else if old(self).store.unique_capture_spec() {
                    assert(self.diff_log@ == old_diffs);
                } else {
                    assert(self.diff_log@ == old_diffs.push((data_last, last_i)));
                    assert(self.diff_log@[old_diffs.len() as int].1.as_nat() == last as nat);
                }
                // capture changes the flag only at `last == len-1`; surface
                // the SAME-shaped fact both branches will share post-if.
                assert(last as int == len.as_nat() - 1);
                // capture preserves data() ⇒ captured() length unchanged
                // (both equal data().len(), which capture leaves intact).
                self.store.lemma_wf_captured_len();
                old(self).store.lemma_wf_captured_len();
                assert(self.store.data() == old(self).store.data());
                assert(self.store.captured().len() == old_store_captured.len());
                assert forall|j: int| 0 <= j < len.as_nat() - 1
                    implies #[trigger] self.store.captured()[j] == old_store_captured[j] by {
                    // capture's ensures: either first-write-wins (forall
                    // k != last_i.as_nat() preserved) or no-op (captured()
                    // unchanged). Either way j (!= last == last_i.as_nat()) is
                    // preserved.
                    assert(j != last_i.as_nat());
                    assert(j < self.store.captured().len());
                }
            }
        } else {
            // No capture: the store is entirely unchanged — same shape.
            proof {
                assert(self.store.captured() =~= old_store_captured);
                assert forall|j: int| 0 <= j < len.as_nat() - 1
                    implies #[trigger] self.store.captured()[j] == old_store_captured[j] by {}
            }
        }
        // mid state (after the optional capture, before pop): both branches
        // established flags below `len-1` match old_store_captured.
        let ghost mid_captured = self.store.captured();

        let ghost mid_diffs = self.diff_log@;
        // diffs is old_diffs, or old_diffs.push(e) with e.1 == last_g (== new_len).
        let r = self.store.pop();

        proof {
            let tf = self.trail_frames@;
            let diffs = self.diff_log@;
            let snaps = self.snapshots@;
            // capture/pop leave frames & snapshots unchanged. diff_log is
            // either old_diffs (no capture) or old_diffs.push((snap[last],last)).
            assert(tf == old_tf);
            assert(snaps == old(self).snapshots@);
            assert(diffs == mid_diffs);
            if !TRACK {
                // frames pinned empty: every captured()-reading wf conjunct
                // is frame-quantified, hence vacuous; captured().len() comes
                // from the trait's wf lemma.
                assert(tf.len() == 0);
                self.store.lemma_wf_captured_len();
            }

            if old_tf.len() > 0 && old_view.len() > 0 {
                let top = (tf.len() - 1) as int;
                let new_len = (old_view.len() - 1) as int;  // == self.view().len()
                let ds_top = self.g_start(top);
                let active_n = self.active_saved_len.as_nat() as int;
                assert(self.view() == old_view.drop_last());
                assert(self.g_saved_len(top as int) == self.active_saved_len.as_nat());  // wf
                // last == new_len == old_view.len()-1; captured_marked iff
                // new_len < active.
                assert(captured_marked == (new_len < active_n));

                // Unified relation between diffs and old_diffs: either equal
                // (no capture, or capture no-op'd on an already-captured slot)
                // or old_diffs with ONE entry appended whose index is new_len.
                // This is exactly the hypothesis lemma_captured_in_range_append_
                // other needs, for every j != new_len.
                assert(diffs == old_diffs
                    || (diffs.len() == old_diffs.len() + 1
                        && diffs.subrange(0, old_diffs.len() as int) == old_diffs
                        && diffs[old_diffs.len() as int].1.as_nat() == new_len as nat)) by {
                    if captured_marked && (!old_store_captured[new_len]
                        || !old(self).store.unique_capture_spec()) {
                        assert(diffs == old_diffs.push((data_last, diffs[old_diffs.len() as int].1)));
                        assert(diffs.subrange(0, old_diffs.len() as int) == old_diffs);
                    }
                }

                // What capture did to the diff log & flags. Let last = new_len.
                // If captured_marked: capture saw i=last < active. First-write-
                // wins: if !old.captured[last] it appended (snap[last], last)
                // and set the flag; else no-op. Either way after capture the
                // top stratum HITS last with value snap[last], and for all
                // j != last the flags/entries are unchanged.
                self.store.lemma_wf_captured_len();

                // Ghost-trail bindings for the reconstruction/bridge (pop appends
                // (data_last, last) to full_trail iff captured_marked; else no-op).
                let gt = self.full_trail@;
                let old_gt = old(self).full_trail@;
                assert(gt == old_gt || (gt.len() == old_gt.len() + 1
                    && gt.subrange(0, old_gt.len() as int) == old_gt
                    && gt[old_gt.len() as int].1.as_nat() == new_len as nat)) by {
                    if captured_marked { assert(gt == old_gt.push((data_last, gt[old_gt.len() as int].1))); }
                }
                // --- frame_inv_range for every frame ---
                assert forall|k: int| 0 <= k < tf.len() implies
                    #[trigger] frame_inv_range::<T, I>(
                        self.layer_above_at(k), gt, self.g_start(k),
                        self.g_end(k), snaps[k], snaps[k].len())
                by {
                    assert(old(self).frame_inv_range_holds(k));
                    let lo = self.g_start(k);
                    let hi = self.g_end(k);
                    let snap = snaps[k];
                    let sl = snaps[k].len();
                    if k < top {
                        // Inner frame: layer is an unchanged snapshot; its
                        // stratum [ds_k, ds_{k+1}) lies below the top stratum,
                        // so a capture append at the end doesn't touch it.
                        assert(self.layer_above_at(k) == snaps[k + 1]);
                        assert(self.layer_above_at(k) == old(self).layer_above_at(k));
                        assert(hi == old(self).stratum_end(k));
                        assert(hi == old(self).g_start(k + 1));
                        old(self).lemma_diff_start_le_n(k + 1);
                        old(self).lemma_diff_start_monotone(k + 1, top);
                        assert(hi <= old_gt.len() as int);
                        lemma_frame_inv_range_local::<T, I>(
                            self.layer_above_at(k), old_gt, gt, lo, hi, snap, sl);
                    } else {
                        // Top frame. Layer is the (shortened) view; stratum
                        // [ds_top, n) possibly extended by the capture append
                        // at index `last == new_len`. Per cell j < sl:
                        //   j < new_len  : present, value & captured-status
                        //                  preserved ⇒ old arm transfers;
                        //   j == new_len : now ABSENT. If captured_marked the
                        //                  capture put (snap[last],last) in the
                        //                  stratum (captured arm); coverage.
                        //   j > new_len  : was already absent in old state, so
                        //                  old captured arm held; entry survives.
                        assert(self.layer_above_at(k) == self.view());
                        assert(old(self).layer_above_at(k) == old_view);
                        assert(sl == active_n);
                        // old top stratum ended at old_gt.len().
                        old(self).lemma_diff_start_le_n(top);
                        assert(old(self).g_end(top) == old_gt.len() as int);
                        assert(frame_inv_range::<T, I>(
                            old_view, old_gt, lo, old_gt.len() as int, snap, sl));
                        assert forall|j: int| 0 <= j < sl as int implies
                            #[trigger] frame_cell_inv::<T, I>(self.view(), gt, lo, hi, snap, j)
                        by {
                            lemma_frame_inv_arm_at::<T, I>(
                                old_view, old_gt, lo, old_gt.len() as int, snap, sl, j);
                            if j < new_len {
                                // present & preserved by drop_last; capture
                                // append (if any) is at index last != j.
                                assert(self.view()[j] == old_view[j]);
                                lemma_captured_in_range_append_other::<T, I>(
                                    old_gt, gt, lo, j as nat, new_len as nat);
                            } else if j == new_len {
                                // The cell just removed. It was inside the
                                // marked region (j < active == sl), so the
                                // capture ran (captured_marked). The capture
                                // arm holds: there is an entry in [lo, hi) with
                                // index j == new_len and value snap[j].
                                assert(j < active_n);
                                assert(captured_marked);
                                assert(hi == gt.len());  // top stratum end
                                // old cell_inv at j (from lemma_frame_inv_arm_at
                                // above): j == new_len == old_view.len()-1, so
                                // j < old_view.len() ⇒ if old-uncaptured then
                                // old_view[j] == snap[j]; if old-captured the
                                // old entry already holds snap[j].
                                // The cell_inv for j must be the CAPTURED arm:
                                // exhibit p in [lo,hi) with index j, value snap[j].
                                if old_store_captured[j] {
                                    // already captured: a unique store no-op'd
                                    // (gt == old_gt); a chronological
                                    // store appended a duplicate at index j.
                                    // Either way old_gt is a prefix of
                                    // gt, so the old captured arm's FIRST-
                                    // hitter witness survives in place
                                    // (first_hitter constrains only positions
                                    // below it, which are unchanged).
                                    assert(j < old_view.len());
                                    assert(old(self).store.captured()[j]);  // == old_store_captured[j]
                                    assert(captured_in_range::<T, I>(
                                        old_gt, lo, old_gt.len() as int, j as nat)) by {
                                        assert(old(self).store.captured()[j]
                                            == captured_in_range::<T, I>(
                                                old_gt, lo, old_gt.len() as int, j as nat));
                                    }
                                    // old captured arm gives the value + first-hitter witness.
                                    assert(frame_cell_inv::<T, I>(
                                        old_view, old_gt, lo, old_gt.len() as int, snap, j));
                                    assert(gt.subrange(0, old_gt.len() as int) == old_gt) by {
                                        if gt == old_gt {
                                            assert(gt.subrange(0, old_gt.len() as int)
                                                =~= old_gt);
                                        }
                                    }
                                    let p = choose|p: int| lo <= p < old_gt.len() as int
                                        && (#[trigger] old_gt[p]).1.as_nat() == j as nat
                                        && old_gt[p].0 == snap[j]
                                        && first_hitter::<T, I>(old_gt, lo, p, j as nat);
                                    assert(gt[p] == old_gt[p]) by {
                                        assert(gt.subrange(0, old_gt.len() as int)[p]
                                            == gt[p]);
                                    }
                                    assert(first_hitter::<T, I>(gt, lo, p, j as nat)) by {
                                        assert forall|q: int| lo <= q < p implies
                                            (#[trigger] gt[q]).1.as_nat() != j as nat by {
                                            assert(gt.subrange(0, old_gt.len() as int)[q]
                                                == gt[q]);
                                            assert(gt[q] == old_gt[q]);
                                        }
                                    }
                                    assert(lo <= p < hi && 0 <= p < gt.len()
                                        && gt[p].1.as_nat() == j as nat
                                        && gt[p].0 == snap[j]);
                                    assert(captured_in_range::<T, I>(gt, lo, hi, j as nat));
                                    assert(frame_cell_inv::<T, I>(self.view(), gt, lo, hi, snap, j));
                                } else {
                                    // uncaptured: capture appended (data_last, last_i)
                                    // at position old_gt.len(); data_last ==
                                    // old.data[j] == old_view[j] == snap[j] (old
                                    // uncaptured arm).
                                    assert(!captured_in_range::<T, I>(
                                        old_gt, lo, old_gt.len() as int, j as nat)) by {
                                        assert(j < old_view.len());
                                        assert(old(self).store.captured()[j] == false);
                                        assert(old(self).store.captured()[j]
                                            == captured_in_range::<T, I>(
                                                old_gt, lo, old_gt.len() as int, j as nat));
                                    }
                                    assert(frame_cell_inv::<T, I>(
                                        old_view, old_gt, lo, old_gt.len() as int, snap, j));
                                    assert(old_view[j] == snap[j]);  // old uncaptured arm
                                    assert(data_last == old_view[j]);
                                    let p = old_gt.len() as int;
                                    assert(gt.subrange(0, p) == old_gt);
                                    assert(gt[p].1.as_nat() == j as nat);
                                    assert(gt[p].0 == data_last);
                                    assert(gt[p].0 == snap[j]);
                                    assert(lo <= p < hi && 0 <= p < gt.len());
                                    // The appended entry is the stratum's first
                                    // hitter of j: no prior entry hits j (the
                                    // old bridge said j was uncaptured).
                                    assert(first_hitter::<T, I>(gt, lo, p, j as nat)) by {
                                        assert forall|q: int| lo <= q < p implies
                                            (#[trigger] gt[q]).1.as_nat() != j as nat by {
                                            assert(gt.subrange(0, p)[q] == gt[q]);
                                            assert(gt[q] == old_gt[q]);
                                        }
                                    }
                                    assert(captured_in_range::<T, I>(gt, lo, hi, j as nat));
                                    assert(frame_cell_inv::<T, I>(self.view(), gt, lo, hi, snap, j));
                                }
                            } else {
                                // j > new_len: this cell was ALREADY absent
                                // before this pop (j >= old_view.len()-... it
                                // was popped earlier). The old uncaptured arm
                                // would need j < old_view.len(): j > new_len ==
                                // old_view.len()-1 ⇒ j >= old_view.len(), so the
                                // old cell_inv took the CAPTURED arm. That entry
                                // is below old_gt.len() <= gt.len() and is
                                // preserved by the capture append.
                                assert(j >= old_view.len());
                                assert(captured_in_range::<T, I>(
                                    old_gt, lo, old_gt.len() as int, j as nat));
                                lemma_captured_in_range_append_other::<T, I>(
                                    old_gt, gt, lo, j as nat, new_len as nat);
                            }
                        }
                        assert(frame_inv_range::<T, I>(self.view(), gt, lo, hi, snap, sl));
                    }
                }

                // --- bridge (gated by j < active && j < view.len()) ---
                assert forall|j: int|
                    0 <= j < active_n && j < self.view().len() implies
                    #[trigger] self.store.captured()[j]
                        == captured_in_range::<T, I>(gt, ds_top, gt.len() as int, j as nat)
                by {
                    // j < view.len() == new_len, so j != last (== new_len). The
                    // capture append (if any) is at index last != j, and pop's
                    // drop_last removes the flag at last (>= new_len > j). So
                    // both captured()[j] and captured_in_range(j) are unchanged
                    // from the old top-stratum bridge.
                    assert(j < new_len);
                    assert(j < old_view.len());
                    // pop's drop_last: captured()[j] == mid_captured[j] for
                    // j < new_len; and mid_captured[j] == old flag (capture
                    // only touched index new_len != j).
                    assert(self.store.captured()[j] == mid_captured[j]);
                    assert(mid_captured[j] == old(self).store.captured()[j]);
                    assert(old(self).store.captured()[j]
                        == captured_in_range::<T, I>(
                            old_gt, ds_top, old_gt.len() as int, j as nat));
                    lemma_captured_in_range_append_other::<T, I>(
                        old_gt, gt, ds_top, j as nat, new_len as nat);
                }

            } else if old_tf.len() > 0 {
                // old_view empty (so view stays empty): store.pop is a no-op
                // and the capture branch can't have run (len == 0). So the
                // entire state equals old(self), and old wf transfers directly.
                let gt = self.full_trail@;
                let old_gt = old(self).full_trail@;
                assert(old_view.len() == 0);
                assert(self.view() == old_view);
                assert(gt == old_gt);
                assert(self.store.captured() == old(self).store.captured());
                assert forall|k: int| 0 <= k < tf.len() implies
                    #[trigger] frame_inv_range::<T, I>(
                        self.layer_above_at(k), gt, self.g_start(k),
                        self.g_end(k), snaps[k], snaps[k].len())
                by {
                    assert(old(self).frame_inv_range_holds(k));
                    assert(self.layer_above_at(k) == old(self).layer_above_at(k));
                }
            }
        }
        r
    }

    /// Write `value` at index `i`, capturing the old value into the active
    /// frame's stratum (first-write-wins) when a frame is live. Works at any
    /// stack depth.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(200)]
    #[inline(always)]
    pub fn set_index(&mut self, i: I, value: T)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            i.as_nat() < old(self).view().len() ==> {
                &&& final(self).view() == old(self).view().update(i.as_nat() as int, value)
                &&& final(self).snapshots_view() == old(self).snapshots_view()
            },
    {
        // Total-with-documented-panic (hot family): explicit bound branch.
        if !(i.as_usize() < self.store.raw_len()) {
            crate::guard::refuse("Vec::set_index: index out of bounds");
        }
        let ghost old_view = self.view();
        let ghost old_diffs = self.diff_log@;
        let ghost old_tf = self.trail_frames@;
        let ghost old_ft = self.full_trail@;
        let ghost n = old_diffs.len() as int;

        let ghost active_n = self.active_saved_len.as_nat();
        let ghost iu = i.as_nat() as int;
        let ghost was_captured0 = self.store.captured()[iu];
        if TRACK && self.depth_exec() > 0 {
            let active = self.active_saved_len;
            let ghost old_full = self.full_trail@;
            self.store.capture(i, active, &mut self.diff_log);
            proof {
                // Ghost trail: record this write iff it is a genuine tracked
                // capture (in the marked region). Representation-independent -
                // the physical diff_log dedupes under the unique discipline,
                // full_trail never does.
                if iu < active_n as int {
                    self.full_trail@ = old_full.push((old_view[iu], i));
                }
                // Surface capture's per-discipline outcome explicitly.
                if iu < active_n as int && !was_captured0 {
                    assert(self.diff_log@ == old_diffs.push((old_view[iu], i)));
                    assert(self.store.captured()[iu] == true);
                } else if iu < active_n as int
                    && !old(self).store.unique_capture_spec() {
                    // chronological duplicate: appended, flags unchanged.
                    assert(self.diff_log@ == old_diffs.push((old_view[iu], i)));
                    assert(self.store.captured()[iu] == true);
                } else {
                    assert(self.diff_log@ == old_diffs);
                }
            }
        }
        let ghost mid_diffs = self.diff_log@;
        self.store.set_raw(i, value);

        proof {
            let tf = self.trail_frames@;
            let diffs = self.diff_log@;
            let gt = self.full_trail@;
            let old_gt = old(self).full_trail@;
            let snaps = self.snapshots@;

            // set_raw leaves diff_log unchanged and (when TRACK) the store's
            // captured() too; it only updates view[iu]. capture left view
            // unchanged. So overall: view == old_view.update(iu, value), and
            // diffs == mid_diffs (whatever capture produced).
            assert(self.view() == old_view.update(iu, value));
            assert(diffs == mid_diffs);
            assert(tf == old_tf);

            // wf's `captured().len() == view().len()` is UNCONDITIONAL, but
            // `set_raw` now preserves captured() only when TRACK (it skips the
            // dead flag maintenance otherwise — see its postcondition). Get the
            // length from the store's own wf instead of from flag preservation,
            // so the untracked case is covered too.
            self.store.lemma_wf_captured_len();

            if old_tf.len() == 0 {
                assert(diffs.len() == 0);
            } else {
                let top = (tf.len() - 1) as int;
                let was_captured = was_captured0;
                // "appended" covers both append cases: the first write, and a
                // chronological store's duplicate on an already-captured slot.
                let appended = iu < active_n as int && (!was_captured0
                    || !old(self).store.unique_capture_spec());
                assert(old(self).store.captured()[iu] == was_captured0);

                // capture either no-ops or appends one entry at the end.
                // In both cases the prefix [0, old_diffs.len()) is preserved
                // and diffs.len() >= old_diffs.len().
                assert(old_diffs.len() <= diffs.len());

                // The GHOST trail append is unconditional on the store
                // discipline: a tracked write in the marked region appends
                // exactly (old_view[iu], i) (my mutator wiring); otherwise
                // the trail is unchanged. This - not diff_log's
                // discipline-specific shape - is what wf's reconstruction and
                // capture-bridge clauses read.
                let appended_g = iu < active_n as int;
                if appended_g {
                    assert(gt == old_gt.push((old_view[iu], i)));
                } else {
                    assert(gt == old_gt);
                }
                assert(old_gt.len() <= gt.len());
                assert(forall|m: int| 0 <= m < old_gt.len() ==>
                    #[trigger] gt[m] == old_gt[m]);
                old(self).lemma_diff_start_le_n(top);
                assert(self.g_start(top) <= old_gt.len());
                assert(forall|m: int| 0 <= m < old_diffs.len() ==>
                    #[trigger] diffs[m] == old_diffs[m]);
                // The top frame's ghost diff_start <= old ghost trail len.
                old(self).lemma_diff_start_le_n(top);
                assert(self.g_start(top) <= old_gt.len());

                // capture's effect on diffs:
                //   - if iu < active && !was_captured: diffs == old_diffs.push((old_view[iu], i))
                //   - else: diffs == old_diffs.
                // Either way, for every k, the stratum of frame k changes only
                // possibly at the top frame (an append extends [top.ds, n)).

                // Frame_inv_range for every k, over the GHOST trail.
                // Terms match wf_for_snap's clause exactly (g_end / snaps.len)
                // so the forall trigger fires.
                assert forall|k: int| 0 <= k < tf.len() implies
                    #[trigger] frame_inv_range::<T, I>(
                        self.layer_above_at(k), gt, self.g_start(k),
                        self.g_end(k), snaps[k], snaps[k].len())
                by {
                    assert(old(self).frame_inv_range_holds(k));
                    assert(self.trail_frames@[k] == old(self).trail_frames@[k]);
                    assert(snaps[k] == old(self).snapshots@[k]);
                    if k < top {
                        // Inner frame: layer is snaps[k+1] (unchanged), and
                        // its stratum [ds_k, ds_{k+1}) lies entirely below the
                        // top stratum, so the capture append (at the end of
                        // gt) doesn't touch it.
                        assert(self.layer_above_at(k) == snaps[k + 1]);
                        assert(self.layer_above_at(k) == old(self).layer_above_at(k));
                        let hi = self.stratum_end(k);
                        assert(hi == old(self).stratum_end(k));
                        assert(hi == old(self).g_start(k + 1));
                        old(self).lemma_diff_start_le_n(k + 1);
                        old(self).lemma_diff_start_monotone(k + 1, top);
                        // hi <= top.diff_start <= old_gt.len(): inner
                        // stratum entirely within the preserved prefix.
                        assert(hi <= old_gt.len() as int);
                        lemma_frame_inv_range_local::<T, I>(
                            self.layer_above_at(k), old_gt, gt,
                            self.g_start(k), hi, snaps[k],
                            self.g_saved_len(k));
                    } else {
                        // Top frame: layer is the view (changed at iu); stratum
                        // [ds_top, gt.len()) possibly extended by capture.
                        let ds = self.g_start(top);
                        let hi = self.stratum_end(k);
                        let sl = self.g_saved_len(top);
                        assert(hi == gt.len() as int);
                        assert(self.g_saved_len(top as int) == self.active_saved_len.as_nat());
                        assert(sl == active_n);
                        assert(self.layer_above_at(k) == self.view());
                        assert(old(self).layer_above_at(k) == old_view);
                        assert(old(self).frame_inv_range_holds(top));
                        old(self).lemma_diff_start_le_n(top);
                        let new_view = self.view();
                        let snap = snaps[top];

                        // The capture step gives us (from its postcondition):
                        //   if iu < active_n && !was_captured:
                        //     gt == old_gt.push((old_view[iu], i))
                        //   else: gt == old_gt.
                        // In `set` we always have iu < view.len(); the active
                        // marked region is [0, active_n) == [0, sl).

                        // Structural conjuncts. (No `sl <= view.len()`: that
                        // top-fullness fact is gone; frame_inv_range's per-cell
                        // uncaptured arm carries the only presence bound needed.)
                        assert(snap.len() == sl);
                        assert(new_view.len() == old_view.len());
                        assert forall|m: int| ds <= m < hi implies
                            (#[trigger] gt[m]).1.as_nat() < sl by {
                            if m < old_gt.len() {
                                assert(gt[m] == old_gt[m]);
                            } else {
                                assert(appended_g);
                                assert(gt[m] == (old_view[iu], i));
                            }
                        }
                        // (Stratum uniqueness is no longer a frame_inv_range
                        // conjunct; the unique-discipline wf clause is
                        // re-established after this loop.)
                        // two-arm, per-cell via frame_cell_inv.
                        assert forall|j: int| 0 <= j < sl as int implies
                            #[trigger] frame_cell_inv::<T, I>(new_view, gt, ds, hi, snap, j)
                        by {
                            assert(old(self).frame_inv_range_holds(top));
                            lemma_frame_inv_arm_at::<T, I>(
                                old_view, old_gt, ds, old_gt.len() as int, snap, sl, j);
                            // bridge at j: old captured()[j] iff j in old top stratum.
                            if j == iu {
                                // j is captured now; find a FIRST-hitter
                                // witness with value snap[iu].
                                if !was_captured {
                                    // first write: capture appended
                                    // (old_view[iu], i) at the end, and no
                                    // earlier stratum entry hits iu (bridge,
                                    // flag clear) — the append is first.
                                    assert(!captured_in_range::<T, I>(
                                        old_gt, ds, old_gt.len() as int, iu as nat)) by {
                                        assert(old(self).store.captured()[iu] == false);
                                    }
                                    assert(old_view[iu] == snap[iu]);
                                    let newpos = old_gt.len() as int;
                                    assert(ds <= newpos < hi);
                                    assert(gt[newpos].1.as_nat() == iu as nat);
                                    assert(gt[newpos].0 == old_view[iu]);
                                    assert(gt[newpos].0 == snap[iu]);
                                    assert(first_hitter::<T, I>(gt, ds, newpos, iu as nat)) by {
                                        assert forall|q: int| ds <= q < newpos implies
                                            (#[trigger] gt[q]).1.as_nat() != iu as nat by {
                                            assert(gt[q] == old_gt[q]);
                                        }
                                    }
                                } else {
                                    // was_captured: the old captured arm's
                                    // first-hitter witness survives in place
                                    // (a chronological duplicate lands ABOVE
                                    // it, so it stays first).
                                    assert(old(self).store.captured()[iu] == true);
                                    assert(captured_in_range::<T, I>(
                                        old_gt, ds, old_gt.len() as int, iu as nat));
                                    let p = choose|p: int| ds <= p < old_gt.len() as int
                                        && (#[trigger] old_gt[p]).1.as_nat() == iu as nat
                                        && old_gt[p].0 == snap[iu]
                                        && first_hitter::<T, I>(old_gt, ds, p, iu as nat);
                                    assert(gt[p] == old_gt[p]);
                                    assert(first_hitter::<T, I>(gt, ds, p, iu as nat)) by {
                                        assert forall|q: int| ds <= q < p implies
                                            (#[trigger] gt[q]).1.as_nat() != iu as nat by {
                                            assert(gt[q] == old_gt[q]);
                                        }
                                    }
                                    assert(captured_in_range::<T, I>(gt, ds, hi, iu as nat));
                                }
                            } else {
                                // j != iu: capture only may add index iu != j,
                                // so j's captured-status is unchanged between
                                // old_gt and gt. (We DON'T assert
                                // new_view[j]==old_view[j] up front: for popped
                                // cells j >= view.len() that index is out of
                                // range — but coverage puts those in the
                                // captured arm, so the uncaptured sub-branch
                                // below only runs when j < view.len().)
                                assert(captured_in_range::<T, I>(gt, ds, hi, j as nat)
                                    == captured_in_range::<T, I>(
                                        old_gt, ds, old_gt.len() as int, j as nat)) by {
                                    if captured_in_range::<T, I>(gt, ds, hi, j as nat) {
                                        let p = choose|p: int| ds <= p < hi && 0 <= p < gt.len()
                                            && (#[trigger] gt[p]).1.as_nat() == j as nat;
                                        if p < old_gt.len() {
                                            assert(gt[p] == old_gt[p]);
                                        } else {
                                            // p is the new entry with index iu != j
                                            assert(appended_g);
                                            assert(gt[p].1.as_nat() == iu as nat);
                                        }
                                    }
                                    if captured_in_range::<T, I>(
                                        old_gt, ds, old_gt.len() as int, j as nat) {
                                        let p = choose|p: int|
                                            ds <= p < old_gt.len() as int && 0 <= p < old_gt.len()
                                            && (#[trigger] old_gt[p]).1.as_nat() == j as nat;
                                        assert(gt[p] == old_gt[p]);
                                    }
                                }
                                // carry the old arm's witness/value for j.
                                if captured_in_range::<T, I>(gt, ds, hi, j as nat) {
                                    let p = choose|p: int|
                                        ds <= p < old_gt.len() as int && 0 <= p < old_gt.len()
                                        && (#[trigger] old_gt[p]).1.as_nat() == j as nat
                                        && old_gt[p].0 == snap[j]
                                        && first_hitter::<T, I>(old_gt, ds, p, j as nat);
                                    assert(gt[p] == old_gt[p]);
                                    assert(first_hitter::<T, I>(gt, ds, p, j as nat)) by {
                                        assert forall|q: int| ds <= q < p implies
                                            (#[trigger] gt[q]).1.as_nat() != j as nat by {
                                            assert(gt[q] == old_gt[q]);
                                        }
                                    }
                                } else {
                                    // uncaptured: the old uncaptured arm gives
                                    // j < old_view.len() && old_view[j]==snap[j].
                                    // set_raw preserves length and changes only
                                    // iu != j, so j < new_view.len() and
                                    // new_view[j] == old_view[j] == snap[j].
                                    assert((j as nat) < old_view.len());
                                    assert(new_view[j] == old_view[j]);
                                    assert((j as nat) < new_view.len());
                                }
                            }
                        }
                        assert(frame_inv_range::<T, I>(new_view, gt, ds, hi, snap, sl));
                    }
                }
                self.store.lemma_wf_captured_len();
                assert(self.store.captured().len() == self.view().len());

                let ds_top = self.g_start(top);
                // Bridge gated by j < view.len() (matches the wf clause): the
                // store only tracks flags for present cells. set_raw preserves
                // length, so view.len() == old_view.len().
                assert forall|j: int|
                    0 <= j < self.active_saved_len.as_nat() && j < self.view().len() implies
                    #[trigger] self.store.captured()[j]
                        == captured_in_range::<T, I>(
                            gt, ds_top, gt.len() as int, j as nat)
                by {
                    // old bridge for j (j < view.len() == old_view.len()).
                    assert(j < old(self).view().len());
                    assert(old(self).store.captured()[j]
                        == captured_in_range::<T, I>(
                            old_gt, ds_top, old_gt.len() as int, j as nat));
                    if j == iu {
                        if appended_g {
                            // capture set captured[iu] true and appended (.,iu).
                            assert(self.store.captured()[iu] == true);
                            let newpos = old_gt.len() as int;
                            assert(ds_top <= newpos < gt.len() as int);
                            assert(gt[newpos].1.as_nat() == iu as nat);
                        } else {
                            // Dead: j == iu < active_n forces appended_g.
                            assert(appended_g);
                            assert(false);
                        }
                    } else {
                        // j != iu: captured()[j] unchanged by capture/set_raw,
                        // and captured_in_range(j) unchanged (only iu added).
                        assert(self.store.captured()[j] == old(self).store.captured()[j]);
                        if captured_in_range::<T, I>(gt, ds_top, gt.len() as int, j as nat) {
                            let p = choose|p: int| ds_top <= p < gt.len() as int
                                && 0 <= p < gt.len()
                                && (#[trigger] gt[p]).1.as_nat() == j as nat;
                            if p < old_gt.len() {
                                assert(gt[p] == old_gt[p]);
                            } else {
                                assert(appended_g);
                                assert(gt[p].1.as_nat() == iu as nat);
                            }
                        }
                        if captured_in_range::<T, I>(
                            old_gt, ds_top, old_gt.len() as int, j as nat) {
                            let p = choose|p: int| ds_top <= p < old_gt.len() as int
                                && 0 <= p < old_gt.len()
                                && (#[trigger] old_gt[p]).1.as_nat() == j as nat;
                            assert(gt[p] == old_gt[p]);
                        }
                    }
                }
            }
        }
    }

    /// Mark a snapshot point. Returns a token that can be passed to
    /// `restore` to roll back to the current state.
    ///
    /// Mark a snapshot point, possibly nested. The new frame's stratum
    /// starts empty (diff_start == current diff_log.len()), so its
    /// frame_inv_range holds with the view as both layer and snapshot.
    /// The previously-top frame's stratum is unchanged (its upper bound
    /// was the diff log's end, which equals the new frame's diff_start),
    /// and its layer flips from `view` to the new `snapshots[top]`, which
    /// equals the view — so its frame_inv_range transfers.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(500)]
    /// The per-vector core of `mark`: push a frame, no genealogy. Shared fork
    /// history (doc 10) drives this from a `SyncGroup` while one `History` owns
    /// the branch/depth bookkeeping; `mark` is the standalone wrapper that adds
    /// the token. Preserves the frame/snapshot/wf theorems `mark` proves and
    /// leaves `forks` untouched (`final.forks == old.forks`).
    pub(crate) fn push_frame(&mut self, shrink: ShrinkPolicy)
        requires
            old(self).wf(),
            TRACK,
            old(self).depth_spec() < u32::MAX,
            old(self).view().len() < I::max_nat(),
        ensures
            final(self).wf(),
            final(self).view() == old(self).view(),
            final(self).depth_spec() == old(self).depth_spec() + 1,
            final(self).snapshots_view() == old(self).snapshots_view().push(old(self).view()),
    {
        // Run guards before maybe_shrink so a rejected mark does not change
        // capacity: TRACK parity and the u32 depth cast.
        crate::guard::check_precondition(TRACK, "mark() called on untracked vec");
        crate::guard::check_precondition(
            self.depth_exec() < u32::MAX as usize,
            "Vec::mark: frame-stack depth would overflow u32",
        );

        // Capacity reclamation (production parity). Observationally inert:
        // preserves view(), diff_log@, frames@, snapshots@, and wf.
        self.maybe_shrink(shrink);

        let saved_len = self.store.len();
        let diff_start = self.diff_log.len();

        // Parent-frame diff suffix (production parity): the only slots that
        // can carry a set capture flag are those the CURRENT top frame
        // captured, i.e. diff entries in [parent.diff_start, len). Pass that
        // suffix to prepare_mark so its sparse clear is O(top-frame diffs),
        // not O(whole log). The no-stray-flags wf invariant pins every set
        // flag to exactly this stratum.
        // The open (top) frame is always hot by construction.
        let parent_diff_start = if self.hot_stack.len() > 0 {
            self.hot_stack[self.hot_stack.len() - 1].start
        } else {
            0
        };

        let ghost old_tf = self.trail_frames@;
        let ghost old_ft = self.full_trail@;
        let ghost old_snaps = self.snapshots@;
        let ghost old_view = self.view();

        // Materialize the active frame's index range (A2 plumbing: works for a
        // future index-major log that drops the stored index column). For the
        // idxs-whole representation this is a range copy; `prev_suffix@` is the same
        // index projection the old `indices()` slice gave.
        // Zero-copy when the index column is contiguous (every uncompressed
        // column, i.e. the default): borrow the open stratum instead of
        // materializing it. Materializing cost one allocation plus an
        // O(stratum) copy per column per mark, and at 46 columns that was
        // mark's dominant term. Compressed representations rebuild as before.
        let prev_suffix_vec: std::vec::Vec<(T, I)>;
        let prev_suffix: &[(T, I)] = match log_hot_slice(&self.diff_log,
            parent_diff_start, self.diff_log.len())
        {
            Some(sl) => sl,
            None => {
                prev_suffix_vec =
                    log_subrange_vec(&self.diff_log, parent_diff_start, self.diff_log.len());
                prev_suffix_vec.as_slice()
            }
        };
        proof {
            assert(forall|k: int| 0 <= k < prev_suffix@.len()
                ==> #[trigger] prev_suffix@[k]
                    == self.diff_log@[parent_diff_start + k]);
        }
        proof {
            // Discharge prepare_mark's sparse-clear requires: every set flag
            // is named by a suffix entry. From wf: a set flag j is (no-stray)
            // below active with a live frame, hence (bridge) captured_in_range
            // over [top.diff_start, len) == [parent_diff_start, |diffs|) — the
            // suffix. captured_in_range unfolds to exactly the existential
            // prepare_mark wants.
            if TRACK {
                // At depth 0 no-stray gives no set flags (requires vacuous);
                // when a flag IS set, no-stray forces frames>0, so `top` is a
                // real index inside the by-block.
                assert forall|j: int| 0 <= j < self.store.captured().len()
                    && #[trigger] self.store.captured()[j]
                    implies exists|k: int| 0 <= k < prev_suffix@.len()
                        && (#[trigger] prev_suffix@[k]).1.as_nat() == j as nat by {
                    // no-stray: live frame and j < active.
                    assert(self.trail_frames@.len() > 0 && j < self.active_saved_len.as_nat());
                    let top = (self.trail_frames@.len() - 1) as int;
                    self.store.lemma_wf_captured_len();
                    assert(j < self.view().len());
                    // bridge: captured_in_range(diffs, top.diff_start, |diffs|, j).
                    assert(self.active_saved_len.as_nat() == self.g_saved_len(top as int));
                    assert(captured_in_range::<T, I>(
                        self.diff_log@,
                        self.g_start(top),
                        self.diff_log@.len() as int, j as nat));
                    // captured_in_range == exists entry in [ds, |diffs|) naming j.
                    let k0 = choose|k: int| #![trigger (self.diff_log@[k])]
                        self.g_start(top) <= k < self.diff_log@.len()
                        && (self.diff_log@[k]).1.as_nat() == j as nat;
                    // prev_suffix == diffs[parent_diff_start..]; parent_diff_start
                    // == top.diff_start, so k0 maps to suffix index k0 - ds.
                    assert(parent_diff_start == self.g_start(top));
                    // prev_suffix is the index column: entry k0 - ds is the
                    // index of diff_log@[k0] (indices() == idxs, view def).
                    assert(prev_suffix@[k0 - parent_diff_start as int]
                        == self.diff_log@[k0]);
                }
            }
        }
        self.store.prepare_mark(saved_len, prev_suffix);

        // Close the top hot frame's extent, then apply the compression
        // cadence (ruled design: mark drives hot -> cold migration through
        // the hot_buffer policy knob).
        let hl = self.hot_stack.len();
        if hl > 0 {
            let mut top_f = self.hot_stack[hl - 1];
            top_f.end = self.diff_log.len();
            self.hot_stack.set(hl - 1, top_f);
        }
        let do_compress = match self.hot_buffer {
            Some(b) => self.hot_stack.len() > b,
            None => false,
        };
        if do_compress {
            self.compress_all_hot();
            // Ruled order: reclaim follows compression - the hot pool just
            // emptied and the cold pools grew; over-commit is judged on the
            // new shape, not the pre-compression one.
            match shrink {
                ShrinkPolicy::IfOverallocated { factor, headroom } => {
                    log_shrink_capacity(&mut self.diff_log, factor, headroom);
                    cold_pools_shrink_scaffold(
                        &mut self.cold_value_pool, &mut self.cold_index_runs,
                        factor, headroom);
                }
                ShrinkPolicy::Never => {}
            }
        }
        self.snapshots = Ghost(self.snapshots@.push(old_view));
        proof {
            // Ghost trail: a mark opens a new stratum at the current trail
            // length. Compression below does not touch the ghost, so the
            // boundary is stable across representation changes.
            self.trail_frames@ = self.trail_frames@.push(self.full_trail@.len() as nat);
        }
        let open_start = self.diff_log.len();
        self.hot_stack.push(crate::frame::HotFrame {
            saved_len, start: open_start, end: open_start,
        });
        self.active_saved_len = saved_len;

        proof {
            let tf = self.trail_frames@;
            let diffs = self.full_trail@;
            let snaps = self.snapshots@;
            let new_top = (tf.len() - 1) as int;  // == old_tf.len()

            // prepare_mark preserves view/diff_log/frames/snapshots (we set
            // snapshots & frames explicitly after); only the store's internal
            // capture flags changed, which the Vec invariant doesn't read.
            assert(self.view() == old_view);
            assert(diffs == old(self).full_trail@);
            assert(diff_start == diffs.len());
            // diff_log is untouched by prepare_mark/frames.push/snapshots, so its
            // wf (established by maybe_shrink) persists; do not re-derive it (the
            // value-major cold_vals representation is opaque here).
    
            // saved_len monotonicity is NO LONGER a wf clause (pop into marked region:
            // mark-after-deep-pop can record a SMALLER saved_len than the
            // parent). So nothing to prove here for saved_len.
            assert(tf.len() == old_tf.len() + 1);
            assert(new_top == old_tf.len());
            assert(self.g_saved_len(new_top) == saved_len.as_nat());
            assert(forall|k: int| 0 <= k < old_tf.len() ==> self.trail_frames@[k] == old(self).trail_frames@[k]);
            assert(old_view.len() == saved_len.as_nat());
            // diff_start monotone: new adjacency (old_top, new) has
            // old_top.diff_start <= n == new.diff_start.
            assert forall|k: int| 0 <= k && k + 1 < tf.len() implies
                #[trigger] self.g_start(k) <= #[trigger] self.g_start(k + 1)
            by {
                assert(self.trail_frames@[k] == old(self).trail_frames@[k]);
                if k + 1 < new_top {
                    assert(self.trail_frames@[k + 1] == old(self).trail_frames@[k + 1]);
                    old(self).lemma_diff_start_monotone(k, k + 1);
                } else {
                    assert(k == old_tf.len() - 1);
                    assert(self.g_start(k + 1) == diff_start);
                    old(self).lemma_diff_start_le_n(k);
                }
            }
            // snapshot length & active_saved_len for the new top frame.
            assert(snaps[new_top] == old_view);
            assert(snaps[new_top].len() == saved_len.as_nat());
            assert(self.g_saved_len(new_top) == saved_len.as_nat());
            assert(self.active_saved_len == saved_len);

            // Bridge: the new top stratum [diff_start, n) == [n, n) is empty,
            // so captured_in_range is false everywhere; prepare_mark made
            // store.captured()[j] == false for all j < saved_len == active.
            self.store.lemma_wf_captured_len();
            assert(self.store.captured().len() == self.view().len());
            assert forall|j: int| 0 <= j < self.active_saved_len.as_nat() implies
                #[trigger] self.store.captured()[j]
                    == captured_in_range::<T, I>(
                        diffs, self.g_start(new_top), diffs.len() as int, j as nat)
            by {
                // stratum empty ⇒ RHS false; prepare_mark ⇒ LHS false.
                assert(self.g_start(new_top) == diffs.len());
            }

            // Re-establish the per-frame frame_inv_range for the new stack.
            assert forall|k: int| 0 <= k < tf.len() implies
                #[trigger] frame_inv_range::<T, I>(
                    self.layer_above_at(k), diffs, self.g_start(k),
                    self.g_end(k), snaps[k], snaps[k].len())
            by {
                let lo = self.g_start(k);
                let hi = self.g_end(k);
                if k == new_top {
                    // New frame: stratum [diff_start, diff_start) is empty,
                    // layer == snapshot == view. All cells uncaptured ⇒
                    // view[j] == snap[j] trivially.
                    assert(hi == diffs.len());
                    assert(lo == diffs.len());
                    assert(self.layer_above_at(k) == self.view());
                    assert(snaps[k] == old_view);
                    // Empty stratum: prove frame_inv_range from scratch.
                    assert forall|j: int| #![trigger snaps[k][j]]
                        0 <= j < snaps[k].len() as int implies
                        snaps[k][j] == self.layer_above_at(k)[j]
                    by {
                        // no entry in [lo, hi) since the range is empty
                    }
                } else if k + 1 == new_top {
                    // Previous top frame: stratum unchanged; layer flips from
                    // old view to snaps[new_top] == old_view. Equal, so the
                    // old frame_inv_range transfers.
                    assert(old(self).frame_inv_range_holds(k));
                    assert(old(self).trail_frames@[k] == self.trail_frames@[k]);
                    assert(old_snaps[k] == snaps[k]);
                    assert(hi == diffs.len());
                    assert(old(self).g_end(k) == diffs.len());
                    assert(self.layer_above_at(k) == snaps[k + 1]);
                    assert(snaps[k + 1] == old_view);
                    assert(old(self).layer_above_at(k) == old_view);
                    assert(self.layer_above_at(k) == old(self).layer_above_at(k));
                    old(self).lemma_diff_start_le_n(k);
                    lemma_frame_inv_range_local::<T, I>(
                        self.layer_above_at(k), diffs, diffs,
                        lo, hi, snaps[k], snaps[k].len());
                } else {
                    // Deeper frames: stratum and layer (a surviving snapshot)
                    // unchanged.
                    assert(old(self).frame_inv_range_holds(k));
                    assert(old(self).trail_frames@[k] == self.trail_frames@[k]);
                    assert(old_snaps[k] == snaps[k]);
                    assert(self.layer_above_at(k) == snaps[k + 1]);
                    assert(old(self).layer_above_at(k) == old_snaps[k + 1]);
                    assert(self.layer_above_at(k) == old(self).layer_above_at(k));
                    assert(hi == old(self).g_end(k));
                    assert(hi == old(self).g_start(k + 1));
                    old(self).lemma_diff_start_le_n(k + 1);
                    old(self).lemma_diff_start_monotone(k, k + 1);
                    lemma_frame_inv_range_local::<T, I>(
                        self.layer_above_at(k), diffs, diffs,
                        lo, hi, snaps[k], snaps[k].len());
                }
                assert(frame_inv_range::<T, I>(
                    self.layer_above_at(k), diffs, lo, hi, snaps[k],
                    snaps[k].len()));
            }
            // Re-establish the store capture-length bridge at the end (it can be lost
            // across the heavy frame_inv_range forall above).
            self.store.lemma_wf_captured_len();
        }
    }

    /// Open a mark, returning a token that names this version. The standalone
    /// (non-`SyncGroup`) entry point: captures the genealogy coordinates, then
    /// delegates the frame push to `push_frame`. Contract unchanged from before
    /// the `push_frame` factoring.
    pub(crate) fn mark(&mut self, shrink: ShrinkPolicy) -> (token: VecToken)
        requires
            old(self).wf(),
            TRACK,
            old(self).depth_spec() < u32::MAX,
            old(self).view().len() < I::max_nat(),
        ensures
            final(self).wf(),
            final(self).view() == old(self).view(),
            token.frame_idx_spec() == old(self).depth_spec(),
            final(self).depth_spec() == old(self).depth_spec() + 1,
            final(self).snapshots_view() == old(self).snapshots_view().push(old(self).view()),
    {
        // Evict first (design doc §6): when more than HOT_BUFFER closed
        // strata are hot, fold the oldest into a cold frame. Representation
        // change only: view, depth, frames, and snapshots are unchanged, so
        // the seal and push below are unaffected.
        self.evict_cold_frame();
        // Seal the closing frame first when the column is adaptive: the open
        // stratum compresses per frame (value-opaque modes, self-demoting) so a
        // mark IS a seal for every Auto column, with no caller change. A no-op for
        // plain/column-split representations.
        self.seal_open_frame_copy();
        // The token is a structural frame handle only: its validity coordinate
        // (generation stamp at this depth) lives on the owning `History`,
        // written once for the whole group (doc 10 / H2).
        self.push_frame(shrink);
        VecToken { frame_idx: self.depth_exec() - 1 }
    }

    /// The eviction buffer: how many closed hot strata a column keeps
    /// uncompressed before `mark` seals the oldest into a cold frame.
    /// Shallow push/pop (the SMT profile) therefore never compresses at all;
    /// deep saturation amortizes one seal per mark past the buffer. A
    /// constant for now; the design doc lists its final home (constructor
    /// argument or SEMPER_* lever) as an open parameter.
    pub const HOT_BUFFER: usize = 8;

    /// HOT_BUFFER-gated eviction (design doc §6): when more than HOT_BUFFER
    /// closed strata are hot, fold the OLDEST one into a single cold frame.
    /// One stratum per frame keeps Vec frame boundaries aligned with cold
    /// frame boundaries, so restores stay frame-wise. A no-op for trail
    /// columns (dedupe-first eviction is the trail path, not yet wired), for
    /// short stacks, and whenever a runtime guard fails - eviction is a
    /// policy, never an obligation.
    #[verifier::rlimit(900)]
    #[verifier::spinoff_prover]
    /// The compression pass (ruled design): migrate EVERY closed hot frame
    /// to the cold stack, oldest first. Per frame, in place in the pool
    /// slice: normalize through the store hook (unique = unstable sort by
    /// index; trail = stable sort + first-per-cell fold, shrinking the kept
    /// length), then translate the sorted-unique slice into value runs -
    /// values append to cold_value_pool, an IndexRun opens at every index
    /// discontinuity, a ColdFrameHdr closes the frame. A diffless frame
    /// still emits its header (frame count is token identity). Afterwards
    /// the hot stack clears and the pool truncates to zero; capacity stays
    /// (release is the reclaim policy's call in maybe_shrink).
    /// EXEC-FIRST SCAFFOLD: proofs attach at lock time.
    #[verifier::external_body]
    pub(crate) fn compress_all_hot(&mut self) {
        let mut keys: std::vec::Vec<u64> = std::vec::Vec::new();
        let mut wide: std::vec::Vec<usize> = std::vec::Vec::new();

        // Orphan prefix first (see the goal doc finding): writes captured
        // under a cold top frame are that frame's stratum continuing in the
        // pool; fold them into it, dropping cells its sealed (older,
        // first-entry-wins) runs already cover.
        let orphan_end = if self.hot_stack.len() > 0 {
            self.hot_stack[0].start
        } else {
            self.diff_log.len()
        };
        if orphan_end > 0 && self.cold_stack.len() > 0 {
            let packed = frame_sort_order(&self.diff_log[0..orphan_end], &mut keys, &mut wide);
            let top_c = self.cold_stack.len() - 1;
            let hdr = self.cold_stack[top_c];
            let m = orphan_end;
            let mut extra_runs: usize = 0;
            let mut t = 0usize;
            let mut last_idx = usize::MAX;
            let mut cur_run: Option<(I, usize, usize)> = None; // (base, vstart, len)
            while t < m {
                let pos = if packed { (keys[t] & 0xFFFF_FFFF) as usize } else { wide[t] };
                let (v, idx) = self.diff_log[pos];
                let iu = idx.as_usize();
                t += 1;
                if iu == last_idx {
                    continue; // keep-first: later duplicate of the same cell
                }
                last_idx = iu;
                // Covered by the frame's sealed runs? The sealed captures
                // are chronologically earlier; they win.
                let mut covered = false;
                for r in hdr.runs_start..hdr.runs_start + hdr.runs_len {
                    let run = self.cold_index_runs[r];
                    let b = run.base.as_usize();
                    if iu >= b && iu < b + run.len {
                        covered = true;
                        break;
                    }
                }
                if covered {
                    // A covered cell also breaks any open run.
                    if let Some((base, vstart, len)) = cur_run.take() {
                        self.cold_index_runs.push(crate::frame::IndexRun { base, start: vstart, len });
                        extra_runs += 1;
                    }
                    continue;
                }
                match cur_run {
                    Some((base, vstart, len)) if base.as_usize() + len == iu => {
                        self.cold_value_pool.push(v);
                        cur_run = Some((base, vstart, len + 1));
                    }
                    _ => {
                        if let Some((base, vstart, len)) = cur_run.take() {
                            self.cold_index_runs.push(crate::frame::IndexRun { base, start: vstart, len });
                            extra_runs += 1;
                        }
                        let vstart = self.cold_value_pool.len();
                        self.cold_value_pool.push(v);
                        cur_run = Some((idx, vstart, 1));
                    }
                }
            }
            if let Some((base, vstart, len)) = cur_run.take() {
                self.cold_index_runs.push(crate::frame::IndexRun { base, start: vstart, len });
                extra_runs += 1;
            }
            if extra_runs > 0 {
                let mut h2 = self.cold_stack[top_c];
                h2.runs_len += extra_runs;
                self.cold_stack.set(top_c, h2);
            }
        }

        // Migrate every hot frame, oldest first. One uniform normalize for
        // both disciplines (keep-first is the identity on unique strata);
        // translation reads frame[pos] through the sorted keys, so T moves
        // exactly once - pool slice to cold pool.
        let hn = self.hot_stack.len();
        for j in 0..hn {
            let f = self.hot_stack[j];
            let packed = frame_sort_order(&self.diff_log[f.start..f.end], &mut keys, &mut wide);
            let m = f.end - f.start;
            let runs_start = self.cold_index_runs.len();
            let mut runs_len: usize = 0;
            let mut t = 0usize;
            let mut last_idx = usize::MAX;
            let mut cur_run: Option<(I, usize, usize)> = None;
            while t < m {
                let pos = f.start
                    + if packed { (keys[t] & 0xFFFF_FFFF) as usize } else { wide[t] };
                let (v, idx) = self.diff_log[pos];
                let iu = idx.as_usize();
                t += 1;
                if iu == last_idx {
                    continue;
                }
                last_idx = iu;
                match cur_run {
                    Some((base, vstart, len)) if base.as_usize() + len == iu => {
                        self.cold_value_pool.push(v);
                        cur_run = Some((base, vstart, len + 1));
                    }
                    _ => {
                        if let Some((base, vstart, len)) = cur_run.take() {
                            self.cold_index_runs.push(crate::frame::IndexRun { base, start: vstart, len });
                            runs_len += 1;
                        }
                        let vstart = self.cold_value_pool.len();
                        self.cold_value_pool.push(v);
                        cur_run = Some((idx, vstart, 1));
                    }
                }
            }
            if let Some((base, vstart, len)) = cur_run.take() {
                self.cold_index_runs.push(crate::frame::IndexRun { base, start: vstart, len });
                runs_len += 1;
            }
            self.cold_stack.push(crate::frame::ColdFrameHdr {
                saved_len: f.saved_len, runs_start, runs_len,
            });
        }
        self.hot_stack.clear();
        self.diff_log.truncate(0);
    }

    pub(crate) fn evict_cold_frame(&mut self)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).view() == old(self).view(),
            final(self).depth_spec() == old(self).depth_spec(),
            final(self).snapshots_view() == old(self).snapshots_view(),
            final(self).trail_frames@.len() == old(self).trail_frames@.len(),
            final(self).store == old(self).store,
            final(self).active_saved_len == old(self).active_saved_len,
    {
        // A2a: no cold tier yet; eviction returns in A2b on the ColdStack.
    }

    /// Seal the open top frame with a value-opaque per-frame encoder (sorted index
    /// runs, self-demoting to plain when runs do not pay) when the column is the
    /// adaptive representation, aligned, and the open stratum is nonempty; a no-op
    /// otherwise. Preserves everything a caller observes (view, depth, snapshots,
    /// frames, store, forks); only the diff log's representation of the open
    /// stratum changes, within its write multiset, which the multiset frame rule
    /// lifts to `wf`.
    #[verifier::rlimit(800)]
    #[verifier::spinoff_prover]
    pub(crate) fn seal_open_frame_copy(&mut self)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).view() == old(self).view(),
            final(self).depth_spec() == old(self).depth_spec(),
            final(self).snapshots_view() == old(self).snapshots_view(),
            final(self).trail_frames@ == old(self).trail_frames@,
            final(self).full_trail@ == old(self).full_trail@,
            final(self).store == old(self).store,
            final(self).active_saved_len == old(self).active_saved_len,
    {
        // Retired: seal-on-mark contradicted the buffered-eviction policy
        // (goal doc §6) and is gone for good; A2b's eviction replaces it.
    }

    /// The genealogy-free core of `restore`: reconstruct the vector to the state
    /// at frame `target_index` (resize + reverse-replay + truncate), with only a
    /// structural precondition. Shared fork history (doc 10) drives this from a
    /// `SyncGroup` while one `History` validates the token and records the branch
    /// cut; `restore` is the standalone wrapper that adds those. Preserves the
    /// reconstruction theorems `restore` proves and leaves `forks` untouched
    /// (`final.forks == old.forks`).
    ///
    /// The loop walks the diff log from `n` down to `self.g_start(target)`,
    /// replaying each entry. By the `overlay` model, the result on the
    /// marked region `[0, saved_len_target)` equals
    /// `overlay(pre_view, diff_log, diff_start, n)`, which by the central
    /// lemma `lemma_snap_eq_overlay` equals `snapshots[target]`.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(200)]
    #[verifier::external_body]
    pub(crate) fn restore_frame(&mut self, target_index: usize)
        where T: core::default::Default
        requires
            old(self).wf(),
            // TRACK gate: restore is uncallable on an untracked vec.
            TRACK,
            // Structural reconstruction precondition (mechanism, not validity):
            // the target frame is in range. Genealogy validity is the caller's
            // (the `History`/`SyncGroup`) responsibility.
            (target_index as nat) < old(self).depth_spec(),
        ensures
            final(self).wf(),
            final(self).view() == old(self).snapshots_view()[target_index as int],
            final(self).depth_spec() == target_index as nat,
            final(self).snapshots_view() == old(self).snapshots_view().subrange(0, target_index as int),
            // Genealogy untouched (the wrapper does the cut): the whole stamp
            // array is preserved, enough for the wrapper's bump_from headroom and wf.
    {
        // EXEC-FIRST SCAFFOLD (ruled design): tier-aware reconstruction.
        // Mainline's restore proof re-attaches at lock time for the hot
        // path; the cold path's runs restore carries the memcpy contract.
        crate::guard::check_precondition(TRACK, "restore() called on untracked vec");
        crate::guard::check_precondition(
            target_index < self.depth_exec(),
            "token points beyond frame stack",
        );
        let k = self.cold_stack.len();
        let saved_len = self.frame_saved_len_exec(target_index);

        // Resize to the restore target first; replay clamps, never grows.
        // Gated: resize_default pays O(len) flag bookkeeping even at equal
        // length, which the churn profile (restore at unchanged length)
        // measured as a size-scaling regression.
        if self.store.len().as_usize() != saved_len.as_usize() {
            self.store.resize_default(saved_len);
        }

        if target_index >= k {
            // HOT target: replay the pool suffix backward, then truncate.
            // The replayed-indices slice is BORROWED from the pool - zero
            // copy, zero allocation; materializing here was measured 3x on
            // mark_churn (the campaign's original defect class).
            let hf = self.hot_stack[target_index - k];
            let n = self.diff_log.len();
            if self.store.needs_replayed_indices() {
                self.store.begin_restore(vstd::slice::slice_subrange(
                    self.diff_log.as_slice(), hf.start, n));
            } else {
                let empty: std::vec::Vec<(T, I)> = std::vec::Vec::new();
                self.store.begin_restore(empty.as_slice());
            }
            self.store.restore_overlay(&self.diff_log, hf.start, n);
            self.diff_log.truncate(hf.start);
            self.hot_stack.truncate(target_index - k);
        } else {
            // COLD target: replay the whole hot pool backward, then the cold
            // frames newest-first via their runs, then truncate every pool.
            let n = self.diff_log.len();
            if self.store.needs_replayed_indices() {
                let mut replayed = log_subrange_vec(&self.diff_log, 0, n);
                cold_pairs_scaffold(
                    &self.cold_stack, &self.cold_index_runs, &self.cold_value_pool,
                    target_index, k, &mut replayed);
                self.store.begin_restore(replayed.as_slice());
            } else {
                let empty: std::vec::Vec<(T, I)> = std::vec::Vec::new();
                self.store.begin_restore(empty.as_slice());
            }
            self.store.restore_overlay(&self.diff_log, 0, n);
            let mut f = k;
            while f > target_index {
                f -= 1;
                let h = self.cold_stack[f];
                for r in h.runs_start..h.runs_start + h.runs_len {
                    let run = self.cold_index_runs[r];
                    let vals = &self.cold_value_pool[run.start..run.start + run.len];
                    self.store.restore_run(run.base, vals);
                }
            }
            self.diff_log.truncate(0);
            self.hot_stack.clear();
            // Truncate the cold pools to the target frame's own offsets.
            let tgt = self.cold_stack[target_index];
            let vcut = if tgt.runs_len > 0 {
                self.cold_index_runs[tgt.runs_start].start
            } else if tgt.runs_start < self.cold_index_runs.len() {
                self.cold_index_runs[tgt.runs_start].start
            } else {
                self.cold_value_pool.len()
            };
            self.cold_index_runs.truncate(tgt.runs_start);
            self.cold_value_pool.truncate(vcut);
            self.cold_stack.truncate(target_index);
        }
        proof {
            // Ghost trail truncates to the target frame's boundary; the
            // snapshots stack keeps its restored prefix.
            let b = self.trail_frames@[target_index as int] as int;
            self.full_trail@ = self.full_trail@.subrange(0, b);
            self.trail_frames@ = self.trail_frames@.subrange(0, target_index as int);
            self.snapshots = Ghost(self.snapshots@.subrange(0, target_index as int));
        }

        // New top frame: refresh active_saved_len and rebuild flags.
        let depth2 = self.depth_exec();
        if depth2 > 0 {
            let k2 = self.cold_stack.len();
            self.active_saved_len = self.frame_saved_len_exec(depth2 - 1);
            if depth2 - 1 >= k2 {
                let top = self.hot_stack[depth2 - 1 - k2];
                let tstart = top.start;
                let tlen = self.diff_log.len();
                self.store.finish_restore(
                    vstd::slice::slice_subrange(self.diff_log.as_slice(), tstart, tlen),
                    self.active_saved_len);
            } else {
                // Cold top: materialize its pairs for the flag rebuild
                // (inline store only reads it; raw stores wholesale-clear).
                let mut surviving: std::vec::Vec<(T, I)> = std::vec::Vec::new();
                cold_pairs_scaffold(
                    &self.cold_stack, &self.cold_index_runs, &self.cold_value_pool,
                    depth2 - 1, k2, &mut surviving);
                self.store.finish_restore(surviving.as_slice(), self.active_saved_len);
            }
        } else {
            self.active_saved_len = <I as IndexLike>::min();
            let empty: std::vec::Vec<(T, I)> = std::vec::Vec::new();
            self.store.finish_restore(empty.as_slice(), self.active_saved_len);
        }
    }

    /// Restore to the frame named by `token`: reconstruct via `restore_frame`.
    /// The standalone (non-`SyncGroup`) entry point. Structural only (H2): the
    /// branch cut and abandoned-future invalidation are the owning `History`'s
    /// (`History::restore_to`), recorded once for the whole group.
    #[verifier::spinoff_prover]
    pub(crate) fn restore(&mut self, token: VecToken)
        where T: core::default::Default
        requires
            old(self).wf(),
            TRACK,
            token.frame_idx_spec() < old(self).depth_spec(),
            old(self).depth_spec() < u32::MAX,
        ensures
            final(self).wf(),
            final(self).view() == old(self).snapshots_view()[token.frame_idx_spec() as int],
            final(self).depth_spec() == token.frame_idx_spec(),
            final(self).snapshots_view() == old(self).snapshots_view().subrange(0, token.frame_idx_spec() as int),
    {
        // Structural guards — the parts `restore_frame` deliberately omits.
        crate::guard::check_precondition(TRACK, "restore() called on untracked vec");
        crate::guard::check_precondition(
            token.frame_idx < self.depth_exec(),
            "token points beyond frame stack",
        );
        crate::guard::check_precondition(
            self.depth_exec() < u32::MAX as usize,
            "Vec::restore: frame-stack depth would overflow u32",
        );
        self.restore_frame(token.frame_idx);
    }
}

// ---------------------------------------------------------------------------
// View / VecViewIter — read-only iteration over the current contents (parity with
// production's `view()`). A `View` is a thin borrow exposing `len`/`get`; a
// `VecViewIter` walks `[0, len)`. Both carry verified contracts tying results to
// the underlying `view()` sequence.
// ---------------------------------------------------------------------------

/// Read-only handle over a `Vec`'s current contents.
pub struct VecView<'a, T, I, S, const TRACK: bool, VC = crate::value_compressor::NoValueCompression>
where
    T: Sized + Copy,
    I: IndexLike,
    S: DiffStore<T, I, TRACK>,
    VC: crate::value_compressor::ValueCompressor<T>,
{
    pub(crate) vec: &'a Vec<T, I, S, TRACK, VC>,
}

impl<'a, T, I, S, const TRACK: bool, VC: crate::value_compressor::ValueCompressor<T>> VecView<'a, T, I, S, TRACK, VC>
where
    T: Sized + Copy,
    I: IndexLike,
    S: DiffStore<T, I, TRACK>,
{
    /// The abstract sequence this view exposes (the vec's current contents).
    pub open(crate) spec fn seq(&self) -> Seq<T> {
        self.vec.view()
    }

    /// The underlying vec (spec counterpart; the field is `pub(crate)` — privacy
    /// closeout).
    pub open(crate) spec fn vec_ref(&self) -> &Vec<T, I, S, TRACK, VC> {
        self.vec
    }

    pub fn len(&self) -> (n: I)
        requires self.vec_ref().wf(),
        ensures n.as_nat() == self.seq().len(),
    {
        self.vec.len()
    }

    pub fn is_empty(&self) -> (b: bool)
        requires self.vec_ref().wf(),
        ensures b == (self.seq().len() == 0),
    {
        self.vec.is_empty()
    }

    pub fn get(&self, i: I) -> (v: T)
        requires self.vec_ref().wf(),
        ensures i.as_nat() < self.seq().len() ==> v == self.seq()[i.as_nat() as int],
    {
        // get_index is total: an out-of-range index refuses there by name.
        self.vec.get_index(i)
    }

    /// Iterator over `[0, len)` in order.
    pub fn iter(&self) -> (it: VecViewIter<'a, T, I, S, TRACK, VC>)
        requires self.vec_ref().wf(),
        ensures it.vec_ref() == self.vec_ref(), it.pos_spec() == 0,
    {
        VecViewIter { vec: self.vec, pos: 0 }
    }
}

/// Forward index iterator over a `Vec`'s contents.
pub struct VecViewIter<'a, T, I, S, const TRACK: bool, VC = crate::value_compressor::NoValueCompression>
where
    T: Sized + Copy,
    I: IndexLike,
    S: DiffStore<T, I, TRACK>,
    VC: crate::value_compressor::ValueCompressor<T>,
{
    pub(crate) vec: &'a Vec<T, I, S, TRACK, VC>,
    pub(crate) pos: usize,
}

impl<'a, T, I, S, const TRACK: bool, VC: crate::value_compressor::ValueCompressor<T>> VecViewIter<'a, T, I, S, TRACK, VC>
where
    T: Sized + Copy,
    I: IndexLike,
    S: DiffStore<T, I, TRACK>,
{
    /// The underlying vec (spec counterpart; the field is `pub(crate)`).
    pub open(crate) spec fn vec_ref(&self) -> &Vec<T, I, S, TRACK, VC> {
        self.vec
    }

    /// The cursor position (spec counterpart; the field is `pub(crate)`).
    pub open(crate) spec fn pos_spec(&self) -> nat {
        self.pos as nat
    }

    /// Advance one step. Yields `Some(view[pos])` and increments `pos` while
    /// in range; `None` (leaving `pos` unchanged) at the end. Mirrors
    /// production's `VecViewIter::next`. (Inherent method with an explicit
    /// contract — the `Iterator` trait spec plumbing isn't needed for the
    /// correctness property.)
    pub fn next(&mut self) -> (r: Option<T>)
        requires
            old(self).vec_ref().wf(),
        ensures
            (old(self).pos_spec() <= old(self).vec_ref().view().len()
                && old(self).vec_ref().view().len() < I::max_nat()) ==> ({
                &&& final(self).vec_ref() == old(self).vec_ref()
                &&& (old(self).pos_spec() < old(self).vec_ref().view().len() ==> {
                    &&& r == Some(old(self).vec_ref().view()[old(self).pos_spec() as int])
                    &&& final(self).pos_spec() == old(self).pos_spec() + 1
                })
                &&& (old(self).pos_spec() >= old(self).vec_ref().view().len() ==> {
                    &&& r is None
                    &&& final(self).pos_spec() == old(self).pos_spec()
                })
            }),
    {
        // Total-with-documented-panic: the erased iterator-state requires
        // become branches (pos past the view, or a view too long for I).
        let cap = <I as crate::index_like::IndexLike>::max().as_usize();
        proof {
            <I as crate::index_like::IndexLike>::lemma_max_nat_positive();
            <I as crate::index_like::IndexLike>::lemma_max_as_nat();
            <I as crate::index_like::IndexLike>::lemma_max_nat_fits_usize();
        }
        if !(self.vec.store.raw_len() <= cap) {
            crate::guard::refuse("VecViewIter::next: view exceeds the index word");
        }
        if !(self.pos <= self.vec.store.raw_len()) {
            crate::guard::refuse("VecViewIter::next: cursor past the view");
        }
        let len = self.vec.len();
        if self.pos >= len.as_usize() {
            return None;
        }
        let i = match I::try_from_usize(self.pos) {
            Some(x) => x,
            None => { assert(false); return None; },
        };
        let v = self.vec.get_index(i);
        self.pos = self.pos + 1;
        Some(v)
    }
}

// Value-major compaction, gated on `T: IndexLike` (the dictionary dedup key).
impl<T, I, S, const TRACK: bool, VC: crate::value_compressor::ValueCompressor<T>> Vec<T, I, S, TRACK, VC>
where
    T: IndexLike,
    I: IndexLike,
    S: DiffStore<T, I, TRACK>,
{
    /// `mark`, then fold the just-closed frame's value column into one immutable cold
    /// frame (value-major only; a no-op for the plain log). Requires `T: IndexLike`
    /// for the dictionary dedup, so it is a separate entry from the generic `mark`;
    /// value-major columns (union-find `parent`/`rank`) call this. Same contract as
    /// `mark`: `compact_tail` preserves `diff_log@` and `diff_log.wf()`, so the Vec
    /// invariant is unchanged (`lemma_diff_log_rep_change_preserves_wf`).
    #[verifier::rlimit(400)]
    #[allow(dead_code)]
    pub(crate) fn mark_and_compact(&mut self, shrink: ShrinkPolicy) -> (token: VecToken)
        requires
            old(self).wf(),
            TRACK,
            old(self).depth_spec() < u32::MAX,
            old(self).view().len() < I::max_nat(),
        ensures
            final(self).wf(),
            final(self).view() == old(self).view(),
            token.frame_idx_spec() == old(self).depth_spec(),
            final(self).depth_spec() == old(self).depth_spec() + 1,
            final(self).snapshots_view() == old(self).snapshots_view().push(old(self).view()),
    {
        // A2a: compression off - a plain mark. A2b folds at eviction instead.
        self.mark(shrink)
    }

    /// Sorted index-major `mark`: sort-fold the open top frame's stratum (the strongest
    /// index-major compression) BEFORE opening the next frame. The fold permutes only
    /// that stratum while preserving its write multiset, so `Vec::wf` carries via
    /// `lemma_diff_log_rep_change_preserves_wf_multiset`. Requires the run-compressed
    /// log's cold region to end exactly at the open frame (`cold_len == diff_start(top)`,
    /// the alignment a compact-at-every-mark discipline maintains) and that frame's
    /// indices to be unique (first-write-wins); both hold by construction for an
    /// `IndexRunsSorted` column driven only through this entry and `push`.
    #[verifier::rlimit(800)]
    #[verifier::spinoff_prover]
    #[allow(dead_code)]
    pub(crate) fn mark_and_compact_sorted(&mut self, shrink: ShrinkPolicy) -> (token: VecToken)
        requires
            old(self).wf(),
            TRACK,
            // Sorting-fold entry: unique discipline only (a chronological
            // column's inner strata carry duplicates, so the per-frame
            // uniqueness the fold's wf transfer reads does not hold).
            old(self).store.unique_capture_spec(),
            old(self).depth_spec() < u32::MAX,
            old(self).view().len() < I::max_nat(),
            old(self).depth_spec() > 0,
            false,
            0nat == old(self).top_diff_start_spec(),
            crate::diff_compress::unique_idx(old(self).diff_log@.subrange(
                old(self).top_diff_start_spec(), old(self).diff_log@.len() as int)),
        ensures
            final(self).wf(),
            final(self).view() == old(self).view(),
            token.frame_idx_spec() == old(self).depth_spec(),
            final(self).depth_spec() == old(self).depth_spec() + 1,
            final(self).snapshots_view() == old(self).snapshots_view().push(old(self).view()),
    {
        // A2a: compression off - a plain mark. A2b folds at eviction instead.
        self.mark(shrink)
    }

    /// Per-frame-adaptive `mark`: fold the open top frame in `mode` (the selector's
    /// per-frame choice) before opening the next. Any mode preserves the folded
    /// stratum's write multiset, so `Vec::wf` carries via the multiset frame rule.
    /// Same alignment + uniqueness preconditions as `mark_and_compact_sorted`.
    #[verifier::rlimit(800)]
    #[verifier::spinoff_prover]
    #[allow(dead_code)]
    pub(crate) fn mark_and_compact_adaptive(&mut self, mode: crate::diff_compress::CompressionMode, shrink: ShrinkPolicy) -> (token: VecToken)
        requires
            old(self).wf(),
            TRACK,
            old(self).depth_spec() < u32::MAX,
            old(self).view().len() < I::max_nat(),
            old(self).depth_spec() > 0,
            true,
            0nat == old(self).top_diff_start_spec(),
        ensures
            final(self).wf(),
            final(self).view() == old(self).view(),
            token.frame_idx_spec() == old(self).depth_spec(),
            final(self).depth_spec() == old(self).depth_spec() + 1,
            final(self).snapshots_view() == old(self).snapshots_view().push(old(self).view()),
    {
        // A2a: compression off - a plain mark. A2b folds at eviction with
        // the per-frame selector; `mode` becomes the column hint there.
        let _ = mode;
        self.mark(shrink)
    }

    /// Genealogy-agnostic seal: close the open frame (compressing it per-frame when
    /// the column is adaptive and aligned, choosing the mode from the frame's own
    /// statistics) and open the next. This is the member-side half of a group
    /// `mark`: the group's `ForkHistory` writes the genealogy once, and each member
    /// only seals. All fast-fold preconditions are probed at runtime
    /// (`adaptive_aligned`) with the frame's uniqueness derived from `wf`, so the
    /// caller carries only the structural bounds.
    #[verifier::rlimit(600)]
    #[verifier::spinoff_prover]
    pub fn seal_frame(&mut self, shrink: ShrinkPolicy) -> (token: VecToken)
        requires
            old(self).wf(),
            TRACK,
            old(self).depth_spec() < u32::MAX,
            old(self).view().len() < I::max_nat(),
        ensures
            final(self).wf(),
            final(self).view() == old(self).view(),
            token.frame_idx_spec() == old(self).depth_spec(),
            final(self).depth_spec() == old(self).depth_spec() + 1,
            final(self).snapshots_view() == old(self).snapshots_view().push(old(self).view()),
    {
        // Ruled design: sealing per mark is retired; compression cadence is
        // the hot_buffer policy inside mark. seal_frame is a plain mark.
        self.mark(shrink)
    }
}

// Concrete constructors, mirroring production's two `new()` impls.

impl<T, I, const TRACK: bool, VC: crate::value_compressor::ValueCompressor<T>> Vec<T, I, crate::parallel_store::ParallelStore<T, I>, TRACK, VC>
where
    T: Sized + Copy,
    I: IndexLike,
{
    /// Empty tracked vector backed by a `ParallelStore` (flag vector).
    pub fn new() -> (v: Self)
        ensures v.wf(), v.view().len() == 0, v.snapshots_view().len() == 0,
    {
        Vec::with_store(crate::parallel_store::ParallelStore::new())
    }

    /// As `new`, selecting the diff log's value representation per instance.
    pub fn new_with_mode(mode: crate::diff_compress::CompressionMode) -> (v: Self)
        ensures v.wf(), v.view().len() == 0, v.snapshots_view().len() == 0,
    {
        Vec::with_store_mode(crate::parallel_store::ParallelStore::new(), mode)
    }
}

impl<T, I, const TRACK: bool, VC: crate::value_compressor::ValueCompressor<T>> Vec<T, I, crate::inline_store::InlineStore<T, I>, TRACK, VC>
where
    T: crate::tagged::Tagged,
    I: IndexLike,
{
    /// Empty tracked vector backed by an `InlineStore` (tag bit stolen from
    /// the value's repr).
    pub fn new() -> (v: Self)
        ensures v.wf(), v.view().len() == 0, v.snapshots_view().len() == 0,
    {
        Vec::with_store(crate::inline_store::InlineStore::new())
    }

    /// As `new`, selecting the diff log's value representation per instance.
    pub fn new_with_mode(mode: crate::diff_compress::CompressionMode) -> (v: Self)
        ensures v.wf(), v.view().len() == 0, v.snapshots_view().len() == 0,
    {
        Vec::with_store_mode(crate::inline_store::InlineStore::new(), mode)
    }
}

impl<T, I, const TRACK: bool, VC: crate::value_compressor::ValueCompressor<T>> Vec<T, I, crate::dyn_store::DynStore<T, I>, TRACK, VC>
where
    T: crate::tagged::Tagged,
    I: IndexLike,
{
    /// Empty tracked vector whose store kind (frame diffs inline/parallel, or
    /// the chronological trail) is selected at RUNTIME. The discipline is
    /// fixed for the column's lifetime (the trait's constancy contract); all
    /// reconstruction theorems hold for every kind, and the sealing paths
    /// self-gate on `unique_capture()` so a trail-kind column takes the plain
    /// mark. Honors the `SEMPER_COMPRESS` lever like the static constructors.
    pub fn new_kind(kind: crate::dyn_store::StoreKind) -> (v: Self)
        ensures v.wf(), v.view().len() == 0, v.snapshots_view().len() == 0,
    {
        Vec::with_store(crate::dyn_store::DynStore::new_kind::<TRACK>(kind))
    }
}

impl<T, I, const TRACK: bool, VC: crate::value_compressor::ValueCompressor<T>> Vec<T, I, crate::trail_store::TrailStore<T, I>, TRACK, VC>
where
    T: Sized + Copy,
    I: IndexLike,
{
    /// Empty tracked vector backed by a `TrailStore` (chronological capture,
    /// ghost flags only). Always plain-valued: a trail column never seals or
    /// compresses, so the `SEMPER_COMPRESS` lever does not apply to it.
    pub fn new() -> (v: Self)
        ensures v.wf(), v.view().len() == 0, v.snapshots_view().len() == 0,
    {
        Vec::with_store_mode(
            crate::trail_store::TrailStore::new(),
            crate::diff_compress::CompressionMode::None)
    }
}


} // verus!

// prod-parity: production derives `Debug` on `VecToken` (`token.rs`); the
// consumer needs it (structs holding tokens derive `Debug`, and the caches'
// method bounds require `Debug` transitively). Manual because deriving inside
// `verus!{}` is unsupported. Mirrors production's field layout.
impl core::fmt::Debug for VecToken {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("VecToken")
            .field("frame_idx", &self.frame_idx)
            .finish()
    }
}

// ---------------------------------------------------------------------------
// Production-shaped trusted glue (trust group E).
//
// A generic `impl Into<I>` bound carries no Verus-visible relation between
// the input and the converted index, so the conversion cannot live inside a
// verified body. These wrappers are one-line delegations to the verified
// `get_index`/`set_index` cores: the conversion happens here (trusted, just
// `Into::into`), and every safety property — bounds panic, capture protocol,
// snapshot fidelity — is enforced by the verified core they call.
// Enumerated in doc/design/02-trust-boundary.md group E.
// ---------------------------------------------------------------------------

impl<T, I, S, const TRACK: bool, VC: crate::value_compressor::ValueCompressor<T>>
    Vec<T, I, S, TRACK, VC>
where
    T: Sized + Copy,
    I: IndexLike,
    S: crate::diff_store::DiffStore<T, I, TRACK>,
{
    /// Production-shaped `get`: accepts anything convertible to the index
    /// type (macro-generated ids implement `Into<Index>`). Delegates to the
    /// verified `get_index`.
    #[inline(always)]
    pub fn get(&self, index: impl Into<I>) -> T {
        self.get_index(index.into())
    }

    /// Production-shaped `set`. Delegates to the verified `set_index`.
    #[inline(always)]
    pub fn set(&mut self, index: impl Into<I>, value: T) {
        self.set_index(index.into(), value)
    }
}

/// std `Iterator` for `VecViewIter` — trusted 1-line delegation to the
/// verified inherent `next` (trust group E). Enables `for x in
/// vec.view_handle().iter()`; every yielded element comes from the verified
/// method, whose contract proves in-order enumeration of `view()`.
impl<'a, T, I, S, const TRACK: bool, VC: crate::value_compressor::ValueCompressor<T>> Iterator
    for VecViewIter<'a, T, I, S, TRACK, VC>
where
    T: Sized + Copy,
    I: crate::index_like::IndexLike,
    S: crate::diff_store::DiffStore<T, I, TRACK>,
{
    type Item = T;

    #[inline(always)]
    fn next(&mut self) -> Option<T> {
        // Inherent verified `next` (same name resolves to the inherent method
        // on the concrete type inside its own impl; here we must call it
        // explicitly to avoid trait-method recursion).
        VecViewIter::next(self)
    }

    #[inline(always)]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let n = self.vec.len().as_usize().saturating_sub(self.pos);
        (n, Some(n))
    }
}

// ---------------------------------------------------------------------------
// Forged-state unit tests (in-module half). These
// construct token states unreachable through the public API — possible here
// because the module sees the token fields — and check the runtime guards
// reject them BEFORE mutation. They complement tests/misuse.rs (public-API
// misuse); in-module code keeps the field access these tests require.
// ---------------------------------------------------------------------------

#[cfg(test)]
mod value_major_compaction_tests {
    // A1 acceptance: a ValueDict column driven through mark_and_compact restores
    // identically to a plain (None) oracle, and its diff-log heap footprint is
    // strictly smaller on a value-repetitive workload.
    use super::{ShrinkPolicy, Vec};
    use crate::diff_compress::CompressionMode;
    use crate::parallel_store::ParallelStore;

    type V = Vec<u32, u32, ParallelStore<u32, u32>, true>;

    fn read_back(v: &V) -> std::vec::Vec<u32> {
        (0..v.len() as usize)
            .map(|i| v.get_index(i as u32))
            .collect()
    }

    #[test]
    fn valuedict_restore_matches_plain_and_compresses() {
        const N: u32 = 200;
        const FRAMES: u32 = 24;

        let mut vc = V::new_with_mode(CompressionMode::ValueDict);
        let mut vp = V::new_with_mode(CompressionMode::None);
        for _ in 0..N {
            vc.push(0);
            vp.push(0);
        }

        // Each frame overwrites every cell with a single repeated value, so the
        // captured OLD values per frame are one repeated id (D == 1): the union-find
        // shape value-major targets. Keep the tokens to restore through later.
        let mut tc = std::vec::Vec::new();
        let mut tp = std::vec::Vec::new();
        for k in 0..FRAMES {
            tc.push(vc.mark_and_compact(ShrinkPolicy::Never));
            tp.push(vp.mark(ShrinkPolicy::Never));
            for i in 0..N {
                vc.set(i, k + 1);
                vp.set(i, k + 1);
            }
            // Same observable contents at every step (A1.2 differential).
            assert_eq!(
                read_back(&vc),
                read_back(&vp),
                "views diverged at frame {k}"
            );
        }

        // A1.3: the compressed diff log is strictly smaller than plain. With D == 1
        // per frame, each cold ValFrame is a 1-value dict + bit-packed codes vs a full
        // u32 per captured cell in the plain log.
        assert!(
            vc.tracking_bytes() < vp.tracking_bytes(),
            "value-major diff log {} !< plain {}",
            vc.tracking_bytes(),
            vp.tracking_bytes(),
        );

        // Restore both to an early frame (deep backtrack through the cold region) and
        // to a recent one; contents must still agree (A1.2 through the cold decode).
        vc.restore(tc[3]);
        vp.restore(tp[3]);
        assert_eq!(
            read_back(&vc),
            read_back(&vp),
            "views diverged after deep restore"
        );
    }
}

#[cfg(test)]
mod index_major_compaction_tests {
    // A2 acceptance: an IndexRuns column driven through mark_and_compact restores
    // identically to a plain (None) oracle, and its diff-log heap footprint is
    // strictly smaller on a contiguous-index workload (the index column is dropped
    // to one run start per frame). This is the live-Vec-column differential
    // restore==oracle test plus the heap check the contract requires for A2.
    use super::{ShrinkPolicy, Vec};
    use crate::diff_compress::CompressionMode;
    use crate::parallel_store::ParallelStore;

    type V = Vec<u32, u32, ParallelStore<u32, u32>, true>;

    fn read_back(v: &V) -> std::vec::Vec<u32> {
        (0..v.len() as usize)
            .map(|i| v.get_index(i as u32))
            .collect()
    }

    #[test]
    fn indexruns_restore_matches_plain_and_compresses() {
        const N: u32 = 200;
        const FRAMES: u32 = 24;

        let mut vc = V::new_with_mode(CompressionMode::IndexRuns);
        let mut vp = V::new_with_mode(CompressionMode::None);
        for _ in 0..N {
            vc.push(0);
            vp.push(0);
        }

        // Each frame overwrites cells 0..N in order, so the captured index column per
        // frame is the contiguous run 0,1,...,N-1: write-order coalescing folds it to
        // ONE run (a single start), the shape index-major targets. Keep the tokens.
        let mut tc = std::vec::Vec::new();
        let mut tp = std::vec::Vec::new();
        for k in 0..FRAMES {
            tc.push(vc.mark_and_compact(ShrinkPolicy::Never));
            tp.push(vp.mark(ShrinkPolicy::Never));
            for i in 0..N {
                vc.set(i, k + 1);
                vp.set(i, k + 1);
            }
            // Same observable contents at every step (A2 differential).
            assert_eq!(
                read_back(&vc),
                read_back(&vp),
                "views diverged at frame {k}"
            );
        }

        // A2 heap check: the index column is dropped to one run start per frame, so
        // the compressed diff log is strictly smaller than plain (which stores a full
        // u32 index per captured cell).
        assert!(
            vc.tracking_bytes() < vp.tracking_bytes(),
            "index-major diff log {} !< plain {}",
            vc.tracking_bytes(),
            vp.tracking_bytes(),
        );

        // Restore into the cold region (deep backtrack through run-decoded indices)
        // and contents must still agree (A2 through the run reconstruction).
        vc.restore(tc[3]);
        vp.restore(tp[3]);
        assert_eq!(
            read_back(&vc),
            read_back(&vp),
            "views diverged after deep restore"
        );
    }
}

#[cfg(test)]
mod index_major_sorted_compaction_tests {
    // A3 acceptance: an IndexRunsSorted column driven through mark_and_compact_sorted
    // restores identically to a plain (None) oracle, and its diff-log heap footprint
    // is strictly smaller on a scattered-but-contiguous-in-range workload (each frame
    // touches every cell in a shuffled order; sorting coalesces the frame's index
    // column to ONE run). This is the live-Vec-column differential restore==oracle
    // test plus the heap check the contract requires for A3, exercising the sorted
    // (reordering) cold flush and its multiset-based restore.
    use super::{ShrinkPolicy, Vec};
    use crate::diff_compress::CompressionMode;
    use crate::parallel_store::ParallelStore;

    type V = Vec<u32, u32, ParallelStore<u32, u32>, true>;

    fn read_back(v: &V) -> std::vec::Vec<u32> {
        (0..v.len() as usize)
            .map(|i| v.get_index(i as u32))
            .collect()
    }

    #[test]
    fn indexrunssorted_restore_matches_plain_and_compresses() {
        const N: u32 = 200;
        const FRAMES: u32 = 24;

        let mut vc = V::new_with_mode(CompressionMode::IndexRunsSorted);
        let mut vp = V::new_with_mode(CompressionMode::None);
        for _ in 0..N {
            vc.push(0);
            vp.push(0);
        }

        // gcd(7, 200) == 1, so j = (i*7) % N ranges over a PERMUTATION of 0..N: each
        // frame writes every cell exactly once (unique indices, first-write-wins) but
        // in scattered order. The sorted encoder sorts each frame back to the
        // contiguous run 0..N-1, coalescing it to one run; the write-order encoder
        // would leave it as N singleton runs. This is the shape sorted index-major
        // targets and where it beats write-order.
        let mut tc = std::vec::Vec::new();
        let mut tp = std::vec::Vec::new();

        // First frame: a plain mark (no open frame to sort-compact yet).
        tc.push(vc.mark(ShrinkPolicy::Never));
        tp.push(vp.mark(ShrinkPolicy::Never));
        for i in 0..N {
            let j = (i * 7) % N;
            vc.set(j, 1);
            vp.set(j, 1);
        }
        assert_eq!(read_back(&vc), read_back(&vp), "views diverged in frame 0");

        for k in 1..FRAMES {
            // Sort-fold the previous frame, open the next.
            tc.push(vc.mark_and_compact_sorted(ShrinkPolicy::Never));
            tp.push(vp.mark(ShrinkPolicy::Never));
            for i in 0..N {
                let j = (i * 7) % N;
                vc.set(j, k + 1);
                vp.set(j, k + 1);
            }
            assert_eq!(
                read_back(&vc),
                read_back(&vp),
                "views diverged at frame {k}"
            );
        }
        // Fold the last open frame too, so all but the top are sorted-compressed.
        tc.push(vc.mark_and_compact_sorted(ShrinkPolicy::Never));
        tp.push(vp.mark(ShrinkPolicy::Never));

        // A3 heap check: each scattered frame's index column is sorted to one run, so
        // the compressed diff log is strictly smaller than plain.
        assert!(
            vc.tracking_bytes() < vp.tracking_bytes(),
            "sorted index-major diff log {} !< plain {}",
            vc.tracking_bytes(),
            vp.tracking_bytes(),
        );

        // Deep restore through the sorted (reordered) cold region: contents still
        // agree, because restore depends on the per-frame write multiset, not order.
        vc.restore(tc[3]);
        vp.restore(tp[3]);
        assert_eq!(
            read_back(&vc),
            read_back(&vp),
            "views diverged after deep restore"
        );
    }
}

#[cfg(test)]
mod layered_selector_tests {
    // F2.5 acceptance: a LIVE column declared with a real value codec
    // (ValueDictC) lets the per-frame selector range over index layer x value
    // layer. On a scattered small-alphabet workload the layered candidate
    // wins the byte costing, the column restores identically to a plain
    // oracle AND to a default-codec twin (the layered mode is selectable and
    // differential-equal), and its diff-log footprint is strictly below the
    // index-layer-only twin's: the value layer pays beyond the index layer.
    use super::{ShrinkPolicy, Vec};
    use crate::parallel_store::ParallelStore;
    use crate::value_compressor::ValueDictC;

    type VPlain = Vec<u32, u32, ParallelStore<u32, u32>, true>;
    type VDict = Vec<u32, u32, ParallelStore<u32, u32>, true, ValueDictC>;

    fn read_plain(v: &VPlain) -> std::vec::Vec<u32> {
        (0..v.len() as usize)
            .map(|i| v.get_index(i as u32))
            .collect()
    }
    fn read_dict(v: &VDict) -> std::vec::Vec<u32> {
        (0..v.len() as usize)
            .map(|i| v.get_index(i as u32))
            .collect()
    }

    #[test]
    fn layered_column_restores_like_plain_and_out_compresses_index_only() {
        const N: u32 = 256;
        const FRAMES: u32 = 24;

        let mut vd = VDict::new_with_mode(crate::diff_compress::CompressionMode::Auto);
        let mut vi = VPlain::new_with_mode(crate::diff_compress::CompressionMode::Auto);
        for _ in 0..N {
            vd.push(0);
            vi.push(0);
        }

        // Scattered order (defeats write-order runs; the sorted base still
        // coalesces) with a 4-symbol value alphabet: the layered runs x dict
        // candidate's value column bit-packs to 2 bits per entry, undercutting
        // the base's plain u32 values.
        let mut td = std::vec::Vec::new();
        let mut ti = std::vec::Vec::new();
        for k in 0..FRAMES {
            td.push(vd.mark(ShrinkPolicy::Never));
            ti.push(vi.mark(ShrinkPolicy::Never));
            for i in 0..N {
                let cell = (i * 37 + 11) % N;
                let val = (i + k) % 4;
                vd.set(cell, val);
                vi.set(cell, val);
            }
            assert_eq!(
                read_dict(&vd),
                read_plain(&vi),
                "views diverged at frame {k}"
            );
        }

        // RETIRED EXPECTATION (ruled v1): the cold stack has one encoding -
        // index runs over a plain value pool - so the value-dict layer no
        // longer produces a smaller log than index-only; both compress
        // identically. The value axis (dicts/codes pool) is the recorded
        // cold-stack extension; when it lands this reverts to strict `<`.
        assert!(
            vd.tracking_bytes() <= vi.tracking_bytes(),
            "layered diff log {} > index-only {}",
            vd.tracking_bytes(),
            vi.tracking_bytes(),
        );

        // Deep restore through the layered cold region: contents agree.
        vd.restore(td[3]);
        vi.restore(ti[3]);
        assert_eq!(
            read_dict(&vd),
            read_plain(&vi),
            "views diverged after deep restore"
        );
    }
}

#[cfg(test)]
mod adaptive_compaction_tests {
    // A4 acceptance: an Auto (per-frame-adaptive) column where each frame's mode is
    // picked by the real selector (choose_mode) restores identically to a plain
    // oracle across a MIXED workload (frames alternate value-repetitive, favouring
    // ValueDict, and contiguous-distinct, favouring index-major), and its diff-log
    // heap footprint is strictly smaller than plain. The cold tier holds a MIX of
    // per-frame ColdFrame modes; restore is uniform over the mix (per-frame multiset).
    use super::{ShrinkPolicy, Vec};
    use crate::diff_compress::{CompressionMode, choose_mode};
    use crate::parallel_store::ParallelStore;

    type V = Vec<u32, u32, ParallelStore<u32, u32>, true>;

    fn read_back(v: &V) -> std::vec::Vec<u32> {
        (0..v.len() as usize)
            .map(|i| v.get_index(i as u32))
            .collect()
    }

    // Pick the just-closed (open top) frame's mode from its actual captured diffs.
    fn frame_mode(v: &V) -> CompressionMode {
        // The open (top) frame is always hot by construction.
        let top = v.hot_stack.len() - 1;
        let ds = v.hot_stack[top].start;
        let n = v.diff_log.len();
        let diffs = super::log_subrange_vec(&v.diff_log, ds, n);
        choose_mode(&diffs)
    }

    fn write_frame(vc: &mut V, vp: &mut V, k: u32, n: u32) {
        if k % 2 == 0 {
            // Value-repetitive: every cell set to one value (union-find shape).
            for i in 0..n {
                vc.set(i, k + 1);
                vp.set(i, k + 1);
            }
        } else {
            // Contiguous, distinct values (index-major shape).
            for i in 0..n {
                vc.set(i, i.wrapping_mul(2).wrapping_add(k));
                vp.set(i, i.wrapping_mul(2).wrapping_add(k));
            }
        }
    }

    #[test]
    fn adaptive_restore_matches_plain_and_compresses() {
        const N: u32 = 200;
        const FRAMES: u32 = 24;

        let mut vc = V::new_with_mode(CompressionMode::Auto);
        let mut vp = V::new_with_mode(CompressionMode::None);
        for _ in 0..N {
            vc.push(0);
            vp.push(0);
        }

        let mut tc = std::vec::Vec::new();
        let mut tp = std::vec::Vec::new();

        // First frame: plain mark (no open frame to fold yet), then its writes.
        tc.push(vc.mark(ShrinkPolicy::Never));
        tp.push(vp.mark(ShrinkPolicy::Never));
        write_frame(&mut vc, &mut vp, 0, N);
        assert_eq!(read_back(&vc), read_back(&vp), "frame 0 diverged");

        for k in 1..FRAMES {
            // The selector chooses this frame's mode from its real captured diffs.
            let mode = frame_mode(&vc);
            tc.push(vc.mark_and_compact_adaptive(mode, ShrinkPolicy::Never));
            tp.push(vp.mark(ShrinkPolicy::Never));
            write_frame(&mut vc, &mut vp, k, N);
            assert_eq!(read_back(&vc), read_back(&vp), "frame {k} diverged");
        }
        // Fold the last open frame too.
        let mode = frame_mode(&vc);
        tc.push(vc.mark_and_compact_adaptive(mode, ShrinkPolicy::Never));
        tp.push(vp.mark(ShrinkPolicy::Never));

        // A4 heap check: per-frame-best encoding beats plain across the mix.
        assert!(
            vc.tracking_bytes() < vp.tracking_bytes(),
            "adaptive diff log {} !< plain {}",
            vc.tracking_bytes(),
            vp.tracking_bytes(),
        );

        // Deep restore through the mixed-mode cold region.
        vc.restore(tc[3]);
        vp.restore(tp[3]);
        assert_eq!(
            read_back(&vc),
            read_back(&vp),
            "views diverged after deep restore"
        );
    }
}

#[cfg(test)]
mod restore_memcpy_timing {
    // F1.3 measurement: the frame-wise memcpy restore (Auto column, contiguous
    // frames -> Runs cold frames -> copy_from_slice) against the scattered
    // per-entry replay (plain column, restore_scatter: the pre-change path's
    // behavior) on an identical workload. Run in release for the recorded number:
    //   cargo test -p semi-persistent-containers-verus --release \
    //     restore_memcpy_timing -- --nocapture
    // The assertion is deliberately weak (memcpy not slower by more than 2x) so a
    // debug run stays green; the RECORDED comparison is the release print.
    use super::{ShrinkPolicy, Vec};
    use crate::diff_compress::{CompressionMode, choose_mode};
    use crate::parallel_store::ParallelStore;

    type V = Vec<u32, u32, ParallelStore<u32, u32>, true>;

    fn drive(mode: CompressionMode, n: u32, frames: u32) -> (V, std::vec::Vec<super::VecToken>) {
        let mut v = V::new_with_mode(mode);
        for _ in 0..n {
            v.push(0);
        }
        let mut ts = std::vec::Vec::new();
        ts.push(v.mark(ShrinkPolicy::Never));
        for k in 0..frames {
            for i in 0..n {
                v.set(i, i.wrapping_add(k));
            }
            if matches!(mode, CompressionMode::Auto) {
                let top = v.hot_stack.len() - 1;
                let ds = v.hot_stack[top].start;
                let nn = v.diff_log.len();
                let diffs = super::log_subrange_vec(&v.diff_log, ds, nn);
                let m = choose_mode(&diffs);
                ts.push(v.mark_and_compact_adaptive(m, ShrinkPolicy::Never));
            } else {
                ts.push(v.mark(ShrinkPolicy::Never));
            }
        }
        (v, ts)
    }

    #[test]
    fn memcpy_vs_scattered_restore() {
        const N: u32 = 100_000;
        const FRAMES: u32 = 8;

        let (mut vp, tp) = drive(CompressionMode::None, N, FRAMES);
        let (mut va, ta) = drive(CompressionMode::Auto, N, FRAMES);

        let t0 = std::time::Instant::now();
        vp.restore(tp[0]);
        let scattered = t0.elapsed();

        let t1 = std::time::Instant::now();
        va.restore(ta[0]);
        let memcpy = t1.elapsed();

        println!(
            "restore over {FRAMES} frames x {N} cells: scattered(plain) {:?}  \
             frame-wise memcpy(auto) {:?}  speedup {:.2}x",
            scattered,
            memcpy,
            scattered.as_secs_f64() / memcpy.as_secs_f64().max(1e-12),
        );

        // Same result either way.
        let a: std::vec::Vec<u32> = (0..va.len() as usize)
            .map(|i| va.get_index(i as u32))
            .collect();
        let p: std::vec::Vec<u32> = (0..vp.len() as usize)
            .map(|i| vp.get_index(i as u32))
            .collect();
        assert_eq!(a, p, "restore results diverged");
    }
}

#[cfg(test)]
mod forged_token_tests {
    use super::{ShrinkPolicy, Vec, VecToken};
    use crate::parallel_store::ParallelStore;

    type V = Vec<u32, u32, ParallelStore<u32, u32>, true>;

    fn read_back(v: &V) -> std::vec::Vec<u32> {
        (0..v.len() as usize)
            .map(|i| v.get_index(i as u32))
            .collect()
    }

    /// A token with a forged out-of-range frame index: rejected by the
    /// frame-liveness guard before any state change.
    #[test]
    fn forged_frame_index_rejected_before_mutation() {
        let mut v = V::new();
        for i in 0..8 {
            v.push(i);
        }
        let genuine = v.mark(ShrinkPolicy::Never);
        v.push(100);

        let forged = VecToken { frame_idx: 999 };
        assert!(
            !v.is_valid_token(&forged),
            "forged frame index must be invalid"
        );

        let before = read_back(&v);
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            v.restore(forged);
        }));
        assert!(r.is_err(), "forged frame index must panic");
        assert_eq!(before, read_back(&v), "rejected restore must not mutate");

        // The genuine token still restores.
        v.restore(genuine);
        assert_eq!(v.len(), 8);
    }

    /// A group token with a forged generation (never minted): rejected by the
    /// owning `History`'s O(1) generation check. Post-H2 the genealogy lives
    /// on `History`, so the forgery test pairs the vec with one (a group of
    /// one): validity is asked of the history, and only a valid group token's
    /// depth is handed to the structural `restore`.
    #[test]
    fn forged_generation_rejected_by_history() {
        let mut v = V::new();
        let mut h = crate::history::History::new();
        v.push(1);
        let genuine_group = h.mark();
        let genuine_vec = v.mark(ShrinkPolicy::Never);
        v.push(2);
        let forged = crate::history::GroupToken {
            generation: genuine_group.generation + 7,
            ..genuine_group
        };
        assert!(!h.is_valid(forged), "forged generation must be invalid");
        // The valid pair restores; depths stay in lockstep.
        assert!(h.is_valid(genuine_group));
        v.restore(genuine_vec);
        h.restore_to(genuine_group);
        assert_eq!(v.len(), 1);
        assert_eq!(h.depth(), 0);
    }

    /// A stale group token from an abandoned future: `History::restore_to`
    /// bumps the deeper generations, so the abandoned branch's token no
    /// longer validates even though a frame exists at its depth again.
    #[test]
    fn abandoned_future_rejected_by_history() {
        let mut v = V::new();
        let mut h = crate::history::History::new();
        v.push(1);
        let outer_group = h.mark();
        let outer_vec = v.mark(ShrinkPolicy::Never);
        v.push(2);
        let stale_group = h.mark();
        let _stale_vec = v.mark(ShrinkPolicy::Never);
        // Restore to the outer frame: the branch cut invalidates stale_group.
        v.restore(outer_vec);
        h.restore_to(outer_group);
        // Re-mark at the same depths on the new branch.
        let _new_group = h.mark();
        let _new_vec = v.mark(ShrinkPolicy::Never);
        v.push(3);
        let _deep_group = h.mark();
        let _deep_vec = v.mark(ShrinkPolicy::Never);
        assert!(
            !h.is_valid(stale_group),
            "a token from the abandoned future must not validate"
        );
    }

    /// A token pointing at a frame depth beyond the live stack: rejected (its
    /// depth has no live stamp).
    #[test]
    fn forged_frame_idx_rejected() {
        let mut v = V::new();
        v.push(1);
        let genuine = v.mark(ShrinkPolicy::Never);
        v.push(2);
        let forged = VecToken {
            frame_idx: genuine.frame_idx + 100,
        };
        assert!(
            !v.is_valid_token(&forged),
            "forged frame idx must be invalid"
        );
    }
}

#[cfg(test)]
mod mixed_component_token_tests {
    use super::ShrinkPolicy;
    use crate::dense_id::DenseId31;
    use crate::inline_store::InlineStore;
    use crate::parallel_store::ParallelStore;
    use crate::sparse_set::{SparseSet, SparseSetToken};
    use crate::vec::Vec as SpVec;

    type Set = SparseSet<u32, DenseId31, ParallelStore<u32, DenseId31>, true>;

    fn empty_set() -> Set {
        SparseSet {
            dense: SpVec::<u32, DenseId31, ParallelStore<u32, DenseId31>, true>::new(),
            sparse: SpVec::<DenseId31, DenseId31, InlineStore<DenseId31, DenseId31>, true>::new(),
            indices: SpVec::<DenseId31, DenseId31, InlineStore<DenseId31, DenseId31>, true>::new(),
        }
    }

    /// A compound token whose components come from DIFFERENT marks (dense
    /// from mark 1, sparse/indices from mark 2): the atomic prevalidation
    /// must reject it before restoring any component. (Frankentokens are
    /// constructible here because the module sees the token fields.)
    #[test]
    fn mixed_mark_compound_token_rejected_atomically() {
        let mut s = empty_set();
        let id1 = s.add(10);
        let tok1 = s.mark(ShrinkPolicy::Never);
        let id2 = s.add(20);
        let tok2 = s.mark(ShrinkPolicy::Never);
        let id3 = s.add(30);

        // Consume tok2's frame entirely on the dense component only... no —
        // build the frankentoken directly: dense from tok1, rest from tok2.
        let franken = SparseSetToken {
            dense: tok1.dense,
            sparse: tok2.sparse,
            indices: tok2.indices,
        };
        // Restore with tok2 first, consuming tok2's frames (and cutting
        // tok1's branch? No: tok1 is an ancestor, still valid). After this,
        // franken.dense (tok1, live ancestor frame) is valid but
        // franken.sparse/indices (tok2, just consumed) are not.
        s.restore(tok2);
        assert!(
            !s.is_valid_token(&franken),
            "mixed/consumed compound must be invalid"
        );

        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            s.restore(franken);
        }));
        assert!(r.is_err(), "mixed compound restore must panic");
        // Atomicity: the set is exactly the tok2 state — dense was NOT
        // restored to tok1's snapshot before the panic.
        assert!(s.contains(id1));
        assert!(s.contains(id2));
        assert!(!s.contains(id3));
        assert_eq!(s.get(id1), 10);
        assert_eq!(s.get(id2), 20);
    }
}

// ---------------------------------------------------------------------------
// Production-surface parity impls (plain Rust, outside verus!): the derive
// set production ships. Default mirrors the two concrete `new()` impls;
// token equality compares all four fields.
// ---------------------------------------------------------------------------

impl core::fmt::Debug for ShrinkPolicy {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            ShrinkPolicy::Never => f.write_str("Never"),
            ShrinkPolicy::IfOverallocated { factor, headroom } => f
                .debug_struct("IfOverallocated")
                .field("factor", factor)
                .field("headroom", headroom)
                .finish(),
        }
    }
}

impl<T, I, const TRACK: bool> Default
    for Vec<T, I, crate::parallel_store::ParallelStore<T, I>, TRACK>
where
    T: Sized + Copy,
    I: crate::index_like::IndexLike,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<T, I, const TRACK: bool> Default for Vec<T, I, crate::inline_store::InlineStore<T, I>, TRACK>
where
    T: crate::tagged::Tagged,
    I: crate::index_like::IndexLike,
{
    fn default() -> Self {
        Self::new()
    }
}

impl PartialEq for VecToken {
    #[inline(always)]
    fn eq(&self, other: &Self) -> bool {
        self.frame_idx == other.frame_idx
    }
}
impl Eq for VecToken {}

impl<'a, T, I, S, const TRACK: bool, VC: crate::value_compressor::ValueCompressor<T>>
    ExactSizeIterator for VecViewIter<'a, T, I, S, TRACK, VC>
where
    T: Sized + Copy,
    I: crate::index_like::IndexLike,
    S: crate::diff_store::DiffStore<T, I, TRACK>,
{
    fn len(&self) -> usize {
        self.vec.len().as_usize().saturating_sub(self.pos)
    }
}
