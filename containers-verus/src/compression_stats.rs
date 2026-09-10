// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Per-frame statistics and the exact-size scheme decision, plus a calibration
//! accumulator (`doc/design/09-diff-stack-compression.md`).
//!
//! A frame's scheme is decided by exact-size costing from two counts computed in
//! a single O(N) pass — `R`, the number of contiguous index runs (the scatter
//! signal), and `D`, the distinct value count (the value-repetition signal) —
//! without sorting; the sort happens only inside the winning encoder. Accumulated
//! across frames, the same per-scheme byte totals say which scheme wins *on
//! average* for a column, which is what lets a workload calibrate a static default
//! and re-check it periodically instead of paying the adaptive decision every
//! frame.

use vstd::prelude::*;
use crate::index_like::{IndexLike, IndexFromNat};
use crate::diff_compress::CompressionMode;

verus! {

/// One frame's shape: entry count, contiguous-run count, distinct-value count.
#[derive(Clone, Copy)]
pub struct FrameStats {
    pub n: usize,
    pub runs: usize,
    pub distinct: usize,
}

impl FrameStats {
    /// Bytes this frame would occupy under each scheme, given the element widths
    /// (`t`/`i`) and the code width (`c`, `usize` today). Saturating, so a huge
    /// frame never wraps the comparison. `external_body` only because Verus does
    /// not model `saturating_*`; these are size heuristics, not correctness.
    #[verifier::external_body]
    pub fn plain_bytes(self, t: usize, i: usize) -> usize {
        self.n.saturating_mul(t.saturating_add(i))
    }
    /// Index-major (sort-first): run `starts` are `usize`, values are `T`. `runs`
    /// is the sorted run count (contiguous-run starts), which is what
    /// `compress_runs_sorted` achieves — the honest, not optimistic, count.
    #[verifier::external_body]
    pub fn runs_bytes(self, t: usize) -> usize {
        self.runs.saturating_mul(8).saturating_add(self.n.saturating_mul(t))
    }
    /// The code width in BITS the shipped value encoder narrows to
    /// (`Codes::from_usize`): 1/2/4 bit-packed for `D <= 2/4/16`, then byte-granular
    /// 8/16/32 for larger `D`. This is what makes the honest packed cost sub-byte.
    pub fn code_bits(self) -> usize {
        if self.distinct <= 2 { 1 }
        else if self.distinct <= 4 { 2 }
        else if self.distinct <= 16 { 4 }
        else if self.distinct <= 256 { 8 }
        else if self.distinct <= 65536 { 16 }
        else { 32 }
    }
    /// Value-major: dict (`D` values of `T`) + codes (`N` at the narrow bit width,
    /// rounded up to whole bytes) + indices (`N` of `I`, still stored — value-major
    /// does not drop them).
    #[verifier::external_body]
    pub fn dict_bytes(self, t: usize, i: usize) -> usize {
        let code_bytes = self.n.saturating_mul(self.code_bits()).saturating_add(7) / 8;
        self.distinct
            .saturating_mul(t)
            .saturating_add(code_bytes)
            .saturating_add(self.n.saturating_mul(i))
    }

    /// The cheapest scheme for this frame, never worse than plain — costed at the
    /// achievable sizes of the shipped encoders.
    pub fn best_mode(self, t: usize, i: usize) -> CompressionMode {
        let plain = self.plain_bytes(t, i);
        let runs = self.runs_bytes(t);
        let dict = self.dict_bytes(t, i);
        if runs <= dict && runs < plain {
            // `runs_bytes` costs the sorted (index-set) run count, which is what
            // `compress_runs_sorted` achieves — so the honest winner is the sorted
            // encoder, not write-order `IndexRuns` (which fragments into more runs
            // and would exceed this cost). `compress_frame` falls back to
            // write-order if a frame's indices are not unique.
            CompressionMode::IndexRunsSorted
        } else if dict < plain {
            CompressionMode::ValueDict
        } else {
            CompressionMode::None
        }
    }
}

/// Compute a frame's stats in one pass: `R` counts indices whose predecessor is
/// absent (contiguous-run starts), `D` counts distinct values. `external_body`:
/// it uses hash sets (unmodeled) and its output feeds a size heuristic, never
/// correctness. Both counts are exact for the byte formulas above.
#[verifier::external_body]
pub fn frame_stats<T: IndexLike, I: IndexLike>(diffs: &Vec<(T, I)>) -> FrameStats {
    use std::collections::HashSet;
    let n = diffs.len();
    let idx_set: HashSet<usize> = diffs.iter().map(|d| d.1.as_usize()).collect();
    let mut runs: usize = 0;
    for &ix in idx_set.iter() {
        // A run starts at an index whose predecessor is not itself present.
        if ix == 0 || !idx_set.contains(&(ix - 1)) {
            runs += 1;
        }
    }
    let val_set: HashSet<usize> = diffs.iter().map(|d| d.0.as_usize()).collect();
    FrameStats { n, runs, distinct: val_set.len() }
}

/// Running per-scheme byte totals over a window of frames. Feeds two decisions:
/// which static default to promote for a column (`recommend`), and whether an
/// active default is still optimal (compare `recommend` to it after a
/// re-calibration window). Pure accumulation, so it is verified exec.
#[derive(Clone, Copy)]
pub struct CalibrationStats {
    pub frames: usize,
    pub plain_total: usize,
    pub runs_total: usize,
    pub dict_total: usize,
}

impl CalibrationStats {
    pub fn new() -> CalibrationStats {
        CalibrationStats { frames: 0, plain_total: 0, runs_total: 0, dict_total: 0 }
    }

    /// Fold one frame's would-be sizes into the totals, at the shipped encoders'
    /// achievable widths (sorted run count, narrow code width).
    #[verifier::external_body]
    pub fn observe(&mut self, stats: FrameStats, t: usize, i: usize) {
        self.frames = self.frames.saturating_add(1);
        self.plain_total = self.plain_total.saturating_add(stats.plain_bytes(t, i));
        self.runs_total = self.runs_total.saturating_add(stats.runs_bytes(t));
        self.dict_total = self.dict_total.saturating_add(stats.dict_bytes(t, i));
    }

    /// The scheme with the smallest total over the observed frames — the default
    /// to promote for this column on this class of workload.
    pub fn recommend(&self) -> CompressionMode {
        if self.runs_total <= self.dict_total && self.runs_total < self.plain_total {
            // Same honesty point as `best_mode`: the runs totals are sorted-run
            // counts, so promote the sorted encoder.
            CompressionMode::IndexRunsSorted
        } else if self.dict_total < self.plain_total {
            CompressionMode::ValueDict
        } else {
            CompressionMode::None
        }
    }
}

/// Calibrated-adaptive scheme selection: run the exact-size selector (`Auto`) for
/// a calibration window, promote the average winner to a static default, run the
/// default for a period, then re-calibrate — so the per-frame adaptive cost is
/// paid only during the (short) calibration windows, not every frame. This is the
/// policy the e-graph columns use: the first frames of a workload establish each
/// column's default; periodic windows check the default is still optimal.
#[derive(Clone, Copy)]
pub struct CalibrationPolicy {
    /// Frames spent calibrating (running `Auto` + observing) before promoting.
    pub window: usize,
    /// Frames spent on the promoted default before re-calibrating.
    pub period: usize,
    /// True while calibrating; false while running the default.
    pub calibrating: bool,
    /// Frames elapsed in the current phase.
    pub counter: usize,
    /// The promoted default (meaningful once a calibration window has completed).
    pub default: CompressionMode,
    /// Byte totals accumulated during the current calibration window.
    pub stats: CalibrationStats,
}

impl CalibrationPolicy {
    pub fn new(window: usize, period: usize) -> CalibrationPolicy {
        CalibrationPolicy {
            window,
            period,
            calibrating: true,
            counter: 0,
            default: CompressionMode::None,
            stats: CalibrationStats::new(),
        }
    }

    /// The mode for the next flush: `Auto` (per-frame exact) while calibrating,
    /// the promoted default in steady state. Verified: a pure phase read.
    pub fn flush_mode(&self) -> CompressionMode {
        if self.calibrating {
            CompressionMode::Auto
        } else {
            self.default
        }
    }

    /// Advance the state machine by one observed frame. During calibration, fold
    /// the frame's would-be sizes in and, at the end of the window, promote the
    /// winner and switch to the default. During the default phase, count down to
    /// the next re-calibration. `external_body`: heuristic bookkeeping (counters
    /// and size folds), no correctness surface.
    #[verifier::external_body]
    pub fn observe_frame(&mut self, stats: FrameStats, t: usize, i: usize) {
        if self.calibrating {
            self.stats.observe(stats, t, i);
            self.counter = self.counter.saturating_add(1);
            if self.counter >= self.window {
                self.default = self.stats.recommend();
                self.calibrating = false;
                self.counter = 0;
                self.stats = CalibrationStats::new();
            }
        } else {
            self.counter = self.counter.saturating_add(1);
            if self.counter >= self.period {
                self.calibrating = true;
                self.counter = 0;
                self.stats = CalibrationStats::new();
            }
        }
    }
}

} // verus!
