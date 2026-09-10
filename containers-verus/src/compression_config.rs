// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Per-column compression configuration and the when-to-compress policy
//! (`doc/design/09-diff-stack-compression.md`, "Configuration object and when to
//! compress").
//!
//! An aggregate names, per column, both the encoder (`CompressionMode`) and the
//! policy that decides when the plain top is flushed into the compressed bottom.
//! One value, not a type: the SMT profile passes all-`None` and the eq-sat
//! profile passes a per-column table, from one binary.

use vstd::prelude::*;
use crate::diff_compress::CompressionMode;

verus! {

/// Compression configuration for one column: the encoder plus the flush policy.
///
/// `IndexRuns` is a planned third `CompressionMode` (the index-major
/// run-coalescing encoder and its bijection already exist at the `nat` index
/// level in `diff_compress`); integrating it into `FrameEncoding` needs an
/// `IndexLike` spec inverse to materialize `I` from a `usize` run start, so the
/// config's `scheme` today ranges over `{ None, ValueDict }`.
#[derive(Clone, Copy)]
pub struct ColumnConfig {
    /// How a finalized frame is encoded when flushed to the compressed bottom.
    pub scheme: CompressionMode,
    /// Flush the plain top only once its byte footprint reaches this percent of
    /// the live payload (base length times value size). `0` flushes on every
    /// eligible mark; the `None` scheme ignores the field (never flushes).
    pub compress_at_percent: u32,
    /// Keep this many most-recently-marked frames plain regardless of the
    /// trigger (the LRU floor), so an imminent backtrack pays no decode.
    pub keep_hot_frames: usize,
}

impl ColumnConfig {
    /// No compression (the SMT profile): the plain top is the whole history.
    pub const fn none() -> ColumnConfig {
        ColumnConfig { scheme: CompressionMode::None, compress_at_percent: 0, keep_hot_frames: 0 }
    }

    /// Value-dictionary compression with an explicit flush policy (eq-sat, on the
    /// union-find value columns once `dict_find` is hashed and codes narrowed).
    pub const fn value_dict(compress_at_percent: u32, keep_hot_frames: usize) -> ColumnConfig {
        ColumnConfig {
            scheme: CompressionMode::ValueDict,
            compress_at_percent,
            keep_hot_frames,
        }
    }

    /// Index-major run-coalescing with an explicit flush policy (eq-sat, on
    /// columns whose captured indices cluster into contiguous ranges — it drops
    /// the index column, the measured space win).
    pub const fn index_runs(compress_at_percent: u32, keep_hot_frames: usize) -> ColumnConfig {
        ColumnConfig {
            scheme: CompressionMode::IndexRuns,
            compress_at_percent,
            keep_hot_frames,
        }
    }

    /// Whether this column ever compresses (i.e. is not the `None` scheme).
    pub open spec fn compresses(self) -> bool {
        !matches!(self.scheme, CompressionMode::None)
    }

    /// The flush trigger: compress when the uncompressed trail has grown to
    /// `compress_at_percent` of the live payload. Reads two running sizes the
    /// two-stack already tracks: the uncompressed diff byte count and the base
    /// payload byte count (`base_len * value_size`). Saturating throughout, so a
    /// huge trail never wraps the comparison. `None` never fires.
    ///
    /// Exec mirror of `should_flush_spec`; both compute the same predicate so the
    /// policy is testable in isolation from the storage.
    pub fn should_flush(self, uncompressed_bytes: usize, base_bytes: usize) -> (r: bool)
        ensures r == self.should_flush_spec(uncompressed_bytes as nat, base_bytes as nat),
    {
        match self.scheme {
            CompressionMode::None => false,
            // Both compressing modes share the size-fraction trigger.
            CompressionMode::ValueDict | CompressionMode::IndexRuns => {
                // Both products fit u128: `uncompressed_bytes`/`base_bytes` are
                // usize (< 2^64 here, `global size_of usize == 8`), the percent is
                // u32 (< 2^32), so each product is < 2^96 << u128::MAX. The
                // nonlinear step bounds the variable*variable product by the
                // per-operand maxima; the constant*variable product Verus bounds
                // itself.
                let ub = uncompressed_bytes as u128;
                let bb = base_bytes as u128;
                let pc = self.compress_at_percent as u128;
                proof {
                    assert(ub <= u64::MAX as u128);
                    assert(bb <= u64::MAX as u128);
                    assert(pc <= u32::MAX as u128);
                    assert(bb * pc <= (u64::MAX as u128) * (u32::MAX as u128)) by (nonlinear_arith)
                        requires bb <= u64::MAX as u128, pc <= u32::MAX as u128;
                    assert((u64::MAX as u128) * (u32::MAX as u128) < u128::MAX) by (compute);
                }
                let lhs = ub * 100u128;
                let rhs = bb * pc;
                lhs >= rhs
            }
        }
    }

    pub open spec fn should_flush_spec(self, uncompressed_bytes: nat, base_bytes: nat) -> bool {
        match self.scheme {
            CompressionMode::None => false,
            CompressionMode::ValueDict | CompressionMode::IndexRuns =>
                uncompressed_bytes * 100 >= base_bytes * (self.compress_at_percent as nat),
        }
    }

    /// How many of the current `num_frames` plain frames to flush into the
    /// compressed bottom: everything except the `keep_hot_frames` most recent
    /// (the LRU floor). Saturating: never asks to flush more frames than exist,
    /// and returns `0` when the hot floor already covers the whole stack.
    pub fn frames_to_compress(self, num_frames: usize) -> (r: usize)
        ensures
            r == self.frames_to_compress_spec(num_frames as nat),
            r <= num_frames,
    {
        if num_frames > self.keep_hot_frames {
            num_frames - self.keep_hot_frames
        } else {
            0
        }
    }

    pub open spec fn frames_to_compress_spec(self, num_frames: nat) -> nat {
        if num_frames > self.keep_hot_frames as nat {
            (num_frames - self.keep_hot_frames as nat) as nat
        } else {
            0
        }
    }
}

} // verus!
