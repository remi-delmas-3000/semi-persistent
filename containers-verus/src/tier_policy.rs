// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Execution policy for the three-tier Vec history.
//!
//! Limits apply only to closed frames. The newest ingress frame is always
//! retained and writable. `Unbounded` is explicit and never rolls history
//! automatically.

/// Controls Trail -> Hot -> Cold conversion performed by one mark.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RolloverPolicy {
    /// Seal the old frame and open the new frame without converting history.
    Defer,
    /// Apply the vector's configured tier limits (and legacy cadence).
    ApplyConfigured,
    /// Convert every closed prefix selected by each enabled edge.
    ///
    /// When both edges are enabled, Trail -> Hot always runs before
    /// Hot -> Cold so newly deduplicated frames can become cold in the same
    /// mark.
    ForceClosed {
        trail_to_hot: bool,
        hot_to_cold: bool,
    },
}

impl Default for RolloverPolicy {
    fn default() -> Self {
        Self::ApplyConfigured
    }
}

/// Automatic retention limit for one non-terminal tier.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TierLimit {
    /// Never migrate this tier automatically.
    Unbounded,
    /// Retain at most this many closed frames.
    Frames(usize),
    /// Retain the newest closed-frame suffix whose payload fits this count.
    Entries(usize),
    /// Retain the newest closed-frame suffix whose payload fits this many bytes.
    Bytes(usize),
    /// Use representation-specific density/locality heuristics.
    Adaptive,
}

/// Capacity treatment for terminal cold pools after suffix truncation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReclaimPolicy {
    /// Preserve allocations for reuse.
    RetainCapacity,
    /// Release unused capacity after migration or restore.
    ShrinkToFit,
}

/// Independent retention policy for chronological and unique history.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TierPolicy {
    pub trail: TierLimit,
    pub hot: TierLimit,
    pub cold_reclaim: ReclaimPolicy,
}

impl TierPolicy {
    /// Frequent-backtrack profile: formation is append-only and no automatic
    /// conversion occurs.
    pub const fn smt() -> Self {
        Self {
            trail: TierLimit::Unbounded,
            hot: TierLimit::Unbounded,
            cold_reclaim: ReclaimPolicy::RetainCapacity,
        }
    }

    /// Duplicate-sensitive profile. Trail frames dedupe when writes are at
    /// least twice their unique set. Unique hot frames remain buffered until
    /// explicit compression; a future pressure signal may trigger that same
    /// transition without making locality alone a pressure proxy.
    pub const fn adaptive() -> Self {
        Self {
            trail: TierLimit::Adaptive,
            hot: TierLimit::Unbounded,
            cold_reclaim: ReclaimPolicy::RetainCapacity,
        }
    }

    /// Direct-unique profile: every closed unique frame is run-compressed.
    pub const fn restore_optimized() -> Self {
        Self {
            trail: TierLimit::Frames(0),
            hot: TierLimit::Frames(0),
            cold_reclaim: ReclaimPolicy::RetainCapacity,
        }
    }

    /// Unique ingress with arbitrary hot buffering and no automatic cold work.
    pub const fn fully_buffered_unique() -> Self {
        Self {
            trail: TierLimit::Frames(0),
            hot: TierLimit::Unbounded,
            cold_reclaim: ReclaimPolicy::RetainCapacity,
        }
    }
}

impl Default for TierPolicy {
    fn default() -> Self {
        Self::fully_buffered_unique()
    }
}

/// Observable physical occupancy for policy tests and operational diagnostics.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TierStats {
    pub trail_frames: usize,
    pub trail_entries: usize,
    pub hot_frames: usize,
    pub hot_entries: usize,
    pub cold_frames: usize,
    pub cold_runs: usize,
    pub cold_values: usize,
}
