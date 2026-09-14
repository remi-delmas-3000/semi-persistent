// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Focused execution-first tests for the policy-driven three-tier Vec runtime.

use semi_persistent_containers_verus::{
    CompressionMode, DiffStore, MarkOptions, ParallelStore, ReclaimPolicy, RolloverPolicy,
    ShrinkPolicy, StoreKind, TierLimit, TierPolicy, Vec as SpVec, VecD, VecI, VecP, VecT,
};

type V = VecD<u32, u32, true>;

fn policy(trail: TierLimit, hot: TierLimit) -> TierPolicy {
    TierPolicy {
        trail,
        hot,
        cold_reclaim: ReclaimPolicy::RetainCapacity,
    }
}

fn values<S>(v: &SpVec<u32, u32, S, true>) -> std::vec::Vec<u32>
where
    S: DiffStore<u32, u32, true>,
{
    (0..v.len()).map(|i| v.get(i)).collect()
}

#[test]
fn unbounded_protocols_preserve_duplicate_semantics_and_arbitrary_frames() {
    let mut trail = V::new_kind_with_policy(StoreKind::Trail, TierPolicy::smt());
    let mut unique =
        V::new_kind_with_policy(StoreKind::Parallel, TierPolicy::fully_buffered_unique());
    for i in 0..4 {
        trail.try_push(i).unwrap();
        unique.try_push(i).unwrap();
    }
    let trail_token = trail.try_mark(ShrinkPolicy::Never).unwrap();
    let unique_token = unique.try_mark(ShrinkPolicy::Never).unwrap();
    for frame in 0..12u32 {
        for write in 0..10u32 {
            trail.set(1u32, frame * 100 + write);
            unique.set(1u32, frame * 100 + write);
        }
        if frame != 11 {
            trail.try_mark(ShrinkPolicy::Never).unwrap();
            unique.try_mark(ShrinkPolicy::Never).unwrap();
        }
    }

    let ts = trail.tier_stats();
    let us = unique.tier_stats();
    assert_eq!(ts.trail_frames, 12);
    assert_eq!(ts.hot_frames + ts.cold_frames, 0);
    assert_eq!(ts.trail_entries, 120);
    assert_eq!(us.hot_frames, 12);
    assert_eq!(us.trail_frames + us.cold_frames, 0);
    assert_eq!(us.hot_entries, 12);

    trail.try_restore(trail_token).unwrap();
    unique.try_restore(unique_token).unwrap();
    assert_eq!(values(&trail), vec![0, 1, 2, 3]);
    assert_eq!(values(&unique), vec![0, 1, 2, 3]);
}

#[test]
fn zero_and_finite_trail_budgets_migrate_only_closed_oldest_prefixes() {
    let mut zero = V::new_kind_with_policy(
        StoreKind::Trail,
        policy(TierLimit::Frames(0), TierLimit::Frames(0)),
    );
    zero.try_push(0).unwrap();
    for n in 0..5u32 {
        zero.try_mark(ShrinkPolicy::Never).unwrap();
        zero.set(0u32, n + 1);
    }
    let zs = zero.tier_stats();
    assert_eq!(
        zs.trail_frames, 1,
        "the open ingress frame is never migrated"
    );
    assert_eq!(zs.hot_frames, 0);
    assert_eq!(zs.cold_frames, 4);

    let mut entries = V::new_kind_with_policy(
        StoreKind::Trail,
        policy(TierLimit::Entries(2), TierLimit::Unbounded),
    );
    entries.try_push(0).unwrap();
    for n in 0..4u32 {
        entries.try_mark(ShrinkPolicy::Never).unwrap();
        entries.set(0u32, n + 1);
    }
    let es = entries.tier_stats();
    assert_eq!(es.hot_frames, 1);
    assert_eq!(es.trail_frames, 3, "two closed frames plus the open frame");

    let pair_bytes = core::mem::size_of::<(u32, u32)>();
    entries.set_tier_policy(policy(TierLimit::Bytes(pair_bytes), TierLimit::Unbounded));
    entries.apply_tier_policy();
    let bs = entries.tier_stats();
    assert_eq!(bs.hot_frames, 2);
    assert_eq!(bs.trail_frames, 2, "one closed frame plus the open frame");
}

#[test]
fn restore_targets_trail_hot_and_cold_with_nonmonotone_lengths() {
    let mut v = V::new_kind_with_policy(
        StoreKind::Trail,
        policy(TierLimit::Frames(1), TierLimit::Frames(1)),
    );
    for i in 0..6u32 {
        v.try_push(i).unwrap();
    }
    let t0 = v.try_mark(ShrinkPolicy::Never).unwrap();
    v.set(0u32, 10);
    let t1 = v.try_mark(ShrinkPolicy::Never).unwrap();
    v.pop();
    v.pop();
    v.set(0u32, 20);
    let t2 = v.try_mark(ShrinkPolicy::Never).unwrap();
    v.try_push(60).unwrap();
    v.set(1u32, 30);
    let t3 = v.try_mark(ShrinkPolicy::Never).unwrap();
    v.set(2u32, 40);

    let s = v.tier_stats();
    assert_eq!((s.cold_frames, s.hot_frames, s.trail_frames), (1, 1, 2));

    v.try_restore(t3).unwrap();
    assert_eq!(values(&v), vec![20, 30, 2, 3, 60]);
    v.try_restore(t2).unwrap();
    assert_eq!(values(&v), vec![20, 1, 2, 3]);
    assert_eq!(
        v.tier_stats().trail_frames,
        1,
        "hot survivor promoted to trail ingress"
    );
    v.try_restore(t1).unwrap();
    assert_eq!(values(&v), vec![10, 1, 2, 3, 4, 5]);
    assert_eq!(
        v.tier_stats().trail_frames,
        1,
        "cold survivor promoted to trail ingress"
    );
    v.try_restore(t0).unwrap();
    assert_eq!(values(&v), vec![0, 1, 2, 3, 4, 5]);
    assert_eq!(v.depth(), 0);
}

#[test]
fn first_capture_zero_hot_budget_restores_direct_cold_runs() {
    let mut v = V::new_kind_with_policy(StoreKind::Parallel, TierPolicy::restore_optimized());
    for i in 0..8u32 {
        v.try_push(i).unwrap();
    }
    let root = v.try_mark(ShrinkPolicy::Never).unwrap();
    for frame in 0..4u32 {
        for i in 1..6u32 {
            v.set(i, frame * 100 + i);
            v.set(i, frame * 1000 + i); // duplicate suppressed online
        }
        if frame != 3 {
            v.try_mark(ShrinkPolicy::Never).unwrap();
        }
    }
    let s = v.tier_stats();
    assert_eq!(s.trail_frames, 0);
    assert_eq!(s.hot_frames, 1);
    assert_eq!(s.cold_frames, 3);
    assert_eq!(
        s.cold_runs, 3,
        "each clustered frame becomes one direct run"
    );
    v.try_restore(root).unwrap();
    assert_eq!(values(&v), (0..8).collect::<Vec<_>>());
}

#[test]
fn adaptive_policy_dedupes_trail_but_requires_explicit_cold_conversion() {
    let mut v = V::new_kind_with_policy(StoreKind::Trail, TierPolicy::adaptive());
    for i in 0..8u32 {
        v.try_push(i).unwrap();
    }
    v.try_mark(ShrinkPolicy::Never).unwrap();
    for round in 0..4u32 {
        for i in 2..6u32 {
            v.set(i, 100 * round + i);
        }
    }
    v.try_mark(ShrinkPolicy::Never).unwrap();
    let s = v.tier_stats();
    assert_eq!(s.trail_frames, 1);
    assert_eq!(s.hot_frames, 1, "duplicate-dense trail dedupes to hot");
    assert_eq!(s.hot_entries, 4);
    assert_eq!(s.cold_frames, 0, "locality alone is not memory pressure");

    v.compress_hot();
    let compressed = v.tier_stats();
    assert_eq!(compressed.hot_frames, 0);
    assert_eq!(compressed.cold_frames, 1);
    assert_eq!(compressed.cold_runs, 1);
}

#[test]
fn promote_write_remigrate_and_restore_older_history() {
    let mut v = V::new_kind_with_policy(
        StoreKind::Trail,
        policy(TierLimit::Frames(0), TierLimit::Frames(0)),
    );
    for i in 0..5u32 {
        v.try_push(i).unwrap();
    }
    let root = v.try_mark(ShrinkPolicy::Never).unwrap();
    v.set(0u32, 10);
    let into_cold = v.try_mark(ShrinkPolicy::Never).unwrap();
    v.set(1u32, 20);
    v.try_mark(ShrinkPolicy::Never).unwrap();
    v.set(2u32, 30);
    assert!(v.tier_stats().cold_frames >= 2);

    v.try_restore(into_cold).unwrap();
    assert_eq!(values(&v), vec![10, 1, 2, 3, 4]);
    assert_eq!(
        v.tier_stats().trail_frames,
        1,
        "cold survivor is selected ingress"
    );

    v.set(3u32, 99);
    v.try_mark(ShrinkPolicy::Never).unwrap();
    v.set(4u32, 77);
    assert!(
        v.tier_stats().cold_frames >= 1,
        "promoted frame remigrated without orphan payload"
    );

    v.try_restore(root).unwrap();
    assert_eq!(values(&v), vec![0, 1, 2, 3, 4]);
}

#[test]
fn explicit_flush_and_compress_preserve_empty_frame_identity() {
    let mut v = V::new_kind_with_policy(StoreKind::Trail, TierPolicy::smt());
    v.try_push(7).unwrap();
    let root = v.try_mark(ShrinkPolicy::Never).unwrap();
    v.try_mark(ShrinkPolicy::Never).unwrap(); // close an empty logical frame
    v.set(0u32, 8);
    v.set(0u32, 9);
    v.try_mark(ShrinkPolicy::Never).unwrap();

    assert_eq!(v.diff_log_len(), 2);
    v.flush_trail();
    let hot = v.tier_stats();
    assert_eq!(
        (hot.trail_frames, hot.hot_frames, hot.hot_entries),
        (1, 2, 1)
    );
    assert_eq!(v.depth(), 3, "empty frame remains a token boundary");
    assert_eq!(v.diff_log_len(), 1, "dedupe keeps the first capture");

    v.compress_hot();
    let cold = v.tier_stats();
    assert_eq!(
        (cold.cold_frames, cold.cold_runs, cold.cold_values),
        (2, 1, 1)
    );
    assert_eq!(v.diff_log_len(), 0);
    assert!(v.pending_restore_indices(&root).is_some());

    v.try_restore(root).unwrap();
    assert_eq!(values(&v), vec![7]);
}

#[test]
fn scattered_cold_runs_promote_unique_survivor_and_keep_tokens_live() {
    let mut v = V::new_kind_with_policy(StoreKind::Parallel, TierPolicy::restore_optimized());
    for i in 0..8u32 {
        v.try_push(i).unwrap();
    }
    let root = v.try_mark(ShrinkPolicy::Never).unwrap();
    v.set(1u32, 10);
    v.set(3u32, 30);
    v.set(6u32, 60);
    let middle = v.try_mark(ShrinkPolicy::Never).unwrap();
    v.set(0u32, 99);
    v.try_mark(ShrinkPolicy::Never).unwrap();

    let cold = v.tier_stats();
    assert_eq!(cold.cold_frames, 2);
    assert_eq!(cold.cold_runs, 4, "three scattered runs plus one singleton");
    assert_eq!(cold.cold_values, 4);
    let mut pending: Vec<u32> = v.pending_restore_indices(&root).unwrap();
    pending.sort_unstable();
    assert_eq!(pending, vec![0, 1, 3, 6]);
    assert!(v.is_valid_token(&root));
    assert!(v.is_valid_token(&middle));

    v.try_restore(middle).unwrap();
    assert_eq!(values(&v), vec![0, 10, 2, 30, 4, 5, 60, 7]);
    assert!(v.is_valid_token(&root));
    assert!(!v.is_valid_token(&middle));
    assert_eq!(
        v.tier_stats().hot_frames,
        1,
        "cold survivor promoted to unique ingress"
    );

    v.set(2u32, 20);
    v.try_mark(ShrinkPolicy::Never).unwrap();
    assert_eq!(
        v.tier_stats().cold_frames,
        1,
        "promoted survivor remigrates"
    );
    v.try_restore(root).unwrap();
    assert_eq!(values(&v), (0..8).collect::<Vec<_>>());
    assert!(!v.is_valid_token(&root));
}

#[test]
fn hot_entry_and_byte_limits_and_reclamation_apply_to_closed_suffixes() {
    let mut v = V::new_kind_with_policy(StoreKind::Parallel, TierPolicy::fully_buffered_unique());
    for i in 0..4u32 {
        v.try_push(i).unwrap();
    }
    let root = v.try_mark(ShrinkPolicy::Never).unwrap();
    for frame in 0..3u32 {
        v.set(frame, 10 + frame);
        v.try_mark(ShrinkPolicy::Never).unwrap();
    }

    v.set_tier_policy(policy(TierLimit::Frames(0), TierLimit::Entries(2)));
    v.apply_tier_policy();
    assert_eq!(
        (v.tier_stats().cold_frames, v.tier_stats().hot_frames),
        (1, 3)
    );

    let pair_bytes = core::mem::size_of::<(u32, u32)>();
    v.set_tier_policy(policy(TierLimit::Frames(0), TierLimit::Bytes(pair_bytes)));
    v.apply_tier_policy();
    assert_eq!(
        (v.tier_stats().cold_frames, v.tier_stats().hot_frames),
        (2, 2)
    );

    v.set_tier_policy(TierPolicy {
        trail: TierLimit::Frames(0),
        hot: TierLimit::Frames(0),
        cold_reclaim: ReclaimPolicy::ShrinkToFit,
    });
    v.apply_tier_policy();
    let before_restore = v.tracking_bytes();
    assert_eq!(
        (v.tier_stats().cold_frames, v.tier_stats().hot_frames),
        (3, 1)
    );
    v.try_restore(root).unwrap();
    assert_eq!(values(&v), vec![0, 1, 2, 3]);
    assert!(v.tracking_bytes() <= before_restore);
}

#[test]
fn legacy_vec_modes_and_trail_store_preserve_whole_batch_rollover() {
    for mode in [
        CompressionMode::ValueDict,
        CompressionMode::IndexRuns,
        CompressionMode::IndexRunsSorted,
        CompressionMode::Auto,
    ] {
        let mut v = VecP::<u32, u32>::new_with_mode(mode);
        v.try_push(0).unwrap();
        let root = v.try_mark(ShrinkPolicy::Never).unwrap();
        for n in 0..9u32 {
            v.set(0u32, n + 1);
            v.try_mark(ShrinkPolicy::Never).unwrap();
        }
        let stats = v.tier_stats();
        assert_eq!((stats.cold_frames, stats.hot_frames), (9, 1));
        assert_eq!(v.diff_log_len(), 0, "the whole closed batch migrated");
        v.try_restore(root).unwrap();
        assert_eq!(values(&v), vec![0]);
    }

    let mut trail: VecT<u32, u32> = VecT::new();
    trail.try_push(0).unwrap();
    let root = trail.try_mark(ShrinkPolicy::Never).unwrap();
    for n in 0..8u32 {
        trail.set(0u32, n + 1);
        trail.try_mark(ShrinkPolicy::Never).unwrap();
    }
    assert_eq!(
        (
            trail.tier_stats().cold_frames,
            trail.tier_stats().trail_frames
        ),
        (0, 9)
    );
    trail.set(0u32, 9);
    trail.try_mark(ShrinkPolicy::Never).unwrap();
    assert_eq!(
        (
            trail.tier_stats().cold_frames,
            trail.tier_stats().trail_frames
        ),
        (9, 1)
    );
    assert_eq!(trail.diff_log_len(), 0);
    trail.try_restore(root).unwrap();
    assert_eq!(trail.get(0u32), 0);
}

#[test]
fn explicit_policy_replaces_legacy_rollover_cadence() {
    let mut v = VecP::<u32, u32>::new_with_mode(CompressionMode::Auto);
    v.try_push(0).unwrap();
    let root = v.try_mark(ShrinkPolicy::Never).unwrap();
    for n in 0..8u32 {
        v.set(0u32, n + 1);
        v.try_mark(ShrinkPolicy::Never).unwrap();
    }

    v.set_tier_policy(TierPolicy::fully_buffered_unique());
    v.set(0u32, 9);
    v.try_mark(ShrinkPolicy::Never).unwrap();

    let stats = v.tier_stats();
    assert_eq!((stats.cold_frames, stats.hot_frames), (0, 10));
    assert_eq!(v.diff_log_len(), 9);
    v.try_restore(root).unwrap();
    assert_eq!(values(&v), vec![0]);
}

#[test]
fn dynamic_store_protocols_cover_pop_regrow_and_cold_restore() {
    for kind in [StoreKind::Inline, StoreKind::Parallel, StoreKind::Trail] {
        let mut v: VecD<u32, u32> =
            VecD::new_kind_with_policy(kind, TierPolicy::restore_optimized());
        for i in 10..14u32 {
            v.try_push(i).unwrap();
        }
        let root = v.try_mark(ShrinkPolicy::Never).unwrap();
        assert_eq!(v.pop(), Some(13));
        v.try_push(99).unwrap();
        v.set(3u32, 100);
        v.try_mark(ShrinkPolicy::Never).unwrap();
        assert_eq!(v.tier_stats().cold_frames, 1);

        assert_eq!(v.pop(), Some(100));
        v.try_push(77).unwrap();
        v.set(3u32, 88);
        v.try_restore(root).unwrap();
        assert_eq!(
            (0..v.len()).map(|i| v.get(i)).collect::<Vec<_>>(),
            vec![10, 11, 12, 13]
        );
    }
}

#[test]
fn pending_indices_derive_the_open_ingress_end_from_the_pool() {
    for (kind, expected) in [
        (StoreKind::Trail, vec![1, 1, 2]),
        (StoreKind::Parallel, vec![1, 2]),
    ] {
        let tier_policy = if kind == StoreKind::Trail {
            TierPolicy::smt()
        } else {
            TierPolicy::fully_buffered_unique()
        };
        let mut v = V::new_kind_with_policy(kind, tier_policy);
        for i in 0..4 {
            v.try_push(i).unwrap();
        }
        let token = v.try_mark(ShrinkPolicy::Never).unwrap();
        v.set(1u32, 10);
        v.set(1u32, 11);
        v.set(2u32, 20);

        let pending = v.pending_restore_indices(&token).unwrap();
        assert_eq!(pending, expected);

        v.try_restore(token).unwrap();
        assert_eq!(values(&v), vec![0, 1, 2, 3]);
    }
}

#[test]
fn mark_rollover_defer_and_apply_configured_are_per_mark() {
    let mut v = V::new_kind_with_policy(
        StoreKind::Trail,
        policy(TierLimit::Frames(0), TierLimit::Frames(0)),
    );
    v.try_push(0).unwrap();
    let root = v.try_mark(ShrinkPolicy::Never).unwrap();
    v.set(0u32, 1);

    v.try_mark_with(MarkOptions::new(ShrinkPolicy::Never, RolloverPolicy::Defer))
        .unwrap();
    assert_eq!(
        (
            v.tier_stats().cold_frames,
            v.tier_stats().hot_frames,
            v.tier_stats().trail_frames
        ),
        (0, 0, 2),
        "defer only seals and opens"
    );

    v.set(0u32, 2);
    v.try_mark_with(MarkOptions::new(
        ShrinkPolicy::Never,
        RolloverPolicy::ApplyConfigured,
    ))
    .unwrap();
    assert_eq!(
        (
            v.tier_stats().cold_frames,
            v.tier_stats().hot_frames,
            v.tier_stats().trail_frames
        ),
        (2, 0, 1),
        "configured zero limits apply to all closed prefixes"
    );
    v.try_restore(root).unwrap();
    assert_eq!(values(&v), vec![0]);
}

#[test]
fn mark_rollover_force_trail_to_hot_only() {
    let mut v = V::new_kind_with_policy(StoreKind::Trail, TierPolicy::smt());
    v.try_push(7).unwrap();
    let root = v.try_mark(ShrinkPolicy::Never).unwrap();
    v.set(0u32, 8);
    v.set(0u32, 9);
    v.try_mark_with(MarkOptions::new(
        ShrinkPolicy::Never,
        RolloverPolicy::ForceClosed {
            trail_to_hot: true,
            hot_to_cold: false,
        },
    ))
    .unwrap();
    assert_eq!(
        (
            v.tier_stats().cold_frames,
            v.tier_stats().hot_frames,
            v.tier_stats().trail_frames
        ),
        (0, 1, 1)
    );
    assert_eq!(v.tier_stats().hot_entries, 1);
    v.try_restore(root).unwrap();
    assert_eq!(values(&v), vec![7]);
}

#[test]
fn mark_rollover_force_hot_to_cold_only() {
    let mut v = V::new_kind_with_policy(StoreKind::Parallel, TierPolicy::fully_buffered_unique());
    for i in 0..4u32 {
        v.try_push(i).unwrap();
    }
    let root = v.try_mark(ShrinkPolicy::Never).unwrap();
    v.set(1u32, 10);
    v.set(2u32, 20);
    v.try_mark_with(MarkOptions::new(
        ShrinkPolicy::Never,
        RolloverPolicy::ForceClosed {
            trail_to_hot: false,
            hot_to_cold: true,
        },
    ))
    .unwrap();
    assert_eq!(
        (
            v.tier_stats().cold_frames,
            v.tier_stats().hot_frames,
            v.tier_stats().trail_frames
        ),
        (1, 1, 0)
    );
    assert_eq!(v.tier_stats().cold_runs, 1);
    v.try_restore(root).unwrap();
    assert_eq!(values(&v), vec![0, 1, 2, 3]);
}

#[test]
fn mark_rollover_force_both_preserves_empty_frames_and_restore() {
    let mut v = V::new_kind_with_policy(StoreKind::Trail, TierPolicy::smt());
    v.try_push(5).unwrap();
    let root = v.try_mark(ShrinkPolicy::Never).unwrap();
    let force_both = MarkOptions::new(
        ShrinkPolicy::Never,
        RolloverPolicy::ForceClosed {
            trail_to_hot: true,
            hot_to_cold: true,
        },
    );

    v.try_mark_with(force_both).unwrap();
    assert_eq!(
        (
            v.tier_stats().cold_frames,
            v.tier_stats().cold_runs,
            v.tier_stats().trail_frames
        ),
        (1, 0, 1),
        "an empty closed frame remains a cold token boundary"
    );
    v.set(0u32, 6);
    v.try_mark_with(force_both).unwrap();
    assert_eq!(
        (
            v.tier_stats().cold_frames,
            v.tier_stats().hot_frames,
            v.tier_stats().trail_frames
        ),
        (2, 0, 1),
        "forced cascade runs Trail -> Hot before Hot -> Cold"
    );
    assert_eq!(v.depth(), 3);
    v.try_restore(root).unwrap();
    assert_eq!(values(&v), vec![5]);
    assert_eq!(v.depth(), 0);
}

#[test]
fn static_aliases_and_legacy_direct_types_compile() {
    let parallel: VecP<u32, u32> = VecP::new();
    let inline: VecI<u32, u32> = VecI::new();
    let direct_parallel: SpVec<u32, u32, ParallelStore<u32, u32>> =
        SpVec::<u32, u32, ParallelStore<u32, u32>>::new();
    let direct_inline: SpVec<u32, u32, semi_persistent_containers_verus::InlineStore<u32, u32>> =
        SpVec::<u32, u32, semi_persistent_containers_verus::InlineStore<u32, u32>>::new();
    let trail: VecT<u32, u32> = VecT::new();
    let direct_trail: SpVec<
        u32,
        u32,
        semi_persistent_containers_verus::trail_store::TrailStore<u32, u32>,
    > = SpVec::<u32, u32, semi_persistent_containers_verus::trail_store::TrailStore<u32, u32>>::new(
    );
    let direct_dynamic: SpVec<
        u32,
        u32,
        semi_persistent_containers_verus::dyn_store::DynStore<u32, u32>,
    > = SpVec::<
        u32,
        u32,
        semi_persistent_containers_verus::dyn_store::DynStore<u32, u32>,
    >::new_kind(StoreKind::Trail);

    let _ = (
        parallel,
        inline,
        direct_parallel,
        direct_inline,
        trail,
        direct_trail,
        direct_dynamic,
    );
}

#[test]
fn mark_options_preserve_thresholded_shrink_policy() {
    let mut v = V::new_kind(StoreKind::Parallel);
    for i in 0..1024u32 {
        v.try_push(i).unwrap();
    }
    for _ in 1..1024 {
        v.pop();
    }
    let before = v.total_bytes();
    let token = v
        .try_mark_with(MarkOptions::new(
            ShrinkPolicy::IfOverallocated {
                factor: 2,
                headroom: 0,
            },
            RolloverPolicy::Defer,
        ))
        .unwrap();
    assert!(
        v.total_bytes() < before,
        "store capacity should honor shrink thresholds"
    );
    assert_eq!(values(&v), vec![0]);
    v.try_restore(token).unwrap();
}

fn adaptive_input(
    max_closed_history_bytes: usize,
) -> semi_persistent_containers_verus::AdaptiveInput {
    semi_persistent_containers_verus::AdaptiveInput {
        max_closed_history_bytes,
        min_writes_per_unique: semi_persistent_containers_verus::Ratio::new(2, 1).unwrap(),
        min_uniques_per_run: semi_persistent_containers_verus::Ratio::new(2, 1).unwrap(),
    }
}

fn close_deferred(v: &mut V) {
    v.try_mark_with(MarkOptions::new(ShrinkPolicy::Never, RolloverPolicy::Defer))
        .unwrap();
}

fn adaptive_reclaim_fixture(kind: StoreKind, reclaim: ReclaimPolicy) -> V {
    let mut v = V::new_kind_with_policy(
        kind,
        TierPolicy {
            trail: TierLimit::Unbounded,
            hot: TierLimit::Unbounded,
            cold_reclaim: reclaim,
        },
    );
    for i in 0..64u32 {
        v.try_push(i).unwrap();
    }
    close_deferred(&mut v);
    for frame in 0..256u32 {
        for write in 0..64u32 {
            let index = write % 16;
            v.set(index, (frame << 16) ^ write);
        }
        close_deferred(&mut v);
    }
    v
}

#[test]
fn adaptive_shrink_reclaims_migrated_tier_capacities_without_changing_report() {
    for kind in [StoreKind::Trail, StoreKind::Inline, StoreKind::Parallel] {
        let mut retained = adaptive_reclaim_fixture(kind, ReclaimPolicy::RetainCapacity);
        let retained_before = retained.tracking_bytes();
        let retained_report = retained.apply_adaptive(adaptive_input(0));
        let retained_after = retained.tracking_bytes();

        let mut shrunk = adaptive_reclaim_fixture(kind, ReclaimPolicy::ShrinkToFit);
        let no_op_before = shrunk.tracking_bytes();
        let no_op = shrunk.apply_adaptive(adaptive_input(usize::MAX));
        assert_eq!(no_op.inspected_frames, 0, "kind {kind:?}");
        assert_eq!(shrunk.tracking_bytes(), no_op_before, "kind {kind:?}");

        let shrink_before = shrunk.tracking_bytes();
        let shrink_report = shrunk.apply_adaptive(adaptive_input(0));
        let shrink_after = shrunk.tracking_bytes();

        assert_eq!(shrink_report, retained_report, "kind {kind:?}");
        assert!(shrink_report.migrated_frames > 0, "kind {kind:?}");
        assert_eq!(shrunk.tier_stats(), retained.tier_stats(), "kind {kind:?}");
        assert_eq!(values(&shrunk), values(&retained), "kind {kind:?}");
        assert!(
            retained_after > retained_before,
            "RetainCapacity should preserve vacated pools while allocating the destination, kind {kind:?}: {retained_before} -> {retained_after}"
        );
        assert!(
            shrink_after <= shrink_before,
            "ShrinkToFit should not increase tracking capacity, kind {kind:?}: {shrink_before} -> {shrink_after}"
        );
        assert!(
            retained_after.saturating_sub(shrink_after) >= 1024,
            "ShrinkToFit should materially reclaim deterministic fixture capacity, kind {kind:?}: retain={retained_after}, shrink={shrink_after}"
        );
    }
}

#[test]
fn adaptive_ratio_validation_and_budget_boundaries_are_exact() {
    use semi_persistent_containers_verus::Ratio;

    assert!(Ratio::new(2, 0).is_err());
    assert_eq!(Ratio::new(6, 3).unwrap().numerator(), 6);
    assert_eq!(Ratio::new(6, 3).unwrap().denominator(), 3);

    let mut v = V::new_kind_with_policy(StoreKind::Trail, TierPolicy::smt());
    for i in 0..4u32 {
        v.try_push(i).unwrap();
    }
    v.try_mark(ShrinkPolicy::Never).unwrap();
    for round in 0..4u32 {
        v.set(1u32, 10 + round);
    }
    close_deferred(&mut v);

    let observed = v.apply_adaptive(adaptive_input(usize::MAX));
    assert_eq!(
        observed.inspected_frames, 0,
        "an already-met budget is a no-op"
    );
    assert_eq!(observed.logical_bytes_before, observed.logical_bytes_after);
    assert_eq!(observed.budget_unmet_bytes, 0);

    let boundary = v.apply_adaptive(adaptive_input(observed.logical_bytes_before));
    assert_eq!(boundary.inspected_frames, 0, "equality is within budget");
    assert_eq!(boundary.logical_bytes_before, boundary.logical_bytes_after);
    assert_eq!(v.tier_stats().trail_frames, 2);
}

#[test]
fn adaptive_duplicate_threshold_passes_and_fails_without_skipping() {
    let mut pass = V::new_kind_with_policy(StoreKind::Trail, TierPolicy::smt());
    for i in 0..4u32 {
        pass.try_push(i).unwrap();
    }
    pass.try_mark(ShrinkPolicy::Never).unwrap();
    for round in 0..4u32 {
        pass.set(1u32, 20 + round);
    }
    close_deferred(&mut pass);
    let report = pass.apply_adaptive(adaptive_input(0));
    assert_eq!((report.writes, report.uniques), (4, 1));
    assert_eq!(
        (report.inspected_trail_frames, report.migrated_trail_frames),
        (1, 1)
    );
    assert_eq!(
        (pass.tier_stats().trail_frames, pass.tier_stats().hot_frames),
        (1, 1)
    );

    let mut blocked = V::new_kind_with_policy(StoreKind::Trail, TierPolicy::smt());
    for i in 0..4u32 {
        blocked.try_push(i).unwrap();
    }
    blocked.try_mark(ShrinkPolicy::Never).unwrap();
    blocked.set(0u32, 10);
    blocked.set(1u32, 11); // W/U = 1: oldest blocker
    close_deferred(&mut blocked);
    for round in 0..4u32 {
        blocked.set(2u32, 30 + round);
    }
    close_deferred(&mut blocked);
    let report = blocked.apply_adaptive(adaptive_input(0));
    assert_eq!(
        (report.inspected_trail_frames, report.migrated_trail_frames),
        (1, 0)
    );
    assert_eq!(blocked.tier_stats().trail_frames, 3);
    assert_eq!(
        blocked.tier_stats().hot_frames,
        0,
        "later eligible history cannot leapfrog"
    );
}

#[test]
fn adaptive_locality_accepts_contiguous_and_rejects_singletons() {
    let mut contiguous =
        V::new_kind_with_policy(StoreKind::Parallel, TierPolicy::fully_buffered_unique());
    for i in 0..16u32 {
        contiguous.try_push(i).unwrap();
    }
    contiguous.try_mark(ShrinkPolicy::Never).unwrap();
    for i in 2..10u32 {
        contiguous.set(i, 100 + i);
    }
    close_deferred(&mut contiguous);
    let report = contiguous.apply_adaptive(adaptive_input(0));
    assert_eq!((report.uniques, report.runs), (8, 1));
    assert_eq!(
        (report.inspected_hot_frames, report.migrated_hot_frames),
        (1, 1)
    );
    assert_eq!(
        (
            contiguous.tier_stats().cold_frames,
            contiguous.tier_stats().hot_frames
        ),
        (1, 1)
    );

    let mut singleton =
        V::new_kind_with_policy(StoreKind::Parallel, TierPolicy::fully_buffered_unique());
    for i in 0..32u32 {
        singleton.try_push(i).unwrap();
    }
    singleton.try_mark(ShrinkPolicy::Never).unwrap();
    for i in 0..8u32 {
        singleton.set(i * 2, 200 + i);
    }
    close_deferred(&mut singleton);
    let report = singleton.apply_adaptive(adaptive_input(0));
    assert_eq!((report.uniques, report.runs), (8, 8));
    assert_eq!(
        (report.inspected_hot_frames, report.migrated_hot_frames),
        (1, 0)
    );
    assert_eq!(report.budget_unmet_bytes, report.logical_bytes_after);
    assert_eq!(singleton.tier_stats().cold_frames, 0);

    let strict = semi_persistent_containers_verus::AdaptiveInput {
        max_closed_history_bytes: 0,
        min_writes_per_unique: semi_persistent_containers_verus::Ratio::new(2, 1).unwrap(),
        min_uniques_per_run: semi_persistent_containers_verus::Ratio::new(3, 1).unwrap(),
    };
    let mut ratio_blocked =
        V::new_kind_with_policy(StoreKind::Parallel, TierPolicy::fully_buffered_unique());
    for i in 0..4u32 {
        ratio_blocked.try_push(i).unwrap();
    }
    ratio_blocked.try_mark(ShrinkPolicy::Never).unwrap();
    ratio_blocked.set(0u32, 9);
    ratio_blocked.set(1u32, 8);
    close_deferred(&mut ratio_blocked);
    let report = ratio_blocked.apply_adaptive(strict);
    assert_eq!(
        (report.uniques, report.runs, report.migrated_hot_frames),
        (2, 1, 0)
    );
}

#[test]
fn adaptive_empty_frames_preserve_identity_and_cascade_in_order() {
    let mut empty = V::new_kind_with_policy(StoreKind::Trail, TierPolicy::smt());
    empty.try_push(7).unwrap();
    let root = empty.try_mark(ShrinkPolicy::Never).unwrap();
    close_deferred(&mut empty);
    let report = empty.apply_adaptive(adaptive_input(0));
    assert_eq!((report.writes, report.uniques, report.runs), (0, 0, 0));
    assert_eq!(
        (report.migrated_trail_frames, report.migrated_hot_frames),
        (1, 1)
    );
    assert_eq!(
        (
            empty.tier_stats().cold_frames,
            empty.tier_stats().trail_frames
        ),
        (1, 1)
    );
    assert_eq!(empty.depth(), 2);
    assert!(empty.is_valid_token(&root));
    empty.try_restore(root).unwrap();
    assert_eq!(values(&empty), vec![7]);

    let mut cascade = V::new_kind_with_policy(StoreKind::Trail, TierPolicy::smt());
    for i in 0..16u32 {
        cascade.try_push(i).unwrap();
    }
    let root = cascade.try_mark(ShrinkPolicy::Never).unwrap();
    for round in 0..4u32 {
        for i in 2..10u32 {
            cascade.set(i, round * 100 + i);
        }
    }
    close_deferred(&mut cascade);
    let report = cascade.apply_adaptive(adaptive_input(0));
    assert_eq!((report.writes, report.uniques, report.runs), (32, 8, 1));
    assert_eq!(
        (report.migrated_trail_frames, report.migrated_hot_frames),
        (1, 1)
    );
    assert_eq!(
        (
            cascade.tier_stats().cold_frames,
            cascade.tier_stats().hot_frames,
            cascade.tier_stats().trail_frames
        ),
        (1, 0, 1)
    );
    assert_eq!(report.budget_unmet_bytes, report.logical_bytes_after);
    cascade.try_restore(root).unwrap();
    assert_eq!(values(&cascade), (0..16).collect::<Vec<_>>());
}

#[test]
fn try_mark_adaptive_opens_replacement_first_and_preserves_token_semantics() {
    let mut v = V::new_kind_with_policy(StoreKind::Trail, TierPolicy::smt());
    for i in 0..8u32 {
        v.try_push(i).unwrap();
    }
    let root = v.try_mark(ShrinkPolicy::Never).unwrap();
    for round in 0..4u32 {
        for i in 2..6u32 {
            v.set(i, round * 10 + i);
        }
    }
    let after_writes = values(&v);
    let depth_before = v.depth();
    let (token, report) = v
        .try_mark_adaptive(ShrinkPolicy::Never, adaptive_input(0))
        .unwrap();
    assert_eq!(v.depth(), depth_before + 1);
    assert!(v.is_valid_token(&token));
    assert!(v.is_valid_token(&root));
    assert_eq!(report.migrated_trail_frames, 1);
    assert_eq!(
        v.tier_stats().trail_frames,
        1,
        "replacement Trail ingress stays open"
    );

    v.set(0u32, 999);
    v.try_restore(token).unwrap();
    assert_eq!(values(&v), after_writes);
    assert!(!v.is_valid_token(&token));
    assert!(v.is_valid_token(&root));
    v.try_restore(root).unwrap();
    assert_eq!(values(&v), (0..8).collect::<Vec<_>>());
}

#[test]
fn adaptive_handles_nonmonotone_lengths_promotion_and_every_ingress_store() {
    for kind in [StoreKind::Inline, StoreKind::Parallel, StoreKind::Trail] {
        let policy = if kind == StoreKind::Trail {
            TierPolicy::smt()
        } else {
            TierPolicy::fully_buffered_unique()
        };
        let mut v = V::new_kind_with_policy(kind, policy);
        for i in 0..12u32 {
            v.try_push(i).unwrap();
        }
        let root = v.try_mark(ShrinkPolicy::Never).unwrap();
        for round in 0..4u32 {
            for i in 2..8u32 {
                v.set(i, round * 100 + i);
            }
        }
        close_deferred(&mut v);
        v.pop();
        v.pop();
        v.set(2u32, 777);
        let middle = v
            .try_mark_adaptive(ShrinkPolicy::Never, adaptive_input(0))
            .unwrap()
            .0;
        v.try_push(90).unwrap();
        v.set(3u32, 888);
        close_deferred(&mut v);
        v.apply_adaptive(adaptive_input(0));

        v.try_restore(middle).unwrap();
        assert_eq!(v.len(), 10);
        v.set(4u32, 444); // write through the original immutable ingress protocol
        close_deferred(&mut v);
        v.apply_adaptive(adaptive_input(0));
        if kind == StoreKind::Trail {
            assert!(
                v.tier_stats().trail_frames >= 1,
                "Trail ingress retains its writable frame"
            );
        } else {
            assert_eq!(v.tier_stats().trail_frames, 0);
            assert!(
                v.tier_stats().hot_frames >= 1,
                "unique ingress retains its writable Hot frame"
            );
        }
        v.try_restore(root).unwrap();
        assert_eq!(values(&v), (0..12).collect::<Vec<_>>(), "kind {kind:?}");
    }
}

fn adaptive_input_with_ratios(
    max_closed_history_bytes: usize,
    min_writes_per_unique: (usize, usize),
    min_uniques_per_run: (usize, usize),
) -> semi_persistent_containers_verus::AdaptiveInput {
    semi_persistent_containers_verus::AdaptiveInput {
        max_closed_history_bytes,
        min_writes_per_unique: semi_persistent_containers_verus::Ratio::new(
            min_writes_per_unique.0,
            min_writes_per_unique.1,
        )
        .unwrap(),
        min_uniques_per_run: semi_persistent_containers_verus::Ratio::new(
            min_uniques_per_run.0,
            min_uniques_per_run.1,
        )
        .unwrap(),
    }
}

fn trail_frame_bytes(entries: usize) -> usize {
    core::mem::size_of::<semi_persistent_containers_verus::frame::TrailFrame<u32>>()
        + entries * core::mem::size_of::<(u32, u32)>()
}

fn hot_frame_bytes(entries: usize) -> usize {
    core::mem::size_of::<semi_persistent_containers_verus::frame::HotFrame<u32>>()
        + entries * core::mem::size_of::<(u32, u32)>()
}

fn cold_frame_bytes(values: usize, runs: usize) -> usize {
    core::mem::size_of::<semi_persistent_containers_verus::frame::ColdFrameHdr<u32>>()
        + values * core::mem::size_of::<u32>()
        + runs * core::mem::size_of::<semi_persistent_containers_verus::frame::IndexRun<u32>>()
}

#[test]
fn adaptive_hot_blocker_prevents_newer_frame_leapfrog() {
    let mut v = V::new_kind_with_policy(StoreKind::Parallel, TierPolicy::fully_buffered_unique());
    for i in 0..16u32 {
        v.try_push(i).unwrap();
    }
    v.try_mark(ShrinkPolicy::Never).unwrap();

    for i in [0u32, 2, 4, 6] {
        v.set(i, 100 + i);
    }
    close_deferred(&mut v);
    for i in 8..16u32 {
        v.set(i, 200 + i);
    }
    close_deferred(&mut v);

    let report = v.apply_adaptive(adaptive_input(0));
    assert_eq!((report.uniques, report.runs), (4, 4));
    assert_eq!(
        (report.inspected_hot_frames, report.migrated_hot_frames),
        (1, 0)
    );
    assert_eq!(
        (v.tier_stats().hot_frames, v.tier_stats().cold_frames),
        (3, 0),
        "the newer contiguous frame must not leapfrog the oldest blocker"
    );
}

#[test]
fn adaptive_projected_byte_gates_are_ratio_independent() {
    assert_eq!(trail_frame_bytes(2), hot_frame_bytes(2));
    let mut trail = V::new_kind_with_policy(StoreKind::Trail, TierPolicy::smt());
    for i in 0..8u32 {
        trail.try_push(i).unwrap();
    }
    trail.try_mark(ShrinkPolicy::Never).unwrap();
    trail.set(0u32, 10);
    trail.set(1u32, 11);
    close_deferred(&mut trail);
    let report = trail.apply_adaptive(adaptive_input_with_ratios(0, (1, 1), (1, 1)));
    assert_eq!((report.writes, report.uniques), (2, 2));
    assert_eq!(report.migrated_trail_frames, 0);

    assert!(cold_frame_bytes(2, 1) > hot_frame_bytes(2));
    let mut growing_hot =
        V::new_kind_with_policy(StoreKind::Parallel, TierPolicy::fully_buffered_unique());
    for i in 0..8u32 {
        growing_hot.try_push(i).unwrap();
    }
    growing_hot.try_mark(ShrinkPolicy::Never).unwrap();
    growing_hot.set(0u32, 10);
    growing_hot.set(1u32, 11);
    close_deferred(&mut growing_hot);
    let report = growing_hot.apply_adaptive(adaptive_input_with_ratios(0, (1, 1), (2, 1)));
    assert_eq!((report.uniques, report.runs), (2, 1));
    assert_eq!(report.migrated_hot_frames, 0);

    assert_eq!(cold_frame_bytes(6, 1), hot_frame_bytes(6));
    let mut equal_hot =
        V::new_kind_with_policy(StoreKind::Parallel, TierPolicy::fully_buffered_unique());
    for i in 0..12u32 {
        equal_hot.try_push(i).unwrap();
    }
    equal_hot.try_mark(ShrinkPolicy::Never).unwrap();
    for i in 2..8u32 {
        equal_hot.set(i, 100 + i);
    }
    close_deferred(&mut equal_hot);
    let report = equal_hot.apply_adaptive(adaptive_input_with_ratios(0, (1, 1), (2, 1)));
    assert_eq!((report.uniques, report.runs), (6, 1));
    assert_eq!(report.migrated_hot_frames, 1);
}

#[test]
fn adaptive_closed_accounting_and_mixed_cascade_report_are_exact() {
    let mut v = V::new_kind_with_policy(StoreKind::Trail, TierPolicy::smt());
    for i in 0..32u32 {
        v.try_push(i).unwrap();
    }
    v.try_mark(ShrinkPolicy::Never).unwrap();

    for i in 0..6u32 {
        v.set(i, 100 + i);
        v.set(i, 200 + i);
    }
    close_deferred(&mut v);
    let first = v.apply_adaptive(adaptive_input_with_ratios(0, (2, 1), (7, 1)));
    assert_eq!(
        (
            first.migrated_trail_frames,
            first.inspected_hot_frames,
            first.migrated_hot_frames
        ),
        (1, 1, 0)
    );

    for i in 8..16u32 {
        v.set(i, 300 + i);
        v.set(i, 400 + i);
    }
    close_deferred(&mut v);

    let expected_before = hot_frame_bytes(6) + trail_frame_bytes(16);
    let no_op = v.apply_adaptive(adaptive_input(usize::MAX));
    assert_eq!(no_op.logical_bytes_before, expected_before);
    assert_eq!(no_op.logical_bytes_after, expected_before);

    let values_before_live_growth = values(&v);
    for i in 0..4096u32 {
        v.try_push(10_000 + i).unwrap();
    }
    for _ in 0..4096 {
        v.pop();
    }
    assert_eq!(values(&v), values_before_live_growth);
    let after_live_growth = v.apply_adaptive(adaptive_input(usize::MAX));
    assert_eq!(after_live_growth.logical_bytes_before, expected_before);

    let tracking_bytes_before = v.tracking_bytes();
    for i in 0..4096u32 {
        v.set(20u32, 20_000 + i);
    }
    assert!(
        v.tracking_bytes() > tracking_bytes_before,
        "open ingress payload and its allocation must grow independently"
    );
    let after_open_writes = v.apply_adaptive(adaptive_input(usize::MAX));
    assert_eq!(after_open_writes.logical_bytes_before, expected_before);
    assert_eq!(after_open_writes.logical_bytes_after, expected_before);

    let expected_after = 2 * cold_frame_bytes(7, 1);
    let report = v.apply_adaptive(adaptive_input(0));
    assert_eq!(
        (
            report.inspected_trail_frames,
            report.migrated_trail_frames,
            report.inspected_hot_frames,
            report.migrated_hot_frames,
            report.inspected_frames,
            report.migrated_frames
        ),
        (1, 1, 2, 2, 3, 3)
    );
    assert_eq!((report.writes, report.uniques, report.runs), (16, 14, 2));
    assert_eq!(report.logical_bytes_before, expected_before);
    assert_eq!(report.logical_bytes_after, expected_after);
    assert_eq!(report.budget_unmet_bytes, expected_after);
    assert_eq!(
        (
            v.tier_stats().trail_frames,
            v.tier_stats().hot_frames,
            v.tier_stats().cold_frames,
            v.tier_stats().cold_values,
            v.tier_stats().cold_runs
        ),
        (1, 0, 2, 14, 2)
    );
}
