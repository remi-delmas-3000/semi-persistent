// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! E5 measurements for the policy-driven three-tier tracked Vec runtime.
//!
//! Fixtures are deterministic and are rebuilt outside timed loops. Production
//! arms are workload controls only: production implements first-capture-wins
//! history, not the explicit trail/hot/cold policies measured here. Tier
//! occupancy and capacity-based byte diagnostics are emitted outside timing.

use criterion::{BatchSize, BenchmarkId, Criterion, criterion_group, criterion_main};
use semi_persistent_containers as prod;
use semi_persistent_containers_verus as verus;
use std::alloc::{GlobalAlloc, Layout, System};
use std::hint::black_box;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Duration;
use verus::{
    MarkOptions, ReclaimPolicy, RolloverPolicy, ShrinkPolicy, StoreKind, TierLimit, TierPolicy,
};

type V = verus::VecD<u64, u32, true>;
type P = prod::VecP<u64, u32, true>;

const N: usize = 8_192;
const WRITES: usize = 512;
const FRAMES: usize = 8;
const TRACE_FRAMES: usize = 24;
const TRACE_WRITES: usize = 32;

struct CountingAllocator;

static ALLOCATOR_LIVE_BYTES: AtomicUsize = AtomicUsize::new(0);
static ALLOCATOR_PEAK_BYTES: AtomicUsize = AtomicUsize::new(0);

#[global_allocator]
static GLOBAL_ALLOCATOR: CountingAllocator = CountingAllocator;

fn record_allocation(bytes: usize) {
    let live = ALLOCATOR_LIVE_BYTES.fetch_add(bytes, Ordering::SeqCst) + bytes;
    ALLOCATOR_PEAK_BYTES.fetch_max(live, Ordering::SeqCst);
}

fn record_deallocation(bytes: usize) {
    ALLOCATOR_LIVE_BYTES.fetch_sub(bytes, Ordering::SeqCst);
}

unsafe impl GlobalAlloc for CountingAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let ptr = unsafe { System.alloc(layout) };
        if !ptr.is_null() {
            record_allocation(layout.size());
        }
        ptr
    }

    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        let ptr = unsafe { System.alloc_zeroed(layout) };
        if !ptr.is_null() {
            record_allocation(layout.size());
        }
        ptr
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        unsafe { System.dealloc(ptr, layout) };
        record_deallocation(layout.size());
    }

    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        let new_ptr = unsafe { System.realloc(ptr, layout, new_size) };
        if !new_ptr.is_null() {
            if new_size >= layout.size() {
                record_allocation(new_size - layout.size());
            } else {
                record_deallocation(layout.size() - new_size);
            }
        }
        new_ptr
    }
}

#[derive(Clone, Copy)]
struct AllocationWindow {
    before_bytes: usize,
    after_bytes: usize,
    peak_bytes: usize,
}

impl AllocationWindow {
    fn peak_growth_bytes(self) -> usize {
        self.peak_bytes.saturating_sub(self.before_bytes)
    }

    fn transient_peak_bytes(self) -> usize {
        self.peak_bytes
            .saturating_sub(self.before_bytes.max(self.after_bytes))
    }
}

fn allocation_window(operation: impl FnOnce()) -> AllocationWindow {
    let before_bytes = ALLOCATOR_LIVE_BYTES.load(Ordering::SeqCst);
    ALLOCATOR_PEAK_BYTES.store(before_bytes, Ordering::SeqCst);
    operation();
    let after_bytes = ALLOCATOR_LIVE_BYTES.load(Ordering::SeqCst);
    let peak_bytes = ALLOCATOR_PEAK_BYTES
        .load(Ordering::SeqCst)
        .max(before_bytes)
        .max(after_bytes);
    AllocationWindow {
        before_bytes,
        after_bytes,
        peak_bytes,
    }
}

fn report_allocation(label: &str, window: AllocationWindow) {
    eprintln!(
        "three_tier_allocator label={label} before_bytes={} after_bytes={} peak_bytes={} peak_growth_bytes={} transient_peak_bytes={}",
        window.before_bytes,
        window.after_bytes,
        window.peak_bytes,
        window.peak_growth_bytes(),
        window.transient_peak_bytes(),
    );
}

#[derive(Clone, Copy)]
struct Profile {
    name: &'static str,
    kind: StoreKind,
    policy: TierPolicy,
}

const PROFILES: [Profile; 4] = [
    Profile {
        name: "trail_smt",
        kind: StoreKind::Trail,
        policy: TierPolicy::smt(),
    },
    Profile {
        name: "trail_adaptive",
        kind: StoreKind::Trail,
        policy: TierPolicy::adaptive(),
    },
    Profile {
        name: "inline_restore_optimized",
        kind: StoreKind::Inline,
        policy: TierPolicy::restore_optimized(),
    },
    Profile {
        name: "parallel_buffered_unique",
        kind: StoreKind::Parallel,
        policy: TierPolicy::fully_buffered_unique(),
    },
];

fn finite_all_tiers_policy() -> TierPolicy {
    TierPolicy {
        trail: TierLimit::Frames(1),
        hot: TierLimit::Frames(1),
        cold_reclaim: ReclaimPolicy::RetainCapacity,
    }
}

fn build_verus(kind: StoreKind, policy: TierPolicy) -> V {
    let mut v = verus::VecD::<u64, u32, true>::new_kind_with_policy(kind, policy);
    for i in 0..N {
        v.try_push(i as u64).expect("fixture fits u32 index");
    }
    v
}

fn build_prod() -> P {
    let mut v = P::new();
    for i in 0..N {
        v.push(i as u64);
    }
    v
}

#[inline]
fn index_for(write: usize, distinct: usize, frame: usize) -> u32 {
    ((write.wrapping_mul(2_053) + frame.wrapping_mul(97)) % distinct) as u32
}

fn write_verus(v: &mut V, writes: usize, distinct: usize, frame: usize) {
    for write in 0..writes {
        let index = index_for(write, distinct, frame);
        let value = ((frame as u64) << 40) ^ write as u64 ^ 0x9E37_79B9;
        v.set_index(index, value);
    }
}

fn write_prod(v: &mut P, writes: usize, distinct: usize, frame: usize) {
    for write in 0..writes {
        let index = index_for(write, distinct, frame);
        let value = ((frame as u64) << 40) ^ write as u64 ^ 0x9E37_79B9;
        v.set(index, value);
    }
}

fn mark_verus(v: &mut V) -> verus::vec::VecToken {
    v.try_mark(ShrinkPolicy::Never)
        .expect("fixture depth is bounded")
}

fn build_closed_trail(frames: usize, writes: usize, distinct: usize) -> V {
    let mut v = build_verus(StoreKind::Trail, TierPolicy::smt());
    mark_verus(&mut v);
    for frame in 0..frames {
        write_verus(&mut v, writes, distinct, frame);
        mark_verus(&mut v);
    }
    assert!(v.tier_stats().trail_frames > frames);
    v
}

fn build_closed_hot(frames: usize, writes: usize, distinct: usize) -> V {
    let mut v = build_verus(StoreKind::Parallel, TierPolicy::fully_buffered_unique());
    mark_verus(&mut v);
    for frame in 0..frames {
        write_verus(&mut v, writes, distinct, frame);
        mark_verus(&mut v);
    }
    assert!(v.tier_stats().hot_frames > frames);
    v
}

fn trail_restore_fixture() -> (V, verus::vec::VecToken) {
    let mut v = build_verus(StoreKind::Trail, TierPolicy::smt());
    let token = mark_verus(&mut v);
    write_verus(&mut v, WRITES, 32, 0);
    assert_eq!(v.tier_stats().trail_entries, WRITES);
    (v, token)
}

fn hot_restore_fixture() -> (V, verus::vec::VecToken) {
    let mut v = build_verus(StoreKind::Parallel, TierPolicy::fully_buffered_unique());
    let token = mark_verus(&mut v);
    write_verus(&mut v, WRITES, WRITES, 0);
    assert_eq!(v.tier_stats().hot_entries, WRITES);
    (v, token)
}

fn cold_restore_fixture() -> (V, verus::vec::VecToken) {
    let mut v = build_verus(StoreKind::Parallel, TierPolicy::restore_optimized());
    let token = mark_verus(&mut v);
    write_verus(&mut v, WRITES, WRITES, 0);
    mark_verus(&mut v);
    assert!(v.tier_stats().cold_frames > 0);
    (v, token)
}

fn all_tiers_restore_fixture() -> (V, verus::vec::VecToken) {
    let mut v = build_verus(StoreKind::Trail, finite_all_tiers_policy());
    let root = mark_verus(&mut v);
    for frame in 0..6 {
        write_verus(&mut v, WRITES, 64, frame);
        mark_verus(&mut v);
    }
    let stats = v.tier_stats();
    assert!(stats.trail_frames > 0 && stats.hot_frames > 0 && stats.cold_frames > 0);
    (v, root)
}

fn prod_restore_fixture() -> (P, prod::VecToken) {
    let mut v = build_prod();
    let token = v.mark(prod::ShrinkPolicy::Never);
    write_prod(&mut v, WRITES, WRITES, 0);
    (v, token)
}

fn promotion_fixture() -> (V, verus::vec::VecToken) {
    let mut v = build_verus(StoreKind::Parallel, TierPolicy::restore_optimized());
    let mut tokens = Vec::with_capacity(5);
    for frame in 0..5 {
        tokens.push(mark_verus(&mut v));
        write_verus(&mut v, WRITES, WRITES, frame);
    }
    mark_verus(&mut v);
    assert!(v.tier_stats().cold_frames >= 5);
    (v, tokens[2])
}

fn logical_tier_bytes(stats: verus::TierStats) -> (usize, usize, usize) {
    let pair = core::mem::size_of::<(u64, u32)>();
    let trail = stats.trail_entries * pair
        + stats.trail_frames * core::mem::size_of::<verus::frame::TrailFrame<u32>>();
    let hot = stats.hot_entries * pair
        + stats.hot_frames * core::mem::size_of::<verus::frame::HotFrame<u32>>();
    let cold = stats.cold_values * core::mem::size_of::<u64>()
        + stats.cold_runs * core::mem::size_of::<verus::frame::IndexRun<u32>>()
        + stats.cold_frames * core::mem::size_of::<verus::frame::ColdFrameHdr<u32>>();
    (trail, hot, cold)
}

fn report_one(label: &str, v: &V) {
    let stats = v.tier_stats();
    let (trail_bytes, hot_bytes, cold_bytes) = logical_tier_bytes(stats);
    eprintln!(
        "three_tier_stats label={label} stats={stats:?} logical_trail_bytes={trail_bytes} logical_hot_bytes={hot_bytes} logical_cold_bytes={cold_bytes} tracking_bytes={} total_bytes={}",
        v.tracking_bytes(),
        v.total_bytes()
    );
}

fn report_tier_diagnostics() {
    let (trail, _) = trail_restore_fixture();
    report_one("restore_trail", &trail);
    let (hot, _) = hot_restore_fixture();
    report_one("restore_hot", &hot);
    let (cold, _) = cold_restore_fixture();
    report_one("restore_cold", &cold);
    let (all, _) = all_tiers_restore_fixture();
    report_one("restore_all", &all);

    let mut converted = build_closed_trail(FRAMES, WRITES, 32);
    let before = converted.tracking_bytes();
    let before_stats = converted.tier_stats();
    let before_logical = logical_tier_bytes(before_stats);
    converted.flush_trail();
    let after_stats = converted.tier_stats();
    let after_logical = logical_tier_bytes(after_stats);
    eprintln!(
        "three_tier_conversion label=trail_to_hot before_bytes={before} after_bytes={} reclaimed_bytes={} before_logical={before_logical:?} after_logical={after_logical:?} stats={after_stats:?}",
        converted.tracking_bytes(),
        before.saturating_sub(converted.tracking_bytes()),
    );

    let mut compressed = build_closed_hot(FRAMES, WRITES, WRITES);
    let before = compressed.tracking_bytes();
    let before_stats = compressed.tier_stats();
    let before_logical = logical_tier_bytes(before_stats);
    compressed.compress_hot();
    let after_stats = compressed.tier_stats();
    let after_logical = logical_tier_bytes(after_stats);
    eprintln!(
        "three_tier_conversion label=hot_to_cold before_bytes={before} after_bytes={} reclaimed_bytes={} before_logical={before_logical:?} after_logical={after_logical:?} stats={after_stats:?}",
        compressed.tracking_bytes(),
        before.saturating_sub(compressed.tracking_bytes()),
    );

    let (mut promoted, token) = promotion_fixture();
    promoted.try_restore(token).expect("own ancestor token");
    report_one("promotion_after_restore", &promoted);
}

fn report_allocation_diagnostics() {
    let mut converted = build_closed_trail(FRAMES, WRITES, 32);
    let window = allocation_window(|| converted.flush_trail());
    report_allocation("trail_to_hot", window);

    let mut compressed = build_closed_hot(FRAMES, WRITES, WRITES);
    let window = allocation_window(|| compressed.compress_hot());
    report_allocation("hot_to_cold", window);

    let (mut all, root) = all_tiers_restore_fixture();
    let window = allocation_window(|| all.try_restore(root).expect("own root token"));
    report_allocation("restore_all", window);

    let (mut promoted, ancestor) = promotion_fixture();
    let window = allocation_window(|| {
        promoted.try_restore(ancestor).expect("own ancestor token");
        let inner = mark_verus(&mut promoted);
        write_verus(&mut promoted, WRITES, 64, 17);
        promoted
            .try_restore(inner)
            .expect("new token after promotion");
    });
    report_allocation("promotion", window);
}

fn bench_write(c: &mut Criterion) {
    for &(density, distinct) in &[("low_duplicates", WRITES), ("high_duplicates", 32)] {
        let mut group = c.benchmark_group(format!("three_tier/write/{density}"));
        for profile in PROFILES {
            group.bench_function(profile.name, |b| {
                b.iter_batched_ref(
                    || {
                        let mut v = build_verus(profile.kind, profile.policy);
                        mark_verus(&mut v);
                        v
                    },
                    |v| {
                        write_verus(v, WRITES, distinct, 0);
                        black_box(v.diff_log_len())
                    },
                    BatchSize::LargeInput,
                )
            });
        }
        group.bench_function("production", |b| {
            b.iter_batched_ref(
                || {
                    let mut v = build_prod();
                    v.mark(prod::ShrinkPolicy::Never);
                    v
                },
                |v| {
                    write_prod(v, WRITES, distinct, 0);
                    black_box(v.len())
                },
                BatchSize::LargeInput,
            )
        });
        group.finish();
    }
}

fn bench_mark(c: &mut Criterion) {
    let mut group = c.benchmark_group("three_tier/mark");
    group.bench_function("no_rollover_smt", |b| {
        b.iter_batched_ref(
            || {
                let mut v = build_verus(StoreKind::Trail, TierPolicy::smt());
                mark_verus(&mut v);
                write_verus(&mut v, WRITES, WRITES, 0);
                v
            },
            |v| black_box(mark_verus(v)),
            BatchSize::LargeInput,
        )
    });
    group.bench_function("explicit_defer_smt", |b| {
        b.iter_batched_ref(
            || {
                let mut v = build_verus(StoreKind::Trail, TierPolicy::smt());
                mark_verus(&mut v);
                write_verus(&mut v, WRITES, WRITES, 0);
                v
            },
            |v| {
                black_box(
                    v.try_mark_with(MarkOptions::new(ShrinkPolicy::Never, RolloverPolicy::Defer))
                        .expect("fixture remains within mark limits"),
                )
            },
            BatchSize::LargeInput,
        )
    });
    group.bench_function("no_rollover_production", |b| {
        b.iter_batched_ref(
            || {
                let mut v = build_prod();
                v.mark(prod::ShrinkPolicy::Never);
                write_prod(&mut v, WRITES, WRITES, 0);
                v
            },
            |v| black_box(v.mark(prod::ShrinkPolicy::Never)),
            BatchSize::LargeInput,
        )
    });
    group.bench_function("trail_to_hot", |b| {
        b.iter_batched_ref(
            || {
                let policy = TierPolicy {
                    trail: TierLimit::Frames(0),
                    hot: TierLimit::Unbounded,
                    cold_reclaim: ReclaimPolicy::RetainCapacity,
                };
                let mut v = build_verus(StoreKind::Trail, policy);
                mark_verus(&mut v);
                write_verus(&mut v, WRITES, 32, 0);
                v
            },
            |v| black_box(mark_verus(v)),
            BatchSize::LargeInput,
        )
    });
    group.bench_function("hot_to_cold", |b| {
        b.iter_batched_ref(
            || {
                let mut v = build_verus(StoreKind::Parallel, TierPolicy::restore_optimized());
                mark_verus(&mut v);
                write_verus(&mut v, WRITES, WRITES, 0);
                v
            },
            |v| black_box(mark_verus(v)),
            BatchSize::LargeInput,
        )
    });
    group.finish();
}

fn bench_restore(c: &mut Criterion) {
    let mut group = c.benchmark_group("three_tier/restore");
    group.bench_function("trail_one_frame", |b| {
        b.iter_batched_ref(
            trail_restore_fixture,
            |(v, token)| {
                v.try_restore(*token).expect("own token");
                black_box(v.len())
            },
            BatchSize::LargeInput,
        )
    });
    group.bench_function("hot_one_frame", |b| {
        b.iter_batched_ref(
            hot_restore_fixture,
            |(v, token)| {
                v.try_restore(*token).expect("own token");
                black_box(v.len())
            },
            BatchSize::LargeInput,
        )
    });
    group.bench_function("cold_one_frame", |b| {
        b.iter_batched_ref(
            cold_restore_fixture,
            |(v, token)| {
                v.try_restore(*token).expect("own token");
                black_box(v.len())
            },
            BatchSize::LargeInput,
        )
    });
    group.bench_function("all_tiers_deep", |b| {
        b.iter_batched_ref(
            all_tiers_restore_fixture,
            |(v, token)| {
                v.try_restore(*token).expect("own root token");
                black_box(v.len())
            },
            BatchSize::LargeInput,
        )
    });
    group.bench_function("production_one_frame", |b| {
        b.iter_batched_ref(
            prod_restore_fixture,
            |(v, token)| {
                v.restore(*token);
                black_box(v.len())
            },
            BatchSize::LargeInput,
        )
    });
    group.finish();
}

fn bench_conversion(c: &mut Criterion) {
    let mut group = c.benchmark_group("three_tier/conversion");
    group.bench_function("trail_to_hot_dedupe", |b| {
        b.iter_batched_ref(
            || build_closed_trail(FRAMES, WRITES, 32),
            |v| {
                v.flush_trail();
                black_box(v.diff_log_len())
            },
            BatchSize::LargeInput,
        )
    });
    group.bench_function("hot_to_cold_runs", |b| {
        b.iter_batched_ref(
            || build_closed_hot(FRAMES, WRITES, WRITES),
            |v| {
                v.compress_hot();
                black_box(v.diff_log_len())
            },
            BatchSize::LargeInput,
        )
    });
    group.finish();
}

fn bench_promotion(c: &mut Criterion) {
    let mut group = c.benchmark_group("three_tier/promotion");
    group.bench_function("cold_survivor_write_restore", |b| {
        b.iter_batched_ref(
            promotion_fixture,
            |(v, ancestor)| {
                v.try_restore(*ancestor).expect("own ancestor token");
                let inner = mark_verus(v);
                write_verus(v, WRITES, 64, 17);
                v.try_restore(inner).expect("new token after promotion");
                black_box(v.diff_log_len())
            },
            BatchSize::LargeInput,
        )
    });
    group.finish();
}

fn bench_adaptive(c: &mut Criterion) {
    let mut group = c.benchmark_group("three_tier/adaptive_decision");
    for &(name, distinct) in &[
        ("low_duplicates_no_convert", WRITES),
        ("high_duplicates_convert", 32),
    ] {
        group.bench_with_input(BenchmarkId::new(name, WRITES), &distinct, |b, &distinct| {
            b.iter_batched_ref(
                || {
                    let mut v = build_verus(StoreKind::Trail, TierPolicy::adaptive());
                    mark_verus(&mut v);
                    write_verus(&mut v, WRITES, distinct, 0);
                    v
                },
                |v| black_box(mark_verus(v)),
                BatchSize::LargeInput,
            )
        });
    }
    group.finish();
}

fn run_smt_backtrack() -> usize {
    let mut v = build_verus(StoreKind::Trail, TierPolicy::smt());
    for frame in 0..64 {
        let token = mark_verus(&mut v);
        write_verus(&mut v, TRACE_WRITES, 8, frame);
        v.try_restore(token).expect("own token");
    }
    v.len() as usize
}

fn run_prod_backtrack() -> usize {
    let mut v = build_prod();
    for frame in 0..64 {
        let token = v.mark(prod::ShrinkPolicy::Never);
        write_prod(&mut v, TRACE_WRITES, 8, frame);
        v.restore(token);
    }
    v.len() as usize
}

fn run_nested(kind: StoreKind, policy: TierPolicy) -> usize {
    let mut v = build_verus(kind, policy);
    let root = mark_verus(&mut v);
    for frame in 0..TRACE_FRAMES {
        write_verus(&mut v, TRACE_WRITES, 16, frame);
        mark_verus(&mut v);
    }
    v.try_restore(root).expect("own root token");
    v.len() as usize
}

fn run_prod_nested() -> usize {
    let mut v = build_prod();
    let root = v.mark(prod::ShrinkPolicy::Never);
    for frame in 0..TRACE_FRAMES {
        write_prod(&mut v, TRACE_WRITES, 16, frame);
        v.mark(prod::ShrinkPolicy::Never);
    }
    v.restore(root);
    v.len() as usize
}

fn bench_end_to_end(c: &mut Criterion) {
    let mut group = c.benchmark_group("three_tier/end_to_end");
    group.bench_function("smt_backtrack", |b| {
        b.iter(|| black_box(run_smt_backtrack()))
    });
    group.bench_function("smt_backtrack_production", |b| {
        b.iter(|| black_box(run_prod_backtrack()))
    });
    group.bench_function("eqsat_retained", |b| {
        b.iter(|| black_box(run_nested(StoreKind::Trail, TierPolicy::adaptive())))
    });
    group.bench_function("eqsat_retained_production", |b| {
        b.iter(|| black_box(run_prod_nested()))
    });
    group.bench_function("restore_optimized", |b| {
        b.iter(|| {
            black_box(run_nested(
                StoreKind::Parallel,
                TierPolicy::restore_optimized(),
            ))
        })
    });
    group.bench_function("buffered_unique", |b| {
        b.iter(|| {
            black_box(run_nested(
                StoreKind::Parallel,
                TierPolicy::fully_buffered_unique(),
            ))
        })
    });
    group.finish();
}

fn bench_diagnostics(c: &mut Criterion) {
    report_tier_diagnostics();
    report_allocation_diagnostics();
    let mut group = c.benchmark_group("three_tier/diagnostics");
    group.bench_function("reporting_excluded_from_timing", |b| {
        b.iter(|| black_box(0usize))
    });
    group.finish();
}

criterion_group! {
    name = benches;
    config = Criterion::default()
        .sample_size(10)
        .warm_up_time(Duration::from_millis(250))
        .measurement_time(Duration::from_millis(500));
    targets =
        bench_diagnostics,
        bench_write,
        bench_mark,
        bench_restore,
        bench_conversion,
        bench_promotion,
        bench_adaptive,
        bench_end_to_end
}
criterion_main!(benches);
