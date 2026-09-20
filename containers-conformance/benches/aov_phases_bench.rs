// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! `aov/log` taken apart: which phase of the append-log pattern carries the
//! verified side's few per cent.
//!
//! `retained_containers_bench`'s `aov/log` row does 100 000 pushes with a mark
//! in the middle, a slice scan, and a restore, and has sat at 1.04–1.12 of the
//! legacy container for the whole branch without a root cause. Each phase is a
//! row here, on both sides, so the difference has an address.

use criterion::{BatchSize, Criterion, criterion_group, criterion_main};
use semi_persistent_containers as prod;
use semi_persistent_containers_verus as verus;
use semi_persistent_containers_verus::group::ForkHistory;
use std::hint::black_box;

const N: usize = 100_000;

type Legacy = prod::AppendOnlyVec<u64, usize, true>;
type Verified = ForkHistory<verus::AppendOnlyVec<u64, usize, true>>;

fn filled_legacy(n: usize) -> Legacy {
    let mut v = Legacy::new();
    for i in 0..n {
        v.push(i as u64);
    }
    v
}

fn filled_verified(n: usize) -> Verified {
    let mut v = ForkHistory::new(verus::AppendOnlyVec::new());
    for i in 0..n {
        v.try_push(i as u64).expect("push: within index word");
    }
    v
}

/// The pushes alone, from empty, no frame.
fn bench_push(c: &mut Criterion) {
    let mut g = c.benchmark_group("aov_phase/push");
    g.bench_function("legacy", |b| {
        b.iter(|| {
            let mut v = Legacy::new();
            for i in 0..N {
                v.push(i as u64);
            }
            black_box(v.len())
        })
    });
    g.bench_function("verified", |b| {
        b.iter(|| {
            let mut v: Verified = ForkHistory::new(verus::AppendOnlyVec::new());
            for i in 0..N {
                v.try_push(i as u64).expect("push: within index word");
            }
            black_box(v.len())
        })
    });
    g.finish();
}

/// The pushes into a pre-sized vec: growth taken out.
fn bench_push_presized(c: &mut Criterion) {
    let mut g = c.benchmark_group("aov_phase/push_presized");
    g.bench_function("legacy", |b| {
        b.iter_batched_ref(
            || {
                let mut v = filled_legacy(N);
                let tok = v.mark(prod::ShrinkPolicy::Never);
                v.restore(tok);
                v
            },
            |v| {
                for i in 0..N {
                    v.push(i as u64);
                }
                black_box(v.len())
            },
            BatchSize::LargeInput,
        )
    });
    g.bench_function("verified", |b| {
        b.iter_batched_ref(
            || filled_verified(N),
            |v| {
                for i in 0..N {
                    v.try_push(i as u64).expect("push: within index word");
                }
                black_box(v.len())
            },
            BatchSize::LargeInput,
        )
    });
    g.finish();
}

/// The slice scan alone.
fn bench_scan(c: &mut Criterion) {
    let mut g = c.benchmark_group("aov_phase/scan");
    let l = filled_legacy(N);
    let v = filled_verified(N);
    g.bench_function("legacy", |b| {
        b.iter(|| {
            let mut acc = 0u64;
            for x in l.as_slice() {
                acc = acc.wrapping_add(*x);
            }
            black_box(acc)
        })
    });
    g.bench_function("verified", |b| {
        b.iter(|| {
            let mut acc = 0u64;
            for x in v.as_slice() {
                acc = acc.wrapping_add(*x);
            }
            black_box(acc)
        })
    });
    g.finish();
}

/// Mark, push half again, restore: the frame machinery alone.
fn bench_mark_restore(c: &mut Criterion) {
    let mut g = c.benchmark_group("aov_phase/mark_restore");
    g.bench_function("legacy", |b| {
        b.iter_batched_ref(
            || filled_legacy(N / 2),
            |v| {
                let tok = v.mark(prod::ShrinkPolicy::Never);
                for i in 0..N / 2 {
                    v.push(i as u64);
                }
                v.restore(tok);
                black_box(v.len())
            },
            BatchSize::LargeInput,
        )
    });
    g.bench_function("verified", |b| {
        b.iter_batched_ref(
            || filled_verified(N / 2),
            |v| {
                let tok = v
                    .mark(verus::ShrinkPolicy::Never)
                    .expect("mark: depth bounded by this harness");
                for i in 0..N / 2 {
                    v.try_push(i as u64).expect("push: within index word");
                }
                assert!(v.restore_and_pop(tok), "restore: own token");
                black_box(v.len())
            },
            BatchSize::LargeInput,
        )
    });
    g.finish();
}

/// The whole `aov/log` body on each side, in a function the inliner cannot
/// merge into the harness, registered in both orders. If the two orders
/// disagree the composite row's difference is placement, not work.
#[inline(never)]
fn composite_legacy() -> (u64, usize) {
    let mut v = Legacy::new();
    for i in 0..N / 2 {
        v.push(i as u64);
    }
    let tok = v.mark(prod::ShrinkPolicy::Never);
    for i in 0..N / 2 {
        v.push(i as u64);
    }
    let mut acc = 0u64;
    for x in v.as_slice() {
        acc = acc.wrapping_add(*x);
    }
    v.restore(tok);
    (acc, v.len())
}

#[inline(never)]
fn composite_verified() -> (u64, usize) {
    let mut v: Verified = ForkHistory::new(verus::AppendOnlyVec::new());
    for i in 0..N / 2 {
        v.try_push(i as u64).expect("push: within index word");
    }
    let tok = v
        .mark(verus::ShrinkPolicy::Never)
        .expect("mark: depth bounded by this harness");
    for i in 0..N / 2 {
        v.try_push(i as u64).expect("push: within index word");
    }
    let mut acc = 0u64;
    for x in v.as_slice() {
        acc = acc.wrapping_add(*x);
    }
    assert!(v.restore_and_pop(tok), "restore: own token");
    (acc, v.len())
}

/// The legacy body with one small extra allocation live from the mark to the
/// end, as the verified side's history has. If this alone moves the legacy
/// time to the verified time, the composite difference is where the data
/// buffer lands relative to that allocation, not the container's work.
#[inline(never)]
fn composite_legacy_perturbed() -> (u64, usize) {
    let mut v = Legacy::new();
    for i in 0..N / 2 {
        v.push(i as u64);
    }
    let tok = v.mark(prod::ShrinkPolicy::Never);
    let stamps: std::vec::Vec<u64> = std::vec::Vec::with_capacity(4);
    for i in 0..N / 2 {
        v.push(i as u64);
    }
    let mut acc = 0u64;
    for x in v.as_slice() {
        acc = acc.wrapping_add(*x);
    }
    v.restore(tok);
    black_box(&stamps);
    (acc, v.len())
}

fn bench_composite(c: &mut Criterion) {
    let mut g = c.benchmark_group("aov_phase/composite");
    g.bench_function("legacy", |b| b.iter(|| black_box(composite_legacy())));
    g.bench_function("verified", |b| b.iter(|| black_box(composite_verified())));
    g.bench_function("legacy_perturbed", |b| {
        b.iter(|| black_box(composite_legacy_perturbed()))
    });
    g.finish();
    let mut g = c.benchmark_group("aov_phase/composite_swapped");
    g.bench_function("verified", |b| b.iter(|| black_box(composite_verified())));
    g.bench_function("legacy", |b| b.iter(|| black_box(composite_legacy())));
    g.finish();
}

criterion_group!(
    aov_phases,
    bench_push,
    bench_push_presized,
    bench_scan,
    bench_mark_restore,
    bench_composite
);
criterion_main!(aov_phases);
