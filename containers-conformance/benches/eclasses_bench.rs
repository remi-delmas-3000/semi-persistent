// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Aggregate-level comparison of the retained former-production `EClasses`
//! and the verified kernel used by the engine. The workloads isolate the
//! merge/find/mark-restore operations from e-matching and instantiation.
//!
//! Criterion samples both implementations in the same executable. Historical
//! revision-to-revision comparison can additionally use baselines:
//!
//! ```text
//! cargo bench -p containers-conformance --bench eclasses_bench -- --save-baseline before
//! # ... apply the change ...
//! cargo bench -p containers-conformance --bench eclasses_bench -- --baseline before
//! ```
//!
use criterion::{BatchSize, BenchmarkId, Criterion, Throughput, criterion_group, criterion_main};
use semi_persistent_containers as retained;
use semi_persistent_containers_verus as verified;
use std::hint::black_box;
use verified::group::ForkHistory;
use verified::opt::DenseId as _;

retained::define_id31! { pub struct RetainedE / StoredRetainedE, "re"; }
retained::define_id31! { pub struct RetainedK / StoredRetainedK, "rk"; }
retained::define_id31! { pub struct RetainedL / StoredRetainedL, "rl"; }
retained::define_id31! { pub struct RetainedN / StoredRetainedN, "rn"; }
verified::define_id31! { pub struct VerifiedE / StoredVerifiedE, "ve"; }
verified::define_id31! { pub struct VerifiedK / StoredVerifiedK, "vk"; }
verified::define_id31! { pub struct VerifiedL / StoredVerifiedL, "vl"; }
verified::define_id31! { pub struct VerifiedN / StoredVerifiedN, "vn"; }

type RetainedEC = retained::eclasses::EClasses<
    RetainedE,
    RetainedK,
    RetainedL,
    RetainedN,
    retained::union_find::NoJust,
    true,
    false,
>;
type VerifiedEC = ForkHistory<
    verified::eclasses::EClasses<
        VerifiedE,
        VerifiedK,
        VerifiedL,
        VerifiedN,
        verified::union_find::NoJust,
        true,
        false,
    >,
>;

const N: usize = 4096;
const FIND_PASSES: usize = 64;

/// Fresh retained aggregate with `N` singleton classes and one use each.
fn build_retained() -> (RetainedEC, Vec<RetainedE>) {
    let mut ec = RetainedEC::new();
    let mut ids = Vec::with_capacity(N);
    for i in 0..N {
        let id = <RetainedE as retained::DenseId>::from_usize(i);
        let key = ec.add_singleton(id);
        ec.add_use(key, id);
        ids.push(id);
    }
    (ec, ids)
}

/// Fresh verified aggregate with the same classes and uses.
fn build_verified() -> (VerifiedEC, Vec<VerifiedE>) {
    let mut ec = ForkHistory::new(verified::eclasses::EClasses::<
        VerifiedE,
        VerifiedK,
        VerifiedL,
        VerifiedN,
        verified::union_find::NoJust,
        true,
        false,
    >::new());
    let mut ids = Vec::with_capacity(N);
    for _ in 0..N {
        let (id, key) = ec.try_add_singleton();
        ec.add_use(key, id);
        ids.push(id);
    }
    (ec, ids)
}

fn bench_merge_cascade(c: &mut Criterion) {
    let mut g = c.benchmark_group("eclasses/merge_cascade");
    g.throughput(Throughput::Elements(N as u64));

    g.bench_function(BenchmarkId::new("retained", N), |b| {
        b.iter_batched(
            build_retained,
            |(mut ec, ids)| {
                let mut stride = 1;
                while stride < N {
                    let mut i = 0;
                    while i + stride < N {
                        if let Some(mi) = ec.merge(ids[i], ids[i + stride]) {
                            let sk = ec.repr_id(mi.survivor).unwrap();
                            let uses = ec.use_list_id(sk);
                            ec.splice_uses(uses, mi.absorbed_uses);
                        }
                        i += stride * 2;
                    }
                    stride *= 2;
                }
                black_box(ec.num_classes())
            },
            BatchSize::LargeInput,
        )
    });

    g.bench_function(BenchmarkId::new("verified", N), |b| {
        b.iter_batched(
            build_verified,
            |(mut ec, ids)| {
                let mut stride = 1;
                while stride < N {
                    let mut i = 0;
                    while i + stride < N {
                        if let Some(mi) = ec.merge(ids[i], ids[i + stride]) {
                            let sk = ec.repr_id(mi.survivor).unwrap();
                            let uses = ec.use_list_id(sk);
                            ec.splice_uses(uses, mi.absorbed_uses);
                        }
                        i += stride * 2;
                    }
                    stride *= 2;
                }
                black_box(ec.num_classes())
            },
            BatchSize::LargeInput,
        )
    });

    g.finish();
}

/// Merge schedule for the opaque cascade: the tournament pairs, generated
/// once and laundered through `black_box` so the class count and the pair
/// order are runtime values for both arms.
fn cascade_plan(n: usize) -> (usize, Vec<(u32, u32)>) {
    let mut pairs = Vec::with_capacity(n);
    let mut stride = 1;
    while stride < n {
        let mut i = 0;
        while i + stride < n {
            pairs.push((i as u32, (i + stride) as u32));
            i += stride * 2;
        }
        stride *= 2;
    }
    black_box((n, pairs))
}

fn bench_merge_cascade_opaque(c: &mut Criterion) {
    let mut g = c.benchmark_group("eclasses/merge_cascade_opaque");
    let (n, pairs) = cascade_plan(N);
    g.throughput(Throughput::Elements(n as u64));

    g.bench_function(BenchmarkId::new("retained", n), |b| {
        b.iter_batched(
            build_retained,
            |(mut ec, ids)| {
                for &(x, y) in &pairs {
                    if let Some(mi) = ec.merge(ids[x as usize], ids[y as usize]) {
                        let sk = ec.repr_id(mi.survivor).unwrap();
                        let uses = ec.use_list_id(sk);
                        ec.splice_uses(uses, mi.absorbed_uses);
                    }
                }
                black_box(ec.num_classes())
            },
            BatchSize::LargeInput,
        )
    });

    g.bench_function(BenchmarkId::new("verified", n), |b| {
        b.iter_batched(
            build_verified,
            |(mut ec, ids)| {
                for &(x, y) in &pairs {
                    if let Some(mi) = ec.merge(ids[x as usize], ids[y as usize]) {
                        let sk = ec.repr_id(mi.survivor).unwrap();
                        let uses = ec.use_list_id(sk);
                        ec.splice_uses(uses, mi.absorbed_uses);
                    }
                }
                black_box(ec.num_classes())
            },
            BatchSize::LargeInput,
        )
    });

    g.finish();
}

/// Min-monomial rows: `set_min_width` once, then every class gets a full row
/// written column by column (chapter 20 second pass, `set_min_monomial`).
fn bench_set_min_monomial(c: &mut Criterion) {
    const W: usize = 8;
    let mut g = c.benchmark_group("eclasses/set_min_monomial");
    g.throughput(Throughput::Elements((N * W) as u64));

    g.bench_function(BenchmarkId::new("retained", N), |b| {
        b.iter_batched(
            || {
                let (mut ec, ids) = build_retained();
                ec.set_min_width(W);
                (ec, ids)
            },
            |(mut ec, ids)| {
                for &id in &ids {
                    let key = ec.repr_id(id).unwrap();
                    for col in 0..W {
                        ec.set_min_monomial(key, col, id);
                    }
                }
                black_box(ec.num_classes())
            },
            BatchSize::LargeInput,
        )
    });

    g.bench_function(BenchmarkId::new("verified", N), |b| {
        b.iter_batched(
            || {
                let (mut ec, ids) = build_verified();
                ec.set_min_width(W);
                (ec, ids)
            },
            |(mut ec, ids)| {
                for &id in &ids {
                    let key = ec.repr_id(id).unwrap();
                    for col in 0..W {
                        ec.set_min_monomial(key, col, id);
                    }
                }
                black_box(ec.num_classes())
            },
            BatchSize::LargeInput,
        )
    });

    g.finish();
}

type RetainedProofUf = retained::union_find::UnionFind<RetainedE, u8, true, true>;
type VerifiedProofUf = ForkHistory<verified::union_find::UnionFind<VerifiedE, u8, true, true>>;

/// `explain` across a deep chain: N sets unioned into one path, then the two
/// ends explained (chapter 20 item 4, the repeated `find_const` traversals).
fn bench_union_find_explain_deep_chain(c: &mut Criterion) {
    let mut r = RetainedProofUf::new();
    let mut v = VerifiedProofUf::new(verified::union_find::UnionFind::new());
    for i in 0..N {
        r.make_set(<RetainedE as retained::DenseId>::from_usize(i));
        v.make_set(VerifiedE::from_usize(i));
    }
    for i in 0..N - 1 {
        r.union_justified(
            <RetainedE as retained::DenseId>::from_usize(i),
            <RetainedE as retained::DenseId>::from_usize(i + 1),
            (i % 251) as u8,
        );
        v.union_justified(
            VerifiedE::from_usize(i),
            VerifiedE::from_usize(i + 1),
            (i % 251) as u8,
        );
    }
    let mut g = c.benchmark_group("union_find/explain_deep_chain");
    g.bench_function(BenchmarkId::new("retained", N), |b| {
        let mut buf = retained::union_find::ProofBuf::new();
        b.iter(|| {
            buf.clear();
            let ok = r.explain(
                <RetainedE as retained::DenseId>::from_usize(0),
                <RetainedE as retained::DenseId>::from_usize(N - 1),
                &mut buf,
            );
            black_box((ok, buf.steps.len()))
        })
    });
    g.bench_function(BenchmarkId::new("verified", N), |b| {
        let mut buf = verified::union_find::ProofBuf::new();
        b.iter(|| {
            buf.clear();
            let ok = v.explain(
                VerifiedE::from_usize(0),
                VerifiedE::from_usize(N - 1),
                &mut buf,
            );
            black_box((ok, buf.steps.len()))
        })
    });
    g.finish();
}

fn merged_retained() -> (RetainedEC, Vec<RetainedE>) {
    let (mut ec, ids) = build_retained();
    for i in 1..N {
        ec.merge(ids[0], ids[i]);
    }
    (ec, ids)
}

fn merged_verified() -> (VerifiedEC, Vec<VerifiedE>) {
    let (mut ec, ids) = build_verified();
    for i in 1..N {
        ec.merge(ids[0], ids[i]);
    }
    (ec, ids)
}

fn bench_find_sweep(c: &mut Criterion) {
    let mut g = c.benchmark_group("eclasses/find_sweep");
    g.throughput(Throughput::Elements((N * FIND_PASSES) as u64));

    g.bench_function(BenchmarkId::new("retained", N), |b| {
        let (ec, ids) = merged_retained();
        b.iter(|| {
            // Accumulate without a per-element `black_box`: that forced a
            // store/reload of `acc` on every find, whose address aliasing
            // with the arrays made the loop bimodal across processes.
            let mut acc = 0usize;
            for _ in 0..FIND_PASSES {
                for &id in &ids {
                    acc ^= retained::DenseId::to_usize(ec.find_const(id));
                }
            }
            black_box(acc)
        })
    });

    g.bench_function(BenchmarkId::new("verified", N), |b| {
        let (ec, ids) = merged_verified();
        b.iter(|| {
            let mut acc = 0usize;
            for _ in 0..FIND_PASSES {
                for &id in &ids {
                    acc ^= verified::DenseId::to_usize(ec.find_const(id));
                }
            }
            black_box(acc)
        })
    });

    g.finish();
}

fn bench_mark_merge_restore(c: &mut Criterion) {
    let mut g = c.benchmark_group("eclasses/mark_merge_restore");
    g.throughput(Throughput::Elements(255));

    g.bench_function(BenchmarkId::new("retained", N), |b| {
        b.iter_batched(
            build_retained,
            |(mut ec, ids)| {
                let tok = ec.mark(retained::ShrinkPolicy::Never);
                for i in 1..256 {
                    ec.merge(ids[0], ids[i]);
                }
                ec.restore(tok);
                black_box(ec.num_classes())
            },
            BatchSize::LargeInput,
        )
    });

    g.bench_function(BenchmarkId::new("verified", N), |b| {
        b.iter_batched(
            build_verified,
            |(mut ec, ids)| {
                let tok = ec
                    .mark(verified::ShrinkPolicy::Never)
                    .expect("mark: bounded depth");
                for i in 1..256 {
                    ec.merge(ids[0], ids[i]);
                }
                // Legacy restore == verified restore_and_pop (restore + pop_scope fused; design doc 08 §1).
                assert!(ec.restore_and_pop(tok), "own token");
                black_box(ec.num_classes())
            },
            BatchSize::LargeInput,
        )
    });

    g.finish();
}

criterion_group!(
    benches,
    bench_merge_cascade,
    bench_merge_cascade_opaque,
    bench_set_min_monomial,
    bench_union_find_explain_deep_chain,
    bench_find_sweep,
    bench_mark_merge_restore,
);
criterion_main!(benches);
