// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Two-stack diff-log benches, shaped like the saturation loop: frequent marks,
//! a few writes per mark, with compression activated on mark. Measures the mark
//! path (including the triggered flushes) under a compressing config against a
//! non-compressing one, and prints the resulting hot/cold stack footprints so the
//! space effect is visible next to the time.
//!
//! The value dictionary is a known space loss at the current code width (see
//! diff_compress_bench and doc 09), so the ValueDict run is expected to move
//! frames into the cold stack and cost encode time without yet saving bytes; the
//! bench exists to exercise the activate-on-mark mechanism end to end and to be
//! the harness that measures the win once codes are narrowed and IndexRuns lands.

use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};
use std::hint::black_box;

use semi_persistent_containers_verus as verus;
use verus::{ColumnConfig, TwoStackLog};

const MARKS: usize = 400;
const WRITES_PER_MARK: usize = 16;

struct XorShift(u64);
impl XorShift {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }
}

// One saturation-shaped run: WRITES_PER_MARK pushes then a mark, MARKS times.
// `distinct` bounds the value alphabet (union-find representatives), so the
// ValueDict frames dedup. Returns (hot_bytes, cold_bytes) at the end.
fn run(config: ColumnConfig, base_bytes: usize, distinct: u32) -> (usize, usize) {
    let mut ts: TwoStackLog<u32, u32> = TwoStackLog::new(config);
    let mut rng = XorShift(0x2545F491);
    let mut cell: u32 = 0;
    for _ in 0..MARKS {
        for _ in 0..WRITES_PER_MARK {
            let v = (rng.next() % distinct as u64) as u32;
            ts.push(v, cell);
            cell = cell.wrapping_add(1) & 0x000F_FFFF;
        }
        let hb = ts.hot_bytes();
        ts.mark(hb, base_bytes);
    }
    (ts.hot_bytes(), ts.cold_bytes())
}

fn bench_two_stack(c: &mut Criterion) {
    // base payload size the size-fraction trigger compares against.
    let base_bytes = 1 << 20; // 1 MiB "live e-graph"
    let distinct = 256u32;

    let none = ColumnConfig::none();
    // Flush when the uncompressed top reaches 5% of the live payload, keeping
    // the 4 most-recent frames hot (LRU floor).
    let dict = ColumnConfig::value_dict(5, 4);

    // Report the final footprints once (space is deterministic given the seed).
    report_footprints(base_bytes, distinct, none, dict);

    let mut g = c.benchmark_group("two_stack/mark_churn");
    g.bench_with_input(BenchmarkId::new("none", "nocompress"), &none, |b, &cfg| {
        b.iter(|| black_box(run(cfg, base_bytes, distinct)))
    });
    g.bench_with_input(BenchmarkId::new("valuedict", "compress_5pct_hot4"), &dict, |b, &cfg| {
        b.iter(|| black_box(run(cfg, base_bytes, distinct)))
    });
    g.finish();
}

fn report_footprints(base_bytes: usize, distinct: u32, none: ColumnConfig, dict: ColumnConfig) {
    use std::sync::atomic::{AtomicBool, Ordering};
    static DONE: AtomicBool = AtomicBool::new(false);
    if DONE.swap(true, Ordering::Relaxed) {
        return;
    }
    let (nh, nc) = run(none, base_bytes, distinct);
    let (dh, dc) = run(dict, base_bytes, distinct);
    eprintln!(
        "\n=== two-stack footprint after {} marks x {} writes (distinct={}) ===",
        MARKS, WRITES_PER_MARK, distinct
    );
    eprintln!("  {:>12} {:>12} {:>12} {:>12}", "config", "hot_bytes", "cold_bytes", "total");
    eprintln!("  {:>12} {:>12} {:>12} {:>12}", "none", nh, nc, nh + nc);
    eprintln!("  {:>12} {:>12} {:>12} {:>12}", "valuedict", dh, dc, dh + dc);
    eprintln!(
        "  (value-dict total / none total: {:.2}x — <1.0 once codes are narrowed)\n",
        (dh + dc) as f64 / (nh + nc).max(1) as f64
    );
}

criterion_group!(benches, bench_two_stack);
criterion_main!(benches);
