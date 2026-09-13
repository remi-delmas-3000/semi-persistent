// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Trail-column compression at eviction (design doc §7, deliverable 5).
//!
//! A trail column appends EVERY write, duplicates included, so before the
//! dedupe-first eviction converter it never compressed at all. This test
//! drives a `VecT` past the HOT_BUFFER with heavily duplicated per-frame
//! writes and checks two things: the diff log SHRANK below the append count
//! (dedupe-first dropped the later duplicates at eviction), and every
//! restore still reproduces its snapshot exactly (the chronologically first
//! capture per cell is the one reconstruction needs; later duplicates are
//! inert under overlay's first-entry-wins order).

use semi_persistent_containers_verus as verus;
use verus::VecT;
use verus::vec::ShrinkPolicy;

const LEN: usize = 64;
const FRAMES: usize = 14; // HOT_BUFFER is 8; evictions fire from mark 10 on.
const REPS: usize = 4; // duplicate factor per index per frame

#[test]
fn trail_column_compresses_at_eviction_and_restores() {
    let mut v: VecT<u64, u32> = VecT::new();
    for i in 0..LEN {
        v.try_push(i as u64).expect("push");
    }

    let mut tokens = Vec::new();
    let mut models: Vec<Vec<u64>> = Vec::new();
    let mut model: Vec<u64> = (0..LEN as u64).collect();
    let mut total_writes: usize = 0;

    let mut seed: u64 = 0x9E3779B97F4A7C15;
    for _frame in 0..FRAMES {
        models.push(model.clone());
        tokens.push(v.try_mark(ShrinkPolicy::Never).expect("mark"));
        // Duplicated writes: 32 writes over 4 cells per frame, values
        // changing every write. The trail appends all of them; only the
        // FIRST capture per cell per frame matters for restore, and the
        // eviction converter must drop the other 28. (An earlier draft drew
        // indices from an LCG's low 6 bits - a full-period generator, so
        // every frame was accidentally duplicate-FREE and nothing could
        // compress; deterministic duplicates keep the test honest.)
        for _rep in 0..REPS {
            for j in 0..8u32 {
                seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
                let idx = j % 4;
                let val = seed ^ (j as u64);
                v.set_index(idx, val);
                model[idx as usize] = val;
                total_writes += 1;
            }
        }
    }

    // Compression: every write was appended, and eviction's dedupe-first
    // dropped the within-frame duplicates, so the log is strictly shorter
    // than the append count. (Each evicted frame wrote 32 entries over at
    // most 32 distinct cells with random collisions, so drops are certain
    // across 14 frames.)
    assert!(
        v.diff_log_len() < total_writes,
        "trail log did not compress: len {} vs {} writes appended",
        v.diff_log_len(),
        total_writes
    );

    // Correctness: unwind every frame, newest first, and compare all cells
    // with the model snapshot taken at its mark.
    while let Some(tok) = tokens.pop() {
        let want = models.pop().expect("model");
        v.try_restore(tok).expect("restore");
        for (i, w) in want.iter().enumerate() {
            assert_eq!(v.get_index(i as u32), *w, "cell {i} diverged after restore");
        }
    }
}
