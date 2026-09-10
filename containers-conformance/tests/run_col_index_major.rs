// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Conformance for the verified index-major run column `RunCol` (the A2
//! encoder that drops the index column and reconstructs each index via
//! `IndexLike::checked_add`, carrying a ghost of the write pairs tied to the runs
//! by `as_nat`). Unlike `RunFrame::decode_exec_i`, `RunCol::decode_exec` is NOT
//! `external_body`: `decode_exec() == decode() == the input pairs` is proved in
//! `containers-verus` with no `IndexFromNat`, so it works for opaque id index
//! types. This test backs two things the proofs do not run under `cargo test`:
//!   - the exec round-trip: `single_run(diffs).decode_exec() == diffs` exactly,
//!   - the heap claim: the encoded `byte_len()` is below a plain `Vec<(T, I)>`
//!     (`len * (size_of::<T>() + size_of::<I>())`) for a contiguous frame,
//!     because the index column is dropped down to one `start`.

use proptest::prelude::*;
use semi_persistent_containers_verus as verus;
use verus::diff_compress::RunCol;

/// Reference restore: apply `(value, index)` pairs to a base column in order,
/// last write wins. The oracle `restore_runs_into`'s memcpy must reproduce.
fn apply_pairs(base: &[u32], pairs: &[(u32, u32)]) -> Vec<u32> {
    let mut col = base.to_vec();
    for &(v, i) in pairs {
        col[i as usize] = v;
    }
    col
}

/// A contiguous frame: values arbitrary, indices `start, start+1, ...`.
fn contiguous(start: u32, vals: &[u32]) -> Vec<(u32, u32)> {
    vals.iter()
        .enumerate()
        .map(|(k, &v)| (v, start + k as u32))
        .collect()
}

fn plain_byte_len(n: usize) -> usize {
    n * (core::mem::size_of::<u32>() + core::mem::size_of::<u32>())
}

proptest! {
    #![proptest_config(ProptestConfig { cases: 2000, ..ProptestConfig::default() })]

    #[test]
    fn single_run_roundtrips_and_compresses(
        start in 0u32..1_000_000u32,
        vals in prop::collection::vec(any::<u32>(), 1..300usize),
    ) {
        let diffs = contiguous(start, &vals);

        let col: RunCol<u32, u32> = RunCol::single_run(&diffs);

        // Exact round-trip: decode reproduces every (value, index) pair.
        let decoded = col.decode_exec();
        prop_assert_eq!(decoded.len(), diffs.len());
        for (got, want) in decoded.iter().zip(diffs.iter()) {
            prop_assert_eq!(got.0, want.0);
            prop_assert_eq!(got.1, want.1);
        }

        // Heap claim: index column dropped to one start ⇒ strictly below plain,
        // for any frame of two or more entries.
        if diffs.len() >= 2 {
            prop_assert!(
                col.byte_len() < plain_byte_len(diffs.len()),
                "encoded {} not below plain {} (n={})",
                col.byte_len(), plain_byte_len(diffs.len()), diffs.len(),
            );
        }
    }
}

proptest! {
    #![proptest_config(ProptestConfig { cases: 2000, ..ProptestConfig::default() })]

    // General write-order coalescing: arbitrary (value, index) streams over a
    // bounded index space, so runs both coalesce (ascending contiguous captures)
    // and fall back to singletons (scattered/descending). compress must round-trip
    // exactly, and the memcpy restore must match the pair-by-pair overlay.
    #[test]
    fn compress_roundtrips_and_restore_matches_overlay(
        diffs in prop::collection::vec((any::<u32>(), 0u32..64u32), 0..200usize),
    ) {
        // (value, index) pairs for the encoder.
        let input: Vec<(u32, u32)> = diffs.clone();

        let col: RunCol<u32, u32> = RunCol::compress(&input);

        // Exact round-trip via the verified decode.
        let decoded = col.decode_exec();
        prop_assert_eq!(decoded.len(), input.len());
        for (got, want) in decoded.iter().zip(input.iter()) {
            prop_assert_eq!(got.0, want.0);
            prop_assert_eq!(got.1, want.1);
        }

        // Random access matches the whole decode at every position.
        for i in 0..decoded.len() {
            prop_assert_eq!(col.decode_at(i), decoded[i]);
        }

        // memcpy restore == pair-by-pair overlay (both onto the same base column).
        let base = vec![0u32; 64];
        let mut memcpy_col = base.clone();
        col.restore_runs_into(&mut memcpy_col);
        let overlay_col = apply_pairs(&base, &decoded);
        prop_assert_eq!(memcpy_col, overlay_col);
    }
}

#[test]
fn single_run_boundaries() {
    // One entry: byte_len == start index + one value; round-trip holds.
    let d = contiguous(7, &[42]);
    let col: RunCol<u32, u32> = RunCol::single_run(&d);
    let got = col.decode_exec();
    assert_eq!(got, vec![(42u32, 7u32)]);

    // A long contiguous run near a high start still reconstructs each index.
    let vals: Vec<u32> = (0..256).map(|k| k * 3).collect();
    let d = contiguous(1_000, &vals);
    let col: RunCol<u32, u32> = RunCol::single_run(&d);
    let got = col.decode_exec();
    assert_eq!(got, d);
    assert!(col.byte_len() < plain_byte_len(d.len()));
}
