// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Proves the SEMPER_COMPRESS=auto lever ACTIVATES (not merely that runs under it
//! stay green): a default-constructed ParallelStore-backed vec becomes the
//! per-frame-adaptive representation (marks observably seal cold frames), and its
//! restore matches an uncompressed oracle. Own test file = own process, so the
//! in-process set_var lands before the lever's OnceLock caches.

use semi_persistent_containers_verus as verus;
use verus::vec::ShrinkPolicy;

type V = verus::Vec<u32, u32, verus::parallel_store::ParallelStore<u32, u32>, true>;

#[test]
fn env_auto_activates_and_matches_oracle() {
    // Single-threaded test binary (one test), set before any construction.
    unsafe { std::env::set_var("SEMPER_COMPRESS", "auto") };

    const N: u32 = 500;
    let mut v = V::new(); // default constructor: the lever's target
    let mut oracle = V::new_with_mode(verus::diff_compress::CompressionMode::None);
    for _ in 0..N {
        v.try_push(0).unwrap();
        oracle.try_push(0).unwrap();
    }
    let t0 = v.try_mark(ShrinkPolicy::Never).unwrap();
    let o0 = oracle.try_mark(ShrinkPolicy::Never).unwrap();
    for i in 0..N {
        v.set_index(i, i + 1);
        oracle.set_index(i, i + 1);
    }
    let bytes_before = v.tracking_bytes();
    let _t1 = v.try_mark(ShrinkPolicy::Never).unwrap();
    let _o1 = oracle.try_mark(ShrinkPolicy::Never).unwrap();
    let bytes_after = v.tracking_bytes();
    let _ = bytes_before;

    // ACTIVATION: the second mark sealed the (contiguous, distinct-valued) frame
    // into a run cold frame, so the compressed log is SMALLER than the oracle's
    // plain log for the same captures. Without activation the two logs are
    // byte-identical in shape and this strict inequality fails.
    let plain_bytes = oracle.tracking_bytes();
    assert!(
        bytes_after < plain_bytes,
        "lever did not activate: compressed {bytes_after} !< plain {plain_bytes}"
    );

    for i in 0..N {
        v.set_index(i, i * 2);
        oracle.set_index(i, i * 2);
    }
    v.try_restore(t0).unwrap();
    oracle.try_restore(o0).unwrap();
    let a: Vec<u32> = (0..N).map(|i| v.get_index(i)).collect();
    let b: Vec<u32> = (0..N).map(|i| oracle.get_index(i)).collect();
    assert_eq!(a, b, "compressed restore diverged from the oracle");
}
