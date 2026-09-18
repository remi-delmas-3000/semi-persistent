// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Session-level bare-pair memo for the exact solver.
//!
//! One entry per class pair `(l, r)`: the term and support of the first
//! context-clean solve, exactly the payload of the exact solver's in-call
//! `SubsumptionState::by_pair`. Promoted to a session container so
//! consecutive hybrid calls (`hybrid_exact`, `rollout_hybrid`) reuse each
//! other's clean solves instead of re-solving overlapping subgraphs; the
//! reuse rule is unchanged: a clean entry re-executes under any entry
//! context disjoint from its support, and the re-execution is the identical
//! derivation, so reuse is equality. Entries are valid for one snapshot and
//! one cycle mode, which is the session's own scope.
//!
//! Semi-persistence follows the interning-log pattern (design chapter 3's
//! derived-index section): the append-only log is the source of truth, the
//! hash index is derived, and `restore` validates the log token BEFORE
//! removing the truncated suffix's keys from the index, reading them from
//! the log while it is still live. Terms reference the session term pool;
//! the session restores the pool with its own token in the same bundle, so
//! a rolled-back entry never outlives the term it points to.

use std::collections::HashMap;

use crate::containers::error::ContainerError;
use crate::containers::group::Member;
use crate::containers::{AppendOnlyVec, IndexLike, ShrinkPolicy};

/// One memoized clean solve. Supports are sorted and deduplicated at
/// publication (the exact solver sorts before it writes).
struct MemoEntry<T, C> {
    key: (u64, u64),
    term: T,
    support_l: Vec<C>,
    support_r: Vec<C>,
}

/// The session memo. `T` is the term id type, `C` the class id type, `I` the
/// session index word.
pub struct ExactMemo<T: Copy, C: Copy + Ord, I: IndexLike = usize> {
    log: AppendOnlyVec<MemoEntry<T, C>, I>,
    /// Derived: class-pair key -> log position of its (unique) entry.
    index: HashMap<(u64, u64), usize>,
    /// The log length at each open frame, oldest first: what the token used to
    /// carry. The index is not semi-persistent, so a move to frame `d` has to
    /// know where that frame started to drop exactly the keys above it.
    frame_lens: Vec<usize>,
}

impl<T: Copy, C: Copy + Ord, I: IndexLike> ExactMemo<T, C, I> {
    pub fn new() -> Self {
        ExactMemo {
            log: AppendOnlyVec::new(),
            index: HashMap::new(),
            frame_lens: Vec::new(),
        }
    }

    pub fn len(&self) -> usize {
        self.log.len().as_usize()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// The clean entry for `(l, r)`, if one was recorded: its term and its
    /// per-side support (sorted, deduplicated).
    pub fn get(&self, l: u64, r: u64) -> Option<(T, &[C], &[C])> {
        let &pos = self.index.get(&(l, r))?;
        let entry = self
            .log
            .get(I::try_from_usize(pos).expect("index within log length"));
        Some((entry.term, &entry.support_l, &entry.support_r))
    }

    /// Record the first clean solve of `(l, r)`; later writers lose, matching
    /// the in-call memo's `or_insert`.
    pub fn insert_if_absent(
        &mut self,
        l: u64,
        r: u64,
        term: T,
        support_l: Vec<C>,
        support_r: Vec<C>,
    ) -> Result<(), ContainerError> {
        if self.index.contains_key(&(l, r)) {
            return Ok(());
        }
        let pos = self.log.len().as_usize();
        self.log.try_push(MemoEntry {
            key: (l, r),
            term,
            support_l,
            support_r,
        })?;
        self.index.insert((l, r), pos);
        Ok(())
    }

    // Structural frame operations: the typed-group member protocol (design doc
    // 10). No tokens — the session's `History` is the only token authority. The
    // derived index is maintained here, which is what the token's saved length
    // used to pay for.
    pub fn push_frame(&mut self, shrink: ShrinkPolicy) {
        self.frame_lens.push(self.len());
        Member::push_frame(&mut self.log, shrink);
    }

    /// Drop the index keys of every entry above frame `depth`, reading them from
    /// the log while it is still live, then move the log.
    fn unindex_above(&mut self, depth: usize) {
        let saved_len = self.frame_lens[depth];
        for pos in saved_len..self.len() {
            let entry = self
                .log
                .get(I::try_from_usize(pos).expect("position within log length"));
            let key = entry.key;
            self.index.remove(&key);
        }
    }

    pub fn reset_frame(&mut self, depth: usize) {
        self.unindex_above(depth);
        Member::reset_frame(&mut self.log, depth);
        self.frame_lens.truncate(depth + 1);
    }

    pub fn restore_frame(&mut self, depth: usize) {
        self.unindex_above(depth);
        Member::restore_frame(&mut self.log, depth);
        self.frame_lens.truncate(depth);
    }

    /// The scope pop keeps the state and drops the checkpoint, so the index is
    /// already correct for what stays live.
    pub fn pop_frame(&mut self) {
        Member::pop_frame(&mut self.log);
        self.frame_lens.pop();
    }

    pub fn frame_depth(&self) -> usize {
        Member::depth_exec(&self.log)
    }
}

impl<T: Copy, C: Copy + Ord, I: IndexLike> Default for ExactMemo<T, C, I> {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    type Memo = ExactMemo<u32, u16>;

    #[test]
    fn first_writer_wins() {
        let mut m = Memo::new();
        m.insert_if_absent(1, 2, 10, vec![3u16], vec![4u16])
            .unwrap();
        m.insert_if_absent(1, 2, 99, vec![], vec![]).unwrap();
        let (t, sl, sr) = m.get(1, 2).unwrap();
        assert_eq!((t, sl, sr), (10, &[3u16][..], &[4u16][..]));
        assert!(m.get(2, 1).is_none());
    }

    #[test]
    fn mark_restore_truncates_and_unindexes() {
        let mut m = Memo::new();
        m.insert_if_absent(1, 2, 10, vec![], vec![]).unwrap();
        let token = m.frame_depth();
        m.push_frame(ShrinkPolicy::Never);
        m.insert_if_absent(3, 4, 20, vec![], vec![]).unwrap();
        assert_eq!(m.len(), 2);

        m.reset_frame(token);
        assert_eq!(m.len(), 1);
        assert!(m.get(1, 2).is_some());
        assert!(m.get(3, 4).is_none());

        // A re-insert after the rollback lands at the recycled position.
        m.insert_if_absent(3, 4, 21, vec![], vec![]).unwrap();
        assert_eq!(m.get(3, 4).unwrap().0, 21);
    }

    #[test]
    fn nested_marks() {
        let mut m = Memo::new();
        let outer = m.frame_depth();
        m.push_frame(ShrinkPolicy::Never);
        m.insert_if_absent(1, 1, 1, vec![], vec![]).unwrap();
        let inner = m.frame_depth();
        m.push_frame(ShrinkPolicy::Never);
        m.insert_if_absent(2, 2, 2, vec![], vec![]).unwrap();
        m.reset_frame(inner);
        assert!(m.get(1, 1).is_some() && m.get(2, 2).is_none());
        m.reset_frame(outer);
        assert!(m.get(1, 1).is_none());
        assert!(m.is_empty());
    }
}
