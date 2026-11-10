//! Knobs this repository's own tests and benchmarks need, and nothing else.
//!
//! None of this is public API. It exists only when the crate is built for
//! its own test suite or with the non-default `internal` feature, it is
//! hidden from the documentation, and it carries no compatibility promise.
//! The supported surface is the one `std::collections::BTreeMap` has.

use crate::layout::{BranchLayout, LeafLayout};
use crate::BPlusTreeMap;

impl<K: Ord + Clone, V> BPlusTreeMap<K, V> {
    /// An empty map whose leaves and branches each hold `capacity` entries.
    ///
    /// Small capacities make splits, merges and borrows happen after a
    /// handful of operations, which is how the tests reach those paths.
    /// `with_capacities` and `with_payload_targets`, the other two knobs,
    /// are defined beside `new` in `lib.rs`.
    #[doc(hidden)]
    pub fn with_capacity(capacity: usize) -> Self {
        Self::with_capacities(capacity, capacity)
    }

    /// The computed layout of this map's leaf nodes.
    #[doc(hidden)]
    pub fn leaf_layout(&self) -> &LeafLayout {
        &self.leaf_layout
    }

    /// The computed layout of this map's branch nodes.
    #[doc(hidden)]
    pub fn branch_layout(&self) -> &BranchLayout {
        &self.branch_layout
    }
}
