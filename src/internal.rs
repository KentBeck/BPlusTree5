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
    #[doc(hidden)]
    pub fn with_capacity(capacity: usize) -> Self {
        Self::with_capacities_impl(capacity, capacity)
    }

    /// An empty map with independent leaf and branch capacities.
    #[doc(hidden)]
    pub fn with_capacities(leaf_cap: usize, branch_cap: usize) -> Self {
        Self::with_capacities_impl(leaf_cap, branch_cap)
    }

    /// An empty map whose capacities come from per-node byte budgets.
    #[doc(hidden)]
    pub fn with_payload_targets(leaf_payload_bytes: usize, branch_payload_bytes: usize) -> Self {
        Self::with_payload_targets_impl(leaf_payload_bytes, branch_payload_bytes)
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
