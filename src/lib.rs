//! A B+ tree map with the API of [`std::collections::BTreeMap`].
//!
//! [`BPlusTreeMap`] stores its entries in fixed-size leaf and branch nodes,
//! each a single raw allocation, with the leaves linked into a doubly
//! linked chain. The public surface is the standard library's: the same
//! method names, signatures, iterator types, and trait impls, so a project
//! can swap `std::collections::BTreeMap` for this type and keep compiling.
//!
//! Three deliberate differences:
//!
//! * `K: Clone` is required wherever std asks only for `K: Ord`, because a
//!   split copies a key up into a branch separator.
//! * Node capacities are chosen for `K` and `V` by [`BPlusTreeMap::new`]
//!   and cannot be set through the public API.
//! * [`BPlusTreeMap::new`] is not a `const fn`, so a map cannot be built in
//!   a constant. It allocates nothing until the first insert either way.
//!
//! Methods the standard library still has behind a nightly feature gate
//! (`extract_if`, `try_insert`, the cursor API, the allocator parameter)
//! are not implemented.
//!
//! [`std::collections::BTreeMap`]: https://doc.rust-lang.org/std/collections/struct.BTreeMap.html

#![no_std]

extern crate alloc;

use core::marker::PhantomData;
use core::ptr::{self, NonNull};

mod bulk;
mod common;
mod delete;
mod entry;
mod get;
mod insert;
#[cfg(any(test, feature = "internal"))]
mod internal;
mod iterate;
mod layout;
mod node_alloc;
mod owned;
mod serde_impls;
mod set;
mod traits;

#[cfg(not(any(test, feature = "internal")))]
use layout::{BranchLayout, LeafLayout, NodeHdr, NodeTag};
use node_alloc::{free_branch_block, free_leaf_block};

#[cfg(feature = "delete_profile")]
pub use delete::DeleteProfile;
pub use entry::{Entry, OccupiedEntry, VacantEntry};
pub use iterate::{Iter, IterMut, Keys, Range, RangeMut, Values, ValuesMut};
pub use owned::{IntoIter, IntoKeys, IntoValues};
pub use set::BPlusTreeSet;

/// Node internals, for this repository's own tests and benchmarks. Not
/// public API; see [`internal`](crate::internal).
#[cfg(any(test, feature = "internal"))]
#[doc(hidden)]
pub use common::ShapeHasher;
#[cfg(any(test, feature = "internal"))]
#[doc(hidden)]
pub use layout::{align_up, BranchLayout, LeafLayout, NodeHdr, NodeTag};

#[cfg(any(test, feature = "internal"))]
#[doc(hidden)]
pub const RECOMMENDED_LEAF_PAYLOAD_BYTES_INTERNAL: usize = RECOMMENDED_LEAF_PAYLOAD_BYTES;
#[cfg(any(test, feature = "internal"))]
#[doc(hidden)]
pub const RECOMMENDED_BRANCH_PAYLOAD_BYTES_INTERNAL: usize = RECOMMENDED_BRANCH_PAYLOAD_BYTES;

/// Leaf key/value bytes targeted by [`BPlusTreeMap::new`].
const RECOMMENDED_LEAF_PAYLOAD_BYTES: usize = 512;

/// Branch key/child-pointer bytes targeted by [`BPlusTreeMap::new`].
const RECOMMENDED_BRANCH_PAYLOAD_BYTES: usize = 4 * 1024;

const MIN_NODE_CAPACITY: usize = 4;

/// Convert a payload target into a valid node capacity. Zero-sized slots can
/// fill the payload without consuming bytes, so they use the format's largest
/// representable capacity.
fn capacity_for_payload(target_bytes: usize, bytes_per_slot: usize) -> usize {
    if bytes_per_slot == 0 {
        u16::MAX as usize
    } else {
        (target_bytes / bytes_per_slot).clamp(MIN_NODE_CAPACITY, u16::MAX as usize)
    }
}

/// An ordered map, stored as a B+ tree.
///
/// See the [crate documentation](crate) for how this differs from
/// [`std::collections::BTreeMap`].
pub struct BPlusTreeMap<K, V> {
    /// Root node (points to a node header at offset 0), or None if empty.
    root: Option<NonNull<u8>>,

    /// Number of key/value pairs stored in the leaves.
    entry_count: usize,

    #[cfg(feature = "delete_profile")]
    delete_profile: DeleteProfile,

    /// Fixed per-kind layouts computed from byte budgets and K/V sizes.
    leaf_layout: LeafLayout,
    branch_layout: BranchLayout,

    _marker: PhantomData<(K, V)>,
}

// The map owns its nodes outright; the raw pointers are never shared with
// anything outside the map, so it is exactly as thread-safe as its contents.
unsafe impl<K: Send, V: Send> Send for BPlusTreeMap<K, V> {}
unsafe impl<K: Sync, V: Sync> Sync for BPlusTreeMap<K, V> {}

impl<K, V> Drop for BPlusTreeMap<K, V> {
    fn drop(&mut self) {
        if let Some(root) = self.root.take() {
            unsafe {
                self.drop_subtree(root);
            }
        }
    }
}

impl<K, V> BPlusTreeMap<K, V> {
    /// Drop every key and value the subtree owns, then free its nodes.
    /// Used by `Drop` and `clear`, which own the whole tree; the incremental
    /// paths in `delete` instead free nodes whose contents have already moved
    /// elsewhere (see `free_emptied_leaf` / `free_emptied_branch`).
    /// Lean: `dropSubtreeH_spec` (`Proofs/HeapLedger.lean`): frees exactly the
    /// subtree's nodes, each once, so each slot's contents drop exactly once.
    unsafe fn drop_subtree(&mut self, node: NonNull<u8>) {
        let hdr = &*(node.as_ptr() as *const NodeHdr);
        match hdr.tag {
            NodeTag::Leaf => self.drop_leaf(node),
            NodeTag::Branch => self.drop_branch(node),
        }
    }

    unsafe fn drop_leaf(&mut self, node: NonNull<u8>) {
        let parts = layout::carve_leaf::<K, V>(node, &self.leaf_layout);
        let len = (*parts.hdr).len as usize;
        ptr::drop_in_place(ptr::slice_from_raw_parts_mut(parts.keys_ptr as *mut K, len));
        ptr::drop_in_place(ptr::slice_from_raw_parts_mut(parts.vals_ptr as *mut V, len));
        free_leaf_block(node, &self.leaf_layout);
    }

    /// Children go first so their nodes are gone before the separators
    /// that ordered them.
    unsafe fn drop_branch(&mut self, node: NonNull<u8>) {
        let parts = layout::carve_branch::<K>(node, &self.branch_layout);
        let len = (*parts.hdr).len as usize;
        let children = core::slice::from_raw_parts(parts.children_ptr as *const *mut u8, len + 1);
        for child in children.iter().filter_map(|&p| NonNull::new(p)) {
            self.drop_subtree(child);
        }
        ptr::drop_in_place(ptr::slice_from_raw_parts_mut(parts.keys_ptr as *mut K, len));
        free_branch_block(node, &self.branch_layout);
    }
}

impl<K: Ord + Clone, V> BPlusTreeMap<K, V> {
    /// An empty map.
    ///
    /// Node capacities are derived from the sizes of `K` and `V`: a leaf
    /// targets 512 bytes of keys and values, a branch 4 KiB of keys and
    /// child pointers. Nothing is allocated until the first insert.
    pub fn new() -> Self {
        Self::with_payload_targets_impl(
            RECOMMENDED_LEAF_PAYLOAD_BYTES,
            RECOMMENDED_BRANCH_PAYLOAD_BYTES,
        )
    }

    /// Construct from desired payload bytes rather than entry counts.
    ///
    /// A leaf slot is one `K` plus one `V`; a branch slot is one `K` plus one
    /// child pointer. Node headers, sibling links, one extra branch child
    /// pointer, and alignment padding sit outside these targets. Capacities
    /// are clamped to the supported range of 4 through [`u16::MAX`], so a
    /// target can be exceeded when four entries of a large type do not fit.
    pub(crate) fn with_payload_targets_impl(
        leaf_payload_bytes: usize,
        branch_payload_bytes: usize,
    ) -> Self {
        let leaf_slot_bytes = core::mem::size_of::<K>().saturating_add(core::mem::size_of::<V>());
        let branch_slot_bytes =
            core::mem::size_of::<K>().saturating_add(core::mem::size_of::<*mut u8>());
        let leaf_cap = capacity_for_payload(leaf_payload_bytes, leaf_slot_bytes);
        let branch_cap = capacity_for_payload(branch_payload_bytes, branch_slot_bytes);
        Self::with_capacities_impl(leaf_cap, branch_cap)
    }

    /// Construct with independent leaf and branch capacities (entries per
    /// node). Inserts shift half a leaf on average, so smaller leaves make
    /// inserts cheaper, while larger branches keep the tree shallow for
    /// lookups; decoupling the two lets a workload pick both.
    ///
    /// Panics if either capacity is below four, the smallest a node can
    /// hold and still split and merge.
    pub(crate) fn with_capacities_impl(leaf_cap: usize, branch_cap: usize) -> Self {
        assert!(
            leaf_cap >= MIN_NODE_CAPACITY && branch_cap >= MIN_NODE_CAPACITY,
            "node capacity must be at least {MIN_NODE_CAPACITY}"
        );
        let leaf_u16 = core::cmp::min(leaf_cap, u16::MAX as usize) as u16;
        let branch_u16 = core::cmp::min(branch_cap, u16::MAX as usize) as u16;
        // The root leaf is allocated by the first insert, so an empty map
        // costs nothing beyond its layouts.
        Self {
            root: None,
            entry_count: 0,
            #[cfg(feature = "delete_profile")]
            delete_profile: DeleteProfile::default(),
            leaf_layout: LeafLayout::compute_for_cap::<K, V>(leaf_u16, true),
            branch_layout: BranchLayout::compute_for_cap::<K>(branch_u16),
            _marker: PhantomData,
        }
    }

    /// An empty map with the same node capacities as this one, so that maps
    /// derived from a map (`clone`, `split_off`) keep its shape.
    pub(crate) fn empty_like(&self) -> Self {
        Self {
            root: None,
            entry_count: 0,
            #[cfg(feature = "delete_profile")]
            delete_profile: DeleteProfile::default(),
            leaf_layout: self.leaf_layout,
            branch_layout: self.branch_layout,
            _marker: PhantomData,
        }
    }

    /// Whether the map holds no entries.
    pub fn is_empty(&self) -> bool {
        self.entry_count == 0
    }

    /// The number of entries.
    pub fn len(&self) -> usize {
        self.entry_count
    }

    /// Remove every entry.
    /// Lean: `clearH_sim` (`Proofs/HeapLedger.lean`): the store is empty
    /// afterwards; `runH_ledger` closes the books over any operation sequence.
    pub fn clear(&mut self) {
        self.entry_count = 0;
        if let Some(root) = self.root.take() {
            unsafe {
                self.drop_subtree(root);
            }
        }
    }
}
