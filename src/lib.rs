#![no_std]

extern crate alloc;

use core::marker::PhantomData;
use core::ptr::{self, NonNull};

mod common;
mod delete;
mod get;
mod insert;
mod iterate;
mod layout;
mod node_alloc;

#[cfg(feature = "delete_profile")]
pub use delete::DeleteProfile;
pub use iterate::{Items, Keys, Values};
pub use layout::{align_up, BranchLayout, LeafLayout, NodeHdr, NodeTag};
pub use node_alloc::{
    alloc_branch_block, alloc_leaf_block, alloc_raw, dealloc_raw, free_branch_block,
    free_leaf_block, init_branch_block, init_leaf_block,
};

/// Leaf key/value bytes targeted by [`BPlusTreeMap::recommended`].
pub const RECOMMENDED_LEAF_PAYLOAD_BYTES: usize = 512;

/// Branch key/child-pointer bytes targeted by [`BPlusTreeMap::recommended`].
pub const RECOMMENDED_BRANCH_PAYLOAD_BYTES: usize = 4 * 1024;

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

/// Raw-memory B+ tree map with fixed-size leaf and branch nodes.
///
/// This type only defines the top-level container and precomputed layouts.
/// Nodes are single raw allocations carved according to these layouts.
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
    /// Returns the configured layout for leaf nodes.
    pub fn leaf_layout(&self) -> &LeafLayout {
        &self.leaf_layout
    }

    /// Returns the configured layout for branch nodes.
    pub fn branch_layout(&self) -> &BranchLayout {
        &self.branch_layout
    }

    /// Drop every key and value the subtree owns, then free its nodes.
    /// Used by `Drop` and `clear`, which own the whole tree; the incremental
    /// paths in `delete` instead free nodes whose contents have already moved
    /// elsewhere (see `free_emptied_leaf` / `free_emptied_branch`).
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

// =============================
// Public API surface (compat scaffolding)
// =============================
// This section exists so the test suite imported from BPlusTree3 compiles
// against this implementation: error types, Result aliases, and convenience
// wrappers (get_item, remove_item, batch_insert, ...) over the real API.

use alloc::format;
use alloc::string::String;
use core::fmt;

#[derive(Debug)]
pub enum BPlusTreeError {
    InvalidCapacity(String),
    KeyNotFound,
    DataIntegrityError(String),
    AllocationError(String),
}

impl fmt::Display for BPlusTreeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BPlusTreeError::InvalidCapacity(s) => write!(f, "InvalidCapacity: {}", s),
            BPlusTreeError::KeyNotFound => write!(f, "Key not found"),
            BPlusTreeError::DataIntegrityError(s) => write!(f, "DataIntegrityError: {}", s),
            BPlusTreeError::AllocationError(s) => write!(f, "AllocationError: {}", s),
        }
    }
}

impl core::error::Error for BPlusTreeError {}

impl<K: Ord + Clone, V> BPlusTreeMap<K, V> {
    // ===== Compatibility constructors =====
    pub fn new(capacity: usize) -> Result<Self, BPlusTreeError> {
        Self::with_caps(capacity, capacity)
    }

    /// Construct with cache-oriented capacities derived from `K` and `V`.
    ///
    /// The targets are 512 bytes of keys and values per leaf and 4 KiB of
    /// keys and child pointers per branch. On a 64-bit target,
    /// `BPlusTreeMap<u64, u64>` gets leaf/branch capacities of 32/256. Larger
    /// element types produce smaller capacities instead of silently creating
    /// much larger nodes.
    pub fn recommended() -> Result<Self, BPlusTreeError> {
        Self::with_payload_targets(
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
    pub fn with_payload_targets(
        leaf_payload_bytes: usize,
        branch_payload_bytes: usize,
    ) -> Result<Self, BPlusTreeError> {
        let leaf_slot_bytes = core::mem::size_of::<K>().saturating_add(core::mem::size_of::<V>());
        let branch_slot_bytes =
            core::mem::size_of::<K>().saturating_add(core::mem::size_of::<*mut u8>());
        let leaf_cap = capacity_for_payload(leaf_payload_bytes, leaf_slot_bytes);
        let branch_cap = capacity_for_payload(branch_payload_bytes, branch_slot_bytes);
        Self::with_caps(leaf_cap, branch_cap)
    }

    /// Construct with independent leaf and branch capacities (entries per
    /// node). Inserts shift half a leaf on average, so smaller leaves make
    /// inserts cheaper, while larger branches keep the tree shallow for
    /// lookups; decoupling the two lets a workload pick both.
    pub fn with_caps(leaf_cap: usize, branch_cap: usize) -> Result<Self, BPlusTreeError> {
        if leaf_cap < MIN_NODE_CAPACITY || branch_cap < MIN_NODE_CAPACITY {
            return Err(BPlusTreeError::InvalidCapacity("capacity too small".into()));
        }
        let leaf_u16 = core::cmp::min(leaf_cap, u16::MAX as usize) as u16;
        let branch_u16 = core::cmp::min(branch_cap, u16::MAX as usize) as u16;
        let leaf_layout = LeafLayout::compute_for_cap::<K, V>(leaf_u16, true);
        let branch_layout = BranchLayout::compute_for_cap::<K>(branch_u16);
        let mut tree = Self {
            root: None,
            entry_count: 0,
            #[cfg(feature = "delete_profile")]
            delete_profile: DeleteProfile::default(),
            leaf_layout,
            branch_layout,
            _marker: PhantomData,
        };
        unsafe {
            let leaf = alloc_leaf_block(&tree.leaf_layout)
                .ok_or_else(|| BPlusTreeError::AllocationError("leaf root".into()))?;
            tree.root = Some(leaf);
        }
        Ok(tree)
    }

    pub fn is_empty(&self) -> bool {
        self.entry_count == 0
    }

    pub fn len(&self) -> usize {
        self.entry_count
    }

    pub fn clear(&mut self) {
        self.entry_count = 0;
        if let Some(root) = self.root.take() {
            unsafe {
                self.drop_subtree(root);
            }
        }
    }
}

// =============================
// Enhanced error/result compatibility layer (stubs)
// =============================

pub type InitResult<T> = Result<T, BPlusTreeError>;
pub type BTreeResult<T> = Result<T, BPlusTreeError>;
pub type KeyResult<T> = Result<T, BPlusTreeError>;
pub type ModifyResult<T> = Result<T, BPlusTreeError>;

#[cfg(feature = "compat_test_api")]
pub trait BTreeResultExt<T> {
    fn with_context(self, _ctx: &str) -> Result<T, BPlusTreeError>;
    fn with_operation(self, _op: &str) -> Result<T, BPlusTreeError>;
    fn or_default_with_log(self) -> T
    where
        T: Default;
}

#[cfg(feature = "compat_test_api")]
impl<T> BTreeResultExt<T> for Result<T, BPlusTreeError> {
    fn with_context(self, _ctx: &str) -> Result<T, BPlusTreeError> {
        self
    }
    fn with_operation(self, _op: &str) -> Result<T, BPlusTreeError> {
        self
    }
    fn or_default_with_log(self) -> T
    where
        T: Default,
    {
        self.unwrap_or_default()
    }
}

impl BPlusTreeError {
    pub fn invalid_capacity(got: usize, min: usize) -> Self {
        BPlusTreeError::InvalidCapacity(format!(
            "Capacity {} is invalid (minimum required: {})",
            got, min
        ))
    }
    pub fn data_integrity(op: &str, why: &str) -> Self {
        BPlusTreeError::DataIntegrityError(format!("{}: {}", op, why))
    }
    pub fn allocation_error(what: &str, why: &str) -> Self {
        BPlusTreeError::AllocationError(format!("Failed to allocate {}: {}", what, why))
    }
}

impl core::cmp::PartialEq for BPlusTreeError {
    fn eq(&self, other: &Self) -> bool {
        core::mem::discriminant(self) == core::mem::discriminant(other)
    }
}
impl Eq for BPlusTreeError {}

// Extra convenience/debug API stubs used in tests
#[cfg(feature = "compat_test_api")]
impl<K: Ord + Clone, V> BPlusTreeMap<K, V> {
    /// Check every tree invariant, naming `op` in the error if any fails.
    pub fn validate_for_operation(&self, op: &str) -> BTreeResult<()> {
        self.check_invariants_detailed()
            .map_err(|why| BPlusTreeError::data_integrity(op, &why))
    }
    pub fn try_get(&self, key: &K) -> KeyResult<&V> {
        self.get_item(key)
    }
    pub fn try_insert(&mut self, key: K, value: V) -> BTreeResult<Option<V>> {
        Ok(self.insert(key, value))
    }
    pub fn try_remove(&mut self, key: &K) -> ModifyResult<V> {
        self.remove_item(key)
    }
}
