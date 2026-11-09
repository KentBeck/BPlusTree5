//! Iteration that consumes the map.
//!
//! The map's nodes are handed to the iterator, which reads each key and
//! value out of its slot and frees every leaf once both cursors have left
//! it. Walking the leaf chain costs one pointer hop per leaf, where
//! repeatedly popping the first entry would cost a descent per item.

use core::iter::FusedIterator;
use core::marker::PhantomData;
use core::ptr::{self, NonNull};

use crate::layout::{self, NodeTag};
use crate::node::{self, LeafRef};
use crate::node_alloc::{free_branch_block, free_leaf_block};
use crate::BPlusTreeMap;

/// Owning iterator over a map's entries, in key order.
pub struct IntoIter<K, V> {
    leaf_layout: layout::LeafLayout,
    /// Leaf the front cursor sits in, or `None` once the two cursors have
    /// met and every leaf has been freed.
    front: Option<NonNull<u8>>,
    front_idx: usize,
    front_len: usize,
    /// Leaf the back cursor sits in. Meaningful only while `front` is Some.
    back: NonNull<u8>,
    /// One past the last entry the back cursor has still to yield.
    back_idx: usize,
    remaining: usize,
    _marker: PhantomData<(K, V)>,
}

// The iterator owns the nodes outright, exactly as the map did.
unsafe impl<K: Send, V: Send> Send for IntoIter<K, V> {}
unsafe impl<K: Sync, V: Sync> Sync for IntoIter<K, V> {}

impl<K, V> IntoIter<K, V> {
    /// Take the map's nodes. The map is left empty, so its own `Drop` frees
    /// nothing and every node is freed exactly once, here.
    pub(crate) fn new(map: &mut BPlusTreeMap<K, V>) -> Self
    where
        K: Ord + Clone,
    {
        let leaf_layout = map.leaf_layout;
        let remaining = map.entry_count;
        map.entry_count = 0;

        // Read both ends of the leaf chain while the branches above it are
        // still there to descend, then keep only the chain.
        let (Some(first), Some(last)) = (map.leftmost_leaf(), map.rightmost_leaf()) else {
            return Self::empty(leaf_layout);
        };
        let root = map.root.take().expect("a leaf chain implies a root");
        unsafe { map.free_branch_spine(root) };
        unsafe {
            let front_len = LeafRef::<K, V>::new(first, &leaf_layout).len();
            let back_idx = LeafRef::<K, V>::new(last, &leaf_layout).len();
            // Only a root leaf can be empty; an empty one still has to be
            // freed, and no entry is ever yielded from it.
            if front_len == 0 {
                free_leaf_block(first, &leaf_layout);
                return Self::empty(leaf_layout);
            }
            Self {
                leaf_layout,
                front: Some(first),
                front_idx: 0,
                front_len,
                back: last,
                back_idx,
                remaining,
                _marker: PhantomData,
            }
        }
    }

    fn empty(leaf_layout: layout::LeafLayout) -> Self {
        Self {
            leaf_layout,
            front: None,
            front_idx: 0,
            front_len: 0,
            back: NonNull::dangling(),
            back_idx: 0,
            remaining: 0,
            _marker: PhantomData,
        }
    }

    /// View `leaf` with the iterator's layout.
    #[inline(always)]
    unsafe fn leaf(&self, leaf: NonNull<u8>) -> LeafRef<K, V> {
        LeafRef::new(leaf, &self.leaf_layout)
    }

    /// Read entry `idx` of `leaf` out, transferring ownership. The slot
    /// stays physically populated; the cursors never revisit it.
    #[inline(always)]
    unsafe fn take_entry(&self, leaf: LeafRef<K, V>, idx: usize) -> (K, V) {
        (ptr::read(leaf.key_ptr(idx)), ptr::read(leaf.val_ptr(idx)))
    }
}

impl<K, V> Iterator for IntoIter<K, V> {
    type Item = (K, V);

    fn next(&mut self) -> Option<(K, V)> {
        loop {
            let leaf = self.front?;
            let same = leaf == self.back;
            let limit = if same { self.back_idx } else { self.front_len };

            if self.front_idx < limit {
                unsafe {
                    let entry = self.take_entry(self.leaf(leaf), self.front_idx);
                    self.front_idx += 1;
                    self.remaining -= 1;
                    return Some(entry);
                }
            }

            // Everything this leaf held has been yielded from one end or
            // the other, so its memory goes back now.
            let next = unsafe {
                let next = self.leaf(leaf).next();
                free_leaf_block(leaf, &self.leaf_layout);
                next
            };

            if same {
                self.front = None;
                return None;
            }

            match next {
                None => {
                    self.front = None;
                    return None;
                }
                Some(next) => unsafe {
                    self.front = Some(next);
                    self.front_idx = 0;
                    self.front_len = self.leaf(next).len();
                },
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.remaining, Some(self.remaining))
    }
}

impl<K, V> DoubleEndedIterator for IntoIter<K, V> {
    fn next_back(&mut self) -> Option<(K, V)> {
        loop {
            let fleaf = self.front?;
            let same = fleaf == self.back;
            let lower = if same { self.front_idx } else { 0 };

            if self.back_idx > lower {
                unsafe {
                    self.back_idx -= 1;
                    let entry = self.take_entry(self.leaf(self.back), self.back_idx);
                    self.remaining -= 1;
                    return Some(entry);
                }
            }

            let prev = unsafe {
                let prev = self.leaf(self.back).prev();
                free_leaf_block(self.back, &self.leaf_layout);
                prev
            };

            if same {
                self.front = None;
                return None;
            }

            match prev {
                None => {
                    self.front = None;
                    return None;
                }
                Some(prev) => unsafe {
                    self.back = prev;
                    self.back_idx = self.leaf(prev).len();
                },
            }
        }
    }
}

impl<K, V> ExactSizeIterator for IntoIter<K, V> {
    fn len(&self) -> usize {
        self.remaining
    }
}

impl<K, V> FusedIterator for IntoIter<K, V> {}

impl<K, V> Drop for IntoIter<K, V> {
    fn drop(&mut self) {
        // Running the iterator to exhaustion drops every entry left and
        // frees every leaf still held.
        for _ in self.by_ref() {}
    }
}

impl<K, V> BPlusTreeMap<K, V> {
    /// Free the branch nodes below `node`, dropping their separator keys
    /// and leaving the leaves and their sibling links untouched.
    ///
    /// The inverse of the branch half of `drop_subtree`: used when the
    /// leaves are about to be drained by an owning iterator.
    unsafe fn free_branch_spine(&mut self, node: NonNull<u8>) {
        if node::tag(node) == NodeTag::Leaf {
            return;
        }
        let branch = self.branch(node);
        for i in 0..=branch.len() {
            if let Some(child) = branch.child_or_null(i) {
                self.free_branch_spine(child);
            }
        }
        branch.drop_keys();
        free_branch_block(node, &self.branch_layout);
    }
}

/// Owning iterator over a map's keys, in order.
pub struct IntoKeys<K, V> {
    pub(crate) inner: IntoIter<K, V>,
}

/// Owning iterator over a map's values, in key order.
pub struct IntoValues<K, V> {
    pub(crate) inner: IntoIter<K, V>,
}

macro_rules! owned_projection {
    ($name:ident, $item:ty, |$kv:ident| $project:expr) => {
        impl<K, V> Iterator for $name<K, V> {
            type Item = $item;

            fn next(&mut self) -> Option<$item> {
                self.inner.next().map(|$kv| $project)
            }

            fn size_hint(&self) -> (usize, Option<usize>) {
                self.inner.size_hint()
            }
        }

        impl<K, V> DoubleEndedIterator for $name<K, V> {
            fn next_back(&mut self) -> Option<$item> {
                self.inner.next_back().map(|$kv| $project)
            }
        }

        impl<K, V> ExactSizeIterator for $name<K, V> {
            fn len(&self) -> usize {
                self.inner.len()
            }
        }

        impl<K, V> FusedIterator for $name<K, V> {}
    };
}

owned_projection!(IntoKeys, K, |kv| kv.0);
owned_projection!(IntoValues, V, |kv| kv.1);
