//! Iteration that consumes the map.
//!
//! The map's nodes are handed to the iterator, which reads each key and
//! value out of its slot and frees every leaf once both cursors have left
//! it. Walking the leaf chain costs one pointer hop per leaf, where
//! repeatedly popping the first entry would cost a descent per item.

use core::iter::FusedIterator;
use core::marker::PhantomData;
use core::ptr::{self, NonNull};

use crate::layout;
use crate::node_alloc::{free_branch_block, free_leaf_block};
use crate::{BPlusTreeMap, NodeHdr, NodeTag};

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
            let fp = layout::carve_leaf::<K, V>(first, &leaf_layout);
            let lp = layout::carve_leaf::<K, V>(last, &leaf_layout);
            let front_len = (*fp.hdr).len as usize;
            let back_idx = (*lp.hdr).len as usize;
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
                    let parts = layout::carve_leaf::<K, V>(leaf, &self.leaf_layout);
                    let k = ptr::read(parts.keys_ptr.add(self.front_idx) as *const K);
                    let v = ptr::read(parts.vals_ptr.add(self.front_idx) as *const V);
                    self.front_idx += 1;
                    self.remaining -= 1;
                    return Some((k, v));
                }
            }

            // Everything this leaf held has been yielded from one end or
            // the other, so its memory goes back now.
            let next = unsafe {
                let parts = layout::carve_leaf::<K, V>(leaf, &self.leaf_layout);
                let next = NonNull::new(*parts.next_ptr);
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
                    let np = layout::carve_leaf::<K, V>(next, &self.leaf_layout);
                    self.front = Some(next);
                    self.front_idx = 0;
                    self.front_len = (*np.hdr).len as usize;
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
                    let parts = layout::carve_leaf::<K, V>(self.back, &self.leaf_layout);
                    self.back_idx -= 1;
                    let k = ptr::read(parts.keys_ptr.add(self.back_idx) as *const K);
                    let v = ptr::read(parts.vals_ptr.add(self.back_idx) as *const V);
                    self.remaining -= 1;
                    return Some((k, v));
                }
            }

            let prev = unsafe {
                let parts = layout::carve_leaf::<K, V>(self.back, &self.leaf_layout);
                let prev = parts.prev_ptr.and_then(|p| NonNull::new(*p));
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
                    let pp = layout::carve_leaf::<K, V>(prev, &self.leaf_layout);
                    self.back = prev;
                    self.back_idx = (*pp.hdr).len as usize;
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
        let hdr = &*(node.as_ptr() as *const NodeHdr);
        if hdr.tag == NodeTag::Leaf {
            return;
        }
        let parts = layout::carve_branch::<K>(node, &self.branch_layout);
        let len = (*parts.hdr).len as usize;
        let children = core::slice::from_raw_parts(parts.children_ptr as *const *mut u8, len + 1);
        for child in children.iter().filter_map(|&p| NonNull::new(p)) {
            self.free_branch_spine(child);
        }
        ptr::drop_in_place(ptr::slice_from_raw_parts_mut(parts.keys_ptr as *mut K, len));
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
