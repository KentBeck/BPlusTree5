use alloc::vec::Vec;

use core::ptr::NonNull;

use crate::layout;
use crate::{alloc_branch_block, alloc_leaf_block, BPlusTreeMap, BTreeResult, NodeHdr, NodeTag};

pub(crate) enum InsertResult<K, V> {
    NoSplit(Option<V>),
    Split {
        sep_key: K,
        right: NonNull<u8>,
        old_value: Option<V>,
    },
}

impl<K: Ord + Clone, V> BPlusTreeMap<K, V> {
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        let old_value = self.insert_inner(key, value);
        if old_value.is_none() {
            self.entry_count += 1;
        }
        old_value
    }

    fn insert_inner(&mut self, key: K, value: V) -> Option<V> {
        let root = match self.root {
            Some(p) => p,
            None => unsafe { alloc_leaf_block(&self.leaf_layout).expect("alloc leaf") },
        };
        if self.root.is_none() {
            self.root = Some(root);
        }

        match unsafe { self.insert_rec(root, key, value) } {
            InsertResult::NoSplit(old) => old,
            InsertResult::Split {
                sep_key,
                right,
                old_value,
            } => {
                // The root itself split: grow the tree by one level.
                unsafe { self.grow_root(root, sep_key, right) };
                old_value
            }
        }
    }

    /// Insert below `node`; on a split, hand the separator and new right
    /// sibling up for the parent to absorb. Mirror of `remove_rec`: descend
    /// on the way down, repair on the way up. Depth is logarithmic in the
    /// entry count (non-root branches hold at least two keys), so the
    /// recursion is shallow.
    unsafe fn insert_rec(&mut self, node: NonNull<u8>, key: K, value: V) -> InsertResult<K, V> {
        let hdr = &*(node.as_ptr() as *const NodeHdr);
        match hdr.tag {
            NodeTag::Leaf => self.leaf_insert_or_split(node, key, value),
            NodeTag::Branch => {
                let (child, child_idx) = self.child_for_key(node, &key).expect("child must exist");
                match self.insert_rec(child, key, value) {
                    InsertResult::NoSplit(old) => InsertResult::NoSplit(old),
                    InsertResult::Split {
                        sep_key,
                        right,
                        old_value,
                    } => self.branch_apply_split(node, child_idx, sep_key, right, old_value),
                }
            }
        }
    }

    /// Replace the root with a new branch holding `sep_key` between the old
    /// root and `right`. Inverse of `replace_root` in delete.
    unsafe fn grow_root(&mut self, old_root: NonNull<u8>, sep_key: K, right: NonNull<u8>) {
        let branch = alloc_branch_block(&self.branch_layout).expect("alloc new root branch");
        let b = layout::carve_branch::<K>(branch, &self.branch_layout);
        (*b.hdr).len = 1;
        self.write_key_at(b.keys_ptr as *mut K, 0, sep_key);
        let children = b.children_ptr as *mut *mut u8;
        *children = old_root.as_ptr();
        *children.add(1) = right.as_ptr();
        self.root = Some(branch);
    }

    pub fn batch_insert(&mut self, items: Vec<(K, V)>) -> BTreeResult<Vec<Option<V>>> {
        let mut old_vals = Vec::with_capacity(items.len());
        for (k, v) in items {
            old_vals.push(self.insert(k, v));
        }
        Ok(old_vals)
    }

    /// Absorb a child split into `node` at `child_idx`: insert the separator
    /// and right-sibling pointer, splitting this branch too if it is full.
    unsafe fn branch_apply_split(
        &mut self,
        node: NonNull<u8>,
        child_idx: usize,
        sep_key: K,
        right: NonNull<u8>,
        old_value: Option<V>,
    ) -> InsertResult<K, V> {
        let b = layout::carve_branch::<K>(node, &self.branch_layout);
        let cur_len = (*b.hdr).len as usize;
        let cap = self.branch_layout.cap as usize;
        if cur_len < cap {
            let keys = b.keys_ptr as *mut K;
            let children = b.children_ptr as *mut *mut u8;
            self.branch_open_gap(keys, children, child_idx, cur_len);
            self.write_key_at(keys, child_idx, sep_key);
            *children.add(child_idx + 1) = right.as_ptr();
            (*b.hdr).len = (cur_len + 1) as u16;
            InsertResult::NoSplit(old_value)
        } else {
            self.branch_insert_and_split(node, child_idx, sep_key, right, old_value)
        }
    }

    unsafe fn branch_insert_and_split(
        &mut self,
        node: NonNull<u8>,
        insert_idx: usize,
        ins_key: K,
        ins_right: NonNull<u8>,
        old_value: Option<V>,
    ) -> InsertResult<K, V> {
        let b = layout::carve_branch::<K>(node, &self.branch_layout);
        let len = (*b.hdr).len as usize;
        let keys = b.keys_ptr as *mut K;
        let children = b.children_ptr as *mut *mut u8;

        let right_node = alloc_branch_block(&self.branch_layout).expect("alloc right branch");
        let rb = layout::carve_branch::<K>(right_node, &self.branch_layout);
        let r_keys = rb.keys_ptr as *mut K;
        let r_children = rb.children_ptr as *mut *mut u8;

        // View the branch as child_0 plus (key, child-after) entries; the
        // entry view makes this one case, shaped like leaf_insert_or_split:
        // move the tail entries out, insert into whichever side the new
        // entry sorts into, then promote the boundary. `left_count` is the
        // final left size; promoting the boundary makes the sides balance.
        let left_count = (len + 1) / 2;
        let left_keep = if insert_idx < left_count {
            left_count - 1
        } else {
            left_count
        };

        // Move entries [left_keep..len) to the right node: keys to [0..),
        // each entry's child to [1..) (slot 0 is filled by the promotion).
        let move_count = len - left_keep;
        core::ptr::copy_nonoverlapping(keys.add(left_keep), r_keys, move_count);
        core::ptr::copy_nonoverlapping(children.add(left_keep + 1), r_children.add(1), move_count);
        (*b.hdr).len = left_keep as u16;
        (*rb.hdr).len = move_count as u16;

        // Insert the new entry into whichever side it sorts into.
        if insert_idx < left_count {
            self.branch_open_gap(keys, children, insert_idx, left_keep);
            self.write_key_at(keys, insert_idx, ins_key);
            *children.add(insert_idx + 1) = ins_right.as_ptr();
            (*b.hdr).len = (left_keep + 1) as u16;
        } else {
            let r_idx = insert_idx - left_keep;
            self.branch_open_gap(r_keys, r_children, r_idx, move_count);
            self.write_key_at(r_keys, r_idx, ins_key);
            *r_children.add(r_idx + 1) = ins_right.as_ptr();
            (*rb.hdr).len = (move_count + 1) as u16;
        }

        // Promote the boundary: the right node's first entry's key goes up,
        // and its child becomes the right node's leftmost child (the same
        // close-slot-0 move as rotate_branch_left's pop).
        let r_len = (*rb.hdr).len as usize;
        let sep_key = core::ptr::read(r_keys);
        core::ptr::copy(r_keys.add(1), r_keys, r_len - 1);
        core::ptr::copy(r_children.add(1), r_children, r_len);
        (*rb.hdr).len = (r_len - 1) as u16;

        InsertResult::Split {
            sep_key,
            right: right_node,
            old_value,
        }
    }

    #[inline(always)]
    unsafe fn insert_into_leaf_slot(
        &mut self,
        parts: layout::LeafParts<K, V>,
        idx: usize,
        cur_len: usize,
        key: K,
        value: V,
    ) {
        self.shift_right(
            parts.keys_ptr as *mut K,
            parts.vals_ptr as *mut V,
            idx,
            cur_len,
        );
        self.write_kv_at(
            parts.keys_ptr as *mut K,
            parts.vals_ptr as *mut V,
            idx,
            key,
            value,
        );
        (*parts.hdr).len = (cur_len + 1) as u16;
    }
    unsafe fn leaf_insert_or_split(
        &mut self,
        leaf: NonNull<u8>,
        key: K,
        value: V,
    ) -> InsertResult<K, V> {
        let parts = layout::carve_leaf::<K, V>(leaf, &self.leaf_layout);
        let len = (*parts.hdr).len as usize;
        let keys = core::slice::from_raw_parts(parts.keys_ptr as *const K, len);
        match self.binary_search_keys(keys, &key) {
            Ok(idx) => {
                let vptr = parts.vals_ptr.add(idx) as *mut V;
                let old = core::ptr::read(vptr);
                core::ptr::write(vptr, value);
                InsertResult::NoSplit(Some(old))
            }
            Err(idx) => {
                if len < self.leaf_layout.cap as usize {
                    self.insert_into_leaf_slot(parts, idx, len, key, value);
                    return InsertResult::NoSplit(None);
                }

                // The leaf is full: split it first, then run the ordinary
                // insert on whichever half the key sorts into. A key below
                // the separator keeps its slot in the left half; a key
                // above it lands in the right half past slot 0, so the
                // separator read at the split stays the right half's first
                // key.
                let (right, sep) = self.split_leaf(leaf);
                let left_len = self.node_len(leaf);
                if key < sep {
                    self.insert_into_leaf_slot(parts, idx, left_len, key, value);
                } else {
                    let r = layout::carve_leaf::<K, V>(right, &self.leaf_layout);
                    self.insert_into_leaf_slot(r, idx - left_len, len - left_len, key, value);
                }
                InsertResult::Split {
                    sep_key: sep,
                    right,
                    old_value: None,
                }
            }
        }
    }

    /// Split a full leaf: the upper half moves to a new right sibling,
    /// linked in after `leaf`. The left half keeps `(len + 1) / 2` items,
    /// so both halves meet the minimum fill for every capacity. Returns the
    /// new sibling and the separator, its first key. Inverse of
    /// `merge_leaf_into`.
    unsafe fn split_leaf(&mut self, leaf: NonNull<u8>) -> (NonNull<u8>, K) {
        let l = layout::carve_leaf::<K, V>(leaf, &self.leaf_layout);
        let len = (*l.hdr).len as usize;
        let left_len = (len + 1) / 2;
        let move_count = len - left_len;

        let right = alloc_leaf_block(&self.leaf_layout).expect("alloc right leaf");
        let r = layout::carve_leaf::<K, V>(right, &self.leaf_layout);
        // Moved-from slots stay physically populated; hdr.len excludes them.
        self.move_kv_range(
            l.keys_ptr as *const K,
            l.vals_ptr as *const V,
            left_len,
            r.keys_ptr as *mut K,
            r.vals_ptr as *mut V,
            0,
            move_count,
        );
        (*l.hdr).len = left_len as u16;
        (*r.hdr).len = move_count as u16;
        self.link_leaf_after(leaf, right);

        let sep = self.key_clone_at(r.keys_ptr as *const K, 0);
        (right, sep)
    }
}
