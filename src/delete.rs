use crate::{
    free_branch_block, free_leaf_block, layout, BPlusTreeError, BPlusTreeMap, NodeHdr, NodeTag,
};
use core::ptr::{self, NonNull};

impl<K: Ord + Clone, V> BPlusTreeMap<K, V> {
    pub fn remove(&mut self, key: &K) -> Option<V> {
        let root = self.root?;
        let result = unsafe { self.remove_rec(root, key) };
        if result.is_some() {
            // Only check root collapse if root is a branch with few children
            // This avoids unnecessary checks when root is a leaf or has many children
            unsafe {
                if let Some(root) = self.root {
                    let hdr = &*(root.as_ptr() as *const NodeHdr);
                    if hdr.tag == NodeTag::Branch && (*hdr).len <= 2 {
                        self.check_root_collapse();
                    }
                }
            }
        }
        result
    }

    unsafe fn check_root_collapse(&mut self) {
        if let Some(root) = self.root {
            let hdr = &*(root.as_ptr() as *const NodeHdr);
            if hdr.tag == NodeTag::Branch {
                let parts = layout::carve_branch::<K>(root, &self.branch_layout);
                let len = (*parts.hdr).len as usize;
                if len <= 1 {
                    let child_count = len + 1;
                    let mut keep_child: Option<NonNull<u8>> = None;
                    let mut keep_is_leaf = false;

                    for i in 0..child_count {
                        let slot = parts.children_ptr.add(i) as *mut *mut u8;
                        let child_ptr = *slot;
                        if child_ptr.is_null() {
                            continue;
                        }

                        let child_hdr = &*(child_ptr as *const NodeHdr);
                        match child_hdr.tag {
                            NodeTag::Leaf => {
                                let child = NonNull::new_unchecked(child_ptr);
                                if (*child_hdr).len == 0 {
                                    self.free_emptied_leaf(child);
                                    *slot = ptr::null_mut();
                                    continue;
                                }
                                if let Some(existing) = keep_child {
                                    if !keep_is_leaf {
                                        return;
                                    }
                                    let existing_hdr = &*(existing.as_ptr() as *const NodeHdr);
                                    let existing_len = (*existing_hdr).len as usize;
                                    let child_len = (*child_hdr).len as usize;
                                    if existing_len + child_len > self.leaf_layout.cap as usize {
                                        return;
                                    }
                                    self.merge_leaf_into(existing, child);
                                    self.free_emptied_leaf(child);
                                    *slot = ptr::null_mut();
                                } else {
                                    keep_child = Some(child);
                                    keep_is_leaf = true;
                                }
                            }
                            NodeTag::Branch => {
                                if keep_child.is_some() {
                                    return;
                                }
                                keep_child = Some(NonNull::new_unchecked(child_ptr));
                                keep_is_leaf = false;
                            }
                        }
                    }

                    // Unlike the merge paths, a collapsing root still owns its
                    // separators: nothing moved them elsewhere.
                    self.empty_branch(root);
                    if let Some(child) = keep_child {
                        if keep_is_leaf {
                            self.make_leaf_root(child);
                        }
                        self.root = Some(child);
                    } else {
                        self.root = None;
                    }
                    self.free_emptied_branch(root);
                }
            }
        }
    }

    unsafe fn make_leaf_root(&self, leaf: NonNull<u8>) {
        let parts = layout::carve_leaf::<K, V>(leaf, &self.leaf_layout);
        if let Some(prev_ptr) = parts.prev_ptr {
            *prev_ptr = ptr::null_mut();
        }
    }

    /// Unlink an emptied leaf from the sibling chain and free its memory.
    /// The caller must already have moved every item out: this frees memory
    /// only, it never drops contents (contrast `drop_subtree`).
    unsafe fn free_emptied_leaf(&mut self, leaf: NonNull<u8>) {
        let parts = layout::carve_leaf::<K, V>(leaf, &self.leaf_layout);
        debug_assert_eq!(
            (*parts.hdr).len,
            0,
            "free_emptied_leaf called on a leaf that still holds items"
        );
        self.unlink_leaf(leaf);
        free_leaf_block(leaf, &self.leaf_layout);
    }

    /// Append every item of `source` onto the end of `target`, leaving
    /// `source` empty. Bulk inverse of the leaf split's item move.
    unsafe fn merge_leaf_into(&self, target: NonNull<u8>, source: NonNull<u8>) {
        let t = layout::carve_leaf::<K, V>(target, &self.leaf_layout);
        let s = layout::carve_leaf::<K, V>(source, &self.leaf_layout);

        let target_len = (*t.hdr).len as usize;
        let source_len = (*s.hdr).len as usize;
        debug_assert!(
            target_len + source_len <= self.leaf_layout.cap as usize,
            "leaf merge would overflow: callers merge only when both halves \
             are at or below the minimum fill"
        );

        core::ptr::copy_nonoverlapping(
            s.keys_ptr as *const K,
            (t.keys_ptr as *mut K).add(target_len),
            source_len,
        );
        core::ptr::copy_nonoverlapping(
            s.vals_ptr as *const V,
            (t.vals_ptr as *mut V).add(target_len),
            source_len,
        );

        (*t.hdr).len = (target_len + source_len) as u16;
        (*s.hdr).len = 0;
    }

    /// Branch counterpart of `merge_leaf_into`: append `separator` and every
    /// entry of `source` onto the end of `target`, leaving `source` empty.
    /// The separator moves down to sit between target's old last child and
    /// source's first child (leaf merges drop it instead: leaf keys carry
    /// their own ordering).
    unsafe fn merge_branch_into(&self, target: NonNull<u8>, separator: K, source: NonNull<u8>) {
        let t = layout::carve_branch::<K>(target, &self.branch_layout);
        let s = layout::carve_branch::<K>(source, &self.branch_layout);

        let target_len = (*t.hdr).len as usize;
        let source_len = (*s.hdr).len as usize;
        debug_assert!(
            target_len + 1 + source_len <= self.branch_layout.cap as usize,
            "branch merge would overflow: callers merge only when both halves \
             are at or below the minimum fill"
        );

        core::ptr::write((t.keys_ptr as *mut K).add(target_len), separator);
        core::ptr::copy_nonoverlapping(
            s.keys_ptr as *const K,
            (t.keys_ptr as *mut K).add(target_len + 1),
            source_len,
        );
        core::ptr::copy_nonoverlapping(
            s.children_ptr as *const *mut u8,
            (t.children_ptr as *mut *mut u8).add(target_len + 1),
            source_len + 1,
        );

        (*t.hdr).len = (target_len + 1 + source_len) as u16;
        (*s.hdr).len = 0;
    }

    unsafe fn fix_branch_child(&mut self, branch: NonNull<u8>, child_idx: usize) {
        let parts = layout::carve_branch::<K>(branch, &self.branch_layout);
        let len = (*parts.hdr).len as usize;
        if len == 0 {
            return;
        }

        let children = parts.children_ptr as *mut *mut u8;
        let idx = child_idx.min(len);
        let child_ptr = *children.add(idx);
        let Some(_) = NonNull::new(child_ptr) else {
            return;
        };

        let child_hdr = &*(child_ptr as *const NodeHdr);
        match child_hdr.tag {
            NodeTag::Leaf => self.rebalance_leaf_child(branch, idx, len),
            NodeTag::Branch => self.rebalance_branch_child(branch, idx, len),
        }
    }

    unsafe fn rebalance_leaf_child(
        &mut self,
        branch: NonNull<u8>,
        child_idx: usize,
        branch_len: usize,
    ) {
        let parts = layout::carve_branch::<K>(branch, &self.branch_layout);
        let children = parts.children_ptr as *mut *mut u8;

        let child_ptr = *children.add(child_idx);
        let child = NonNull::new_unchecked(child_ptr);
        let child_parts = layout::carve_leaf::<K, V>(child, &self.leaf_layout);
        let child_len = (*child_parts.hdr).len as usize;
        let min = self.min_leaf_len();
        if child_len >= min {
            return;
        }

        if child_idx > 0 {
            let left_ptr = *children.add(child_idx - 1);
            if let Some(left) = NonNull::new(left_ptr) {
                let left_hdr = &*(left_ptr as *const NodeHdr);
                if left_hdr.tag == NodeTag::Leaf {
                    let left_parts = layout::carve_leaf::<K, V>(left, &self.leaf_layout);
                    let left_len = (*left_parts.hdr).len as usize;
                    if left_len > min {
                        self.rotate_leaf_right(branch, child_idx - 1);
                        return;
                    }
                }
            }
        }

        if child_idx < branch_len {
            let right_ptr = *children.add(child_idx + 1);
            if let Some(right) = NonNull::new(right_ptr) {
                let right_hdr = &*(right_ptr as *const NodeHdr);
                if right_hdr.tag == NodeTag::Leaf {
                    let right_parts = layout::carve_leaf::<K, V>(right, &self.leaf_layout);
                    let right_len = (*right_parts.hdr).len as usize;
                    if right_len > min {
                        self.rotate_leaf_left(branch, child_idx);
                        return;
                    }
                }
            }
        }

        if child_idx > 0 {
            self.merge_leaf_pair(branch, child_idx - 1);
        } else if child_idx < branch_len {
            self.merge_leaf_pair(branch, child_idx);
        }
    }

    unsafe fn rebalance_branch_child(
        &mut self,
        branch: NonNull<u8>,
        child_idx: usize,
        branch_len: usize,
    ) {
        let parts = layout::carve_branch::<K>(branch, &self.branch_layout);
        let children = parts.children_ptr as *mut *mut u8;

        let child_ptr = *children.add(child_idx);
        let child = NonNull::new_unchecked(child_ptr);
        let child_parts = layout::carve_branch::<K>(child, &self.branch_layout);
        let child_len = (*child_parts.hdr).len as usize;
        let min = self.min_branch_len();
        if child_len >= min {
            return;
        }

        if child_idx > 0 {
            let left_ptr = *children.add(child_idx - 1);
            if let Some(left) = NonNull::new(left_ptr) {
                let left_parts = layout::carve_branch::<K>(left, &self.branch_layout);
                let left_len = (*left_parts.hdr).len as usize;
                if left_len > min {
                    self.rotate_branch_right(branch, child_idx - 1);
                    return;
                }
            }
        }

        if child_idx < branch_len {
            let right_ptr = *children.add(child_idx + 1);
            if let Some(right) = NonNull::new(right_ptr) {
                let right_parts = layout::carve_branch::<K>(right, &self.branch_layout);
                let right_len = (*right_parts.hdr).len as usize;
                if right_len > min {
                    self.rotate_branch_left(branch, child_idx);
                    return;
                }
            }
        }

        if child_idx > 0 {
            self.merge_branch_pair(branch, child_idx - 1);
        } else if child_idx < branch_len {
            self.merge_branch_pair(branch, child_idx);
        }
    }

    /// Rotate one entry rightward through separator `sep_idx`: the left
    /// child's last key moves up to the parent, the old separator moves down
    /// as the right child's first key, and the left child's last subtree
    /// travels with it. A pass-through: contrast the leaf rotations, which
    /// re-derive the separator from data.
    unsafe fn rotate_branch_right(&mut self, branch: NonNull<u8>, sep_idx: usize) {
        let parts = layout::carve_branch::<K>(branch, &self.branch_layout);
        let children = parts.children_ptr as *mut *mut u8;
        let left = NonNull::new_unchecked(*children.add(sep_idx));
        let right = NonNull::new_unchecked(*children.add(sep_idx + 1));

        let l = layout::carve_branch::<K>(left, &self.branch_layout);
        let r = layout::carve_branch::<K>(right, &self.branch_layout);
        let left_len = (*l.hdr).len as usize;
        let right_len = (*r.hdr).len as usize;
        debug_assert!(left_len > 1, "donor would fall below minimum fill");

        let l_keys = l.keys_ptr as *mut K;
        let l_children = l.children_ptr as *mut *mut u8;
        let r_keys = r.keys_ptr as *mut K;
        let r_children = r.children_ptr as *mut *mut u8;
        let sep_slot = (parts.keys_ptr as *mut K).add(sep_idx);

        let promoted = core::ptr::read(l_keys.add(left_len - 1));
        let moved_child = *l_children.add(left_len);
        (*l.hdr).len = (left_len - 1) as u16;

        // Open the right child's slot 0 for the incoming key and child.
        core::ptr::copy(r_keys, r_keys.add(1), right_len);
        core::ptr::copy(r_children, r_children.add(1), right_len + 1);
        core::ptr::write(r_keys, core::ptr::read(sep_slot));
        *r_children = moved_child;
        (*r.hdr).len = (right_len + 1) as u16;

        core::ptr::write(sep_slot, promoted);
    }

    /// Mirror of `rotate_branch_right`: the right child's first key moves up,
    /// the old separator moves down as the left child's last key, and the
    /// right child's first subtree travels with it.
    unsafe fn rotate_branch_left(&mut self, branch: NonNull<u8>, sep_idx: usize) {
        let parts = layout::carve_branch::<K>(branch, &self.branch_layout);
        let children = parts.children_ptr as *mut *mut u8;
        let left = NonNull::new_unchecked(*children.add(sep_idx));
        let right = NonNull::new_unchecked(*children.add(sep_idx + 1));

        let l = layout::carve_branch::<K>(left, &self.branch_layout);
        let r = layout::carve_branch::<K>(right, &self.branch_layout);
        let left_len = (*l.hdr).len as usize;
        let right_len = (*r.hdr).len as usize;
        debug_assert!(right_len > 1, "donor would fall below minimum fill");

        let l_keys = l.keys_ptr as *mut K;
        let l_children = l.children_ptr as *mut *mut u8;
        let r_keys = r.keys_ptr as *mut K;
        let r_children = r.children_ptr as *mut *mut u8;
        let sep_slot = (parts.keys_ptr as *mut K).add(sep_idx);

        let promoted = core::ptr::read(r_keys);
        let moved_child = *r_children;

        core::ptr::write(l_keys.add(left_len), core::ptr::read(sep_slot));
        *l_children.add(left_len + 1) = moved_child;
        (*l.hdr).len = (left_len + 1) as u16;

        // Close the right child's slot 0 after the outgoing key and child.
        core::ptr::copy(r_keys.add(1), r_keys, right_len - 1);
        core::ptr::copy(r_children.add(1), r_children, right_len);
        (*r.hdr).len = (right_len - 1) as u16;

        core::ptr::write(sep_slot, promoted);
    }

    /// Merge the two children flanking separator `left_idx`:
    /// `children[left_idx]` absorbs `children[left_idx + 1]`, and the
    /// separator (returned by `remove_branch_entry`) moves down between them.
    unsafe fn merge_branch_pair(&mut self, branch: NonNull<u8>, left_idx: usize) {
        let parts = layout::carve_branch::<K>(branch, &self.branch_layout);
        let children = parts.children_ptr as *mut *mut u8;
        let left = NonNull::new_unchecked(*children.add(left_idx));
        let right = NonNull::new_unchecked(*children.add(left_idx + 1));

        let separator = self.remove_branch_entry(branch, left_idx);
        self.merge_branch_into(left, separator, right);
        self.free_emptied_branch(right);
    }

    /// Free an emptied branch's memory. Like `free_emptied_leaf`, the caller
    /// must already have moved or dropped every separator; use `empty_branch`
    /// for a branch that still owns its keys.
    unsafe fn free_emptied_branch(&mut self, node: NonNull<u8>) {
        let parts = layout::carve_branch::<K>(node, &self.branch_layout);
        debug_assert_eq!(
            (*parts.hdr).len,
            0,
            "free_emptied_branch called on a branch that still holds separators"
        );
        free_branch_block(node, &self.branch_layout);
    }

    /// Drop the separators a branch still owns and mark it empty, so it meets
    /// `free_emptied_branch`'s precondition.
    unsafe fn empty_branch(&mut self, node: NonNull<u8>) {
        let parts = layout::carve_branch::<K>(node, &self.branch_layout);
        let len = (*parts.hdr).len as usize;
        for i in 0..len {
            ptr::drop_in_place((parts.keys_ptr as *mut K).add(i));
        }
        (*parts.hdr).len = 0;
    }

    /// Rotate one item rightward through separator `sep_idx`: the left
    /// child's last item becomes the right child's first. Leaves re-derive
    /// the separator from the right child's new first key (contrast the
    /// branch rotations, which pass the separator through).
    unsafe fn rotate_leaf_right(&mut self, branch: NonNull<u8>, sep_idx: usize) {
        let parts = layout::carve_branch::<K>(branch, &self.branch_layout);
        let children = parts.children_ptr as *mut *mut u8;
        let left = NonNull::new_unchecked(*children.add(sep_idx));
        let right = NonNull::new_unchecked(*children.add(sep_idx + 1));

        let l = layout::carve_leaf::<K, V>(left, &self.leaf_layout);
        let r = layout::carve_leaf::<K, V>(right, &self.leaf_layout);
        let left_len = (*l.hdr).len as usize;
        let right_len = (*r.hdr).len as usize;
        debug_assert!(left_len > 1, "donor would fall below minimum fill");

        self.shift_right(r.keys_ptr as *mut K, r.vals_ptr as *mut V, 0, right_len);
        self.move_kv_at(
            l.keys_ptr as *mut K,
            l.vals_ptr as *mut V,
            left_len - 1,
            r.keys_ptr as *mut K,
            r.vals_ptr as *mut V,
            0,
        );
        (*l.hdr).len = (left_len - 1) as u16;
        (*r.hdr).len = (right_len + 1) as u16;

        let new_sep = self.key_clone_at(r.keys_ptr as *const K, 0);
        let sep_slot = (parts.keys_ptr as *mut K).add(sep_idx);
        drop(core::ptr::read(sep_slot));
        core::ptr::write(sep_slot, new_sep);
    }

    /// Mirror of `rotate_leaf_right`: the right child's first item becomes
    /// the left child's last, and the separator is re-derived from the right
    /// child's new first key.
    unsafe fn rotate_leaf_left(&mut self, branch: NonNull<u8>, sep_idx: usize) {
        let parts = layout::carve_branch::<K>(branch, &self.branch_layout);
        let children = parts.children_ptr as *mut *mut u8;
        let left = NonNull::new_unchecked(*children.add(sep_idx));
        let right = NonNull::new_unchecked(*children.add(sep_idx + 1));

        let l = layout::carve_leaf::<K, V>(left, &self.leaf_layout);
        let r = layout::carve_leaf::<K, V>(right, &self.leaf_layout);
        let left_len = (*l.hdr).len as usize;
        let right_len = (*r.hdr).len as usize;
        debug_assert!(right_len > 1, "donor would fall below minimum fill");

        self.move_kv_at(
            r.keys_ptr as *mut K,
            r.vals_ptr as *mut V,
            0,
            l.keys_ptr as *mut K,
            l.vals_ptr as *mut V,
            left_len,
        );
        self.shift_left_kv(r.keys_ptr as *mut K, r.vals_ptr as *mut V, 0, right_len - 1);
        (*l.hdr).len = (left_len + 1) as u16;
        (*r.hdr).len = (right_len - 1) as u16;

        let new_sep = self.key_clone_at(r.keys_ptr as *const K, 0);
        let sep_slot = (parts.keys_ptr as *mut K).add(sep_idx);
        drop(core::ptr::read(sep_slot));
        core::ptr::write(sep_slot, new_sep);
    }

    /// Merge the two children flanking separator `left_idx`:
    /// `children[left_idx]` absorbs `children[left_idx + 1]`. Leaf keys carry
    /// their own ordering, so the separator is redundant and dropped.
    unsafe fn merge_leaf_pair(&mut self, branch: NonNull<u8>, left_idx: usize) {
        let parts = layout::carve_branch::<K>(branch, &self.branch_layout);
        let children = parts.children_ptr as *mut *mut u8;
        let left = NonNull::new_unchecked(*children.add(left_idx));
        let right = NonNull::new_unchecked(*children.add(left_idx + 1));

        self.merge_leaf_into(left, right);
        self.free_emptied_leaf(right);
        drop(self.remove_branch_entry(branch, left_idx));
    }

    /// Remove separator `key_idx` and the child slot to its right, returning
    /// the separator by value: branch merges move it down, leaf merges drop
    /// it. The caller owns freeing the removed child's node.
    unsafe fn remove_branch_entry(&mut self, branch: NonNull<u8>, key_idx: usize) -> K {
        let parts = layout::carve_branch::<K>(branch, &self.branch_layout);
        let len = (*parts.hdr).len as usize;
        debug_assert!(key_idx < len, "separator index out of range");

        let keys = parts.keys_ptr as *mut K;
        let children = parts.children_ptr as *mut *mut u8;

        let separator = core::ptr::read(keys.add(key_idx));
        self.branch_close_gap(keys, children, key_idx, len);
        (*parts.hdr).len = (len - 1) as u16;
        separator
    }

    unsafe fn remove_rec(&mut self, node: NonNull<u8>, key: &K) -> Option<V> {
        let hdr = &*(node.as_ptr() as *const NodeHdr);
        match hdr.tag {
            NodeTag::Leaf => self.leaf_remove(node, key),
            NodeTag::Branch => {
                let (child, idx) = self.child_for_key(node, key)?;
                let result = self.remove_rec(child, key);
                if result.is_some() {
                    self.fix_branch_child(node, idx);
                }
                result
            }
        }
    }

    unsafe fn leaf_remove(&mut self, leaf: NonNull<u8>, key: &K) -> Option<V> {
        let parts = layout::carve_leaf::<K, V>(leaf, &self.leaf_layout);
        let len = (*parts.hdr).len as usize;
        let keys = core::slice::from_raw_parts(parts.keys_ptr as *const K, len);
        let idx = self.binary_search_keys(keys, key).ok()?;

        // Read the key and value (transferring ownership)
        let removed_key = core::ptr::read((parts.keys_ptr as *const K).add(idx));
        let value = core::ptr::read(parts.vals_ptr.add(idx) as *const V);

        // Shift remaining elements using batched operation
        if idx < len - 1 {
            self.shift_left_kv(
                parts.keys_ptr as *mut K,
                parts.vals_ptr as *mut V,
                idx,
                len - idx - 1,
            );
        }

        (*parts.hdr).len = (len - 1) as u16;

        // Drop the removed key (value is returned to caller)
        drop(removed_key);

        Some(value)
    }

    pub fn remove_item(&mut self, key: &K) -> Result<V, BPlusTreeError> {
        self.remove(key).ok_or(BPlusTreeError::KeyNotFound)
    }
}
