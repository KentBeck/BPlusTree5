use crate::{
    free_branch_block, free_leaf_block, layout, BPlusTreeError, BPlusTreeMap, NodeHdr, NodeTag,
};
use core::ptr::{self, NonNull};

/// What became of one root child during a root collapse.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum RootChild {
    /// Freed; its slot must be cleared.
    Freed,
    /// Kept as the collapse's survivor.
    Survives,
    /// Cannot be folded in, so the root must stay.
    Blocks,
}

/// How to refill an underfull child, chosen by `plan_rebalance`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Rebalance {
    Keep,
    BorrowFromLeft,
    BorrowFromRight,
    MergeWithLeft,
    MergeWithRight,
}

/// Counts structural work performed by successful removals.
///
/// Available only with the `delete_profile` feature. Call
/// [`BPlusTreeMap::reset_delete_profile`] after building a tree to isolate
/// the removal phase.
#[cfg(feature = "delete_profile")]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct DeleteProfile {
    pub leaf_rebalance_checks: usize,
    pub leaf_borrows: usize,
    pub leaf_merges: usize,
    pub branch_rebalance_checks: usize,
    pub branch_borrows: usize,
    pub branch_merges: usize,
    pub leaf_deallocations: usize,
    pub branch_deallocations: usize,
    pub root_collapses: usize,
}

impl<K: Ord + Clone, V> BPlusTreeMap<K, V> {
    #[cfg(feature = "delete_profile")]
    pub fn delete_profile(&self) -> DeleteProfile {
        self.delete_profile
    }

    #[cfg(feature = "delete_profile")]
    pub fn reset_delete_profile(&mut self) {
        self.delete_profile = DeleteProfile::default();
    }

    pub fn remove(&mut self, key: &K) -> Option<V> {
        let root = self.root?;
        let value = unsafe { self.remove_rec(root, key) }?;

        debug_assert!(self.entry_count > 0, "successful removal from an empty map");
        self.entry_count -= 1;

        // Only check root collapse if root is a branch with few children.
        // This avoids unnecessary checks when root is a leaf or has many children.
        unsafe {
            if let Some(root) = self.root {
                let hdr = &*(root.as_ptr() as *const NodeHdr);
                if hdr.tag == NodeTag::Branch && (*hdr).len <= 2 {
                    self.check_root_collapse();
                }
            }
        }

        Some(value)
    }

    /// Shrink a root branch that has at most two children down to its one
    /// surviving child, or to an empty tree when nothing survives.
    unsafe fn check_root_collapse(&mut self) {
        let Some(root) = self.root else {
            return;
        };
        if self.is_leaf(root) {
            return;
        }
        let parts = layout::carve_branch::<K>(root, &self.branch_layout);
        let child_count = (*parts.hdr).len as usize + 1;
        if child_count > 2 {
            return;
        }

        let children = parts.children_ptr as *mut *mut u8;
        let Some(survivor) = self.consolidate_root_children(children, child_count) else {
            return;
        };
        self.replace_root(root, survivor);
    }

    /// Fold the root's `child_count` children down to at most one node:
    /// drop emptied leaves and merge two leaves that fit together. Returns
    /// `None` when the root still needs more than one child, otherwise the
    /// child that should become the new root (`Some(None)` when none is
    /// left).
    unsafe fn consolidate_root_children(
        &mut self,
        children: *mut *mut u8,
        child_count: usize,
    ) -> Option<Option<NonNull<u8>>> {
        let mut survivor: Option<NonNull<u8>> = None;
        for i in 0..child_count {
            let slot = children.add(i);
            let Some(child) = NonNull::new(*slot) else {
                continue;
            };
            match self.absorb_root_child(survivor, child) {
                RootChild::Freed => *slot = ptr::null_mut(),
                RootChild::Survives => survivor = Some(child),
                RootChild::Blocks => return None,
            }
        }
        Some(survivor)
    }

    /// Fold one root child into the collapse so far: an emptied leaf is
    /// freed outright, the first real child becomes the survivor, and a
    /// later leaf is merged into a leaf survivor when it fits. Anything
    /// else means the root cannot collapse.
    unsafe fn absorb_root_child(
        &mut self,
        survivor: Option<NonNull<u8>>,
        child: NonNull<u8>,
    ) -> RootChild {
        if self.is_leaf(child) && self.node_len(child) == 0 {
            self.free_emptied_leaf(child);
            return RootChild::Freed;
        }
        let Some(kept) = survivor else {
            return RootChild::Survives;
        };
        if self.try_merge_leaves(kept, child) {
            RootChild::Freed
        } else {
            RootChild::Blocks
        }
    }

    /// Merge `source` into `target` and free `source`, but only when both
    /// are leaves whose contents fit in one. Returns whether it merged.
    unsafe fn try_merge_leaves(&mut self, target: NonNull<u8>, source: NonNull<u8>) -> bool {
        if !self.is_leaf(target) || !self.is_leaf(source) {
            return false;
        }
        if self.node_len(target) + self.node_len(source) > self.leaf_layout.cap as usize {
            return false;
        }
        self.merge_leaf_into(target, source);
        self.free_emptied_leaf(source);
        true
    }

    /// Free the old root branch and install `survivor` (or nothing) in its
    /// place.
    unsafe fn replace_root(&mut self, root: NonNull<u8>, survivor: Option<NonNull<u8>>) {
        #[cfg(feature = "delete_profile")]
        {
            self.delete_profile.root_collapses += 1;
        }

        // Unlike the merge paths, a collapsing root still owns its
        // separators: nothing moved them elsewhere.
        self.empty_branch(root);
        if let Some(child) = survivor {
            if self.is_leaf(child) {
                self.make_leaf_root(child);
            }
        }
        self.root = survivor;
        self.free_emptied_branch(root);
    }

    #[inline(always)]
    unsafe fn is_leaf(&self, node: NonNull<u8>) -> bool {
        (*(node.as_ptr() as *const NodeHdr)).tag == NodeTag::Leaf
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
        #[cfg(feature = "delete_profile")]
        {
            self.delete_profile.leaf_deallocations += 1;
        }
        free_leaf_block(leaf, &self.leaf_layout);
    }

    /// Append every item of `source` onto the end of `target`, leaving
    /// `source` empty. Bulk inverse of the leaf split's item move.
    unsafe fn merge_leaf_into(&mut self, target: NonNull<u8>, source: NonNull<u8>) {
        #[cfg(feature = "delete_profile")]
        {
            self.delete_profile.leaf_merges += 1;
        }

        let t = layout::carve_leaf::<K, V>(target, &self.leaf_layout);
        let s = layout::carve_leaf::<K, V>(source, &self.leaf_layout);

        let target_len = (*t.hdr).len as usize;
        let source_len = (*s.hdr).len as usize;
        debug_assert!(
            target_len + source_len <= self.leaf_layout.cap as usize,
            "leaf merge would overflow: callers merge only when both halves \
             are at or below the minimum fill"
        );

        self.move_kv_range(
            s.keys_ptr as *const K,
            s.vals_ptr as *const V,
            0,
            t.keys_ptr as *mut K,
            t.vals_ptr as *mut V,
            target_len,
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
    unsafe fn merge_branch_into(&mut self, target: NonNull<u8>, separator: K, source: NonNull<u8>) {
        #[cfg(feature = "delete_profile")]
        {
            self.delete_profile.branch_merges += 1;
        }

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

    /// Restore minimum fill for `children[child_idx]` after a removal:
    /// borrow from a sibling that can spare an entry, else merge with one.
    /// `rebalance_branch_child` is its structural twin; both defer the
    /// decision to `plan_rebalance` and only supply the leaf or branch
    /// flavour of each repair.
    unsafe fn rebalance_leaf_child(
        &mut self,
        branch: NonNull<u8>,
        child_idx: usize,
        branch_len: usize,
    ) {
        #[cfg(feature = "delete_profile")]
        {
            self.delete_profile.leaf_rebalance_checks += 1;
        }

        let min = self.min_leaf_len();
        match self.plan_rebalance(branch, child_idx, branch_len, min) {
            Rebalance::Keep => {}
            Rebalance::BorrowFromLeft => self.rotate_leaf_right(branch, child_idx - 1),
            Rebalance::BorrowFromRight => self.rotate_leaf_left(branch, child_idx),
            Rebalance::MergeWithLeft => self.merge_leaf_pair(branch, child_idx - 1),
            Rebalance::MergeWithRight => self.merge_leaf_pair(branch, child_idx),
        }
    }

    /// Structural twin of `rebalance_leaf_child`.
    unsafe fn rebalance_branch_child(
        &mut self,
        branch: NonNull<u8>,
        child_idx: usize,
        branch_len: usize,
    ) {
        #[cfg(feature = "delete_profile")]
        {
            self.delete_profile.branch_rebalance_checks += 1;
        }

        let min = self.min_branch_len();
        match self.plan_rebalance(branch, child_idx, branch_len, min) {
            Rebalance::Keep => {}
            Rebalance::BorrowFromLeft => self.rotate_branch_right(branch, child_idx - 1),
            Rebalance::BorrowFromRight => self.rotate_branch_left(branch, child_idx),
            Rebalance::MergeWithLeft => self.merge_branch_pair(branch, child_idx - 1),
            Rebalance::MergeWithRight => self.merge_branch_pair(branch, child_idx),
        }
    }

    /// Decide how to refill `children[child_idx]` when it has dropped below
    /// `min`: prefer borrowing from a sibling that holds more than `min`
    /// (left first), else merge with the left sibling, else the right.
    /// Null siblings can occur at the root while `check_root_collapse` is
    /// mid-repair; they can never lend, but the merge fallback assumes the
    /// chosen neighbour is present, as it always is below the root.
    unsafe fn plan_rebalance(
        &self,
        branch: NonNull<u8>,
        child_idx: usize,
        branch_len: usize,
        min: usize,
    ) -> Rebalance {
        let parts = layout::carve_branch::<K>(branch, &self.branch_layout);
        let children = parts.children_ptr as *mut *mut u8;
        let has_left = child_idx > 0;
        let has_right = child_idx < branch_len;

        let child = NonNull::new_unchecked(*children.add(child_idx));
        if self.node_len(child) >= min {
            return Rebalance::Keep;
        }
        if has_left && self.child_len(children, child_idx - 1) > min {
            return Rebalance::BorrowFromLeft;
        }
        if has_right && self.child_len(children, child_idx + 1) > min {
            return Rebalance::BorrowFromRight;
        }
        if has_left {
            return Rebalance::MergeWithLeft;
        }
        if has_right {
            return Rebalance::MergeWithRight;
        }
        Rebalance::Keep
    }

    /// Length of `children[idx]`, or 0 for a null slot.
    #[inline(always)]
    unsafe fn child_len(&self, children: *mut *mut u8, idx: usize) -> usize {
        NonNull::new(*children.add(idx)).map_or(0, |node| self.node_len(node))
    }

    /// Rotate one entry rightward through separator `sep_idx`: the left
    /// child's last key moves up to the parent, the old separator moves down
    /// as the right child's first key, and the left child's last subtree
    /// travels with it. A pass-through: contrast the leaf rotations, which
    /// re-derive the separator from data.
    unsafe fn rotate_branch_right(&mut self, branch: NonNull<u8>, sep_idx: usize) {
        #[cfg(feature = "delete_profile")]
        {
            self.delete_profile.branch_borrows += 1;
        }

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
        #[cfg(feature = "delete_profile")]
        {
            self.delete_profile.branch_borrows += 1;
        }

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
        #[cfg(feature = "delete_profile")]
        {
            self.delete_profile.branch_deallocations += 1;
        }
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
        #[cfg(feature = "delete_profile")]
        {
            self.delete_profile.leaf_borrows += 1;
        }

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
        #[cfg(feature = "delete_profile")]
        {
            self.delete_profile.leaf_borrows += 1;
        }

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
