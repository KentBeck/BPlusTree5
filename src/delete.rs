use crate::layout::NodeTag;
use crate::node;
use crate::{free_branch_block, free_leaf_block, BPlusTreeMap};
use core::borrow::Borrow;
use core::ptr::NonNull;

/// How to refill an underfull child, chosen by `plan_rebalance`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Rebalance {
    BorrowFromLeft,
    BorrowFromRight,
    MergeWithLeft,
    MergeWithRight,
}

impl Rebalance {
    fn merges_siblings(self) -> bool {
        matches!(self, Self::MergeWithLeft | Self::MergeWithRight)
    }
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

    /// Lean: `removeTree_spec` (`Proofs/Delete.lean`): the returned value was
    /// stored under `key`, the entries become `eraseSorted key` of the old
    /// ones, and the tree stays well-formed at the same height or one lower;
    /// `Map.remove_wf` (`Proofs/Check.lean`) carries `entry_count` along.
    /// On the heap model, `removeH_sim` (`Proofs/HeapRemove.lean`): no fault,
    /// no double free, no leaked node, the sibling chain intact.
    pub fn remove<Q>(&mut self, key: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.remove_entry(key).map(|(_, v)| v)
    }

    /// Remove the entry for `key`, returning the stored key alongside its
    /// value. One descent: the key is read out of its slot rather than
    /// looked up again.
    pub fn remove_entry<Q>(&mut self, key: &Q) -> Option<(K, V)>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        let root = self.root?;
        let mut root_underflowed = false;
        let entry = unsafe { self.remove_rec(root, key, &mut root_underflowed) }?;

        debug_assert!(self.entry_count > 0, "successful removal from an empty map");
        self.entry_count -= 1;

        // Only a root branch left with one or two children can collapse;
        // a leaf root or a wider branch skips the check.
        unsafe {
            if node::tag(root) == NodeTag::Branch && node::len(root) <= 1 {
                self.check_root_collapse(root);
            }
        }

        Some(entry)
    }

    /// Shrink a root branch with at most two children: a lone child becomes
    /// the root, and two leaves whose contents fit in one are merged into
    /// the new root. Anything else keeps the root as it is.
    ///
    /// Children are never null and a non-root leaf is never empty (see
    /// `removeTree_spec` in `lean/BPlusTree/Proofs/Delete.lean`), so there
    /// is nothing to skip or free on the way.
    /// Lean: `checkRootCollapseH_sim` (`Proofs/HeapRemove.lean`) frees exactly
    /// the old root (and the merged-away leaf) and keeps the rest.
    unsafe fn check_root_collapse(&mut self, root: NonNull<u8>) {
        let b = self.branch(root);
        let len = b.len();
        debug_assert!(
            len <= 1,
            "check_root_collapse on a root with more than two children"
        );

        let first = b.child(0);
        if len == 1 {
            let second = b.child(1);
            if !self.try_merge_leaves(first, second) {
                return;
            }
        }
        self.replace_root(root, first);
    }

    /// Merge `source` into `target` and free `source`, but only when both
    /// are leaves whose contents fit in one. Returns whether it merged.
    unsafe fn try_merge_leaves(&mut self, target: NonNull<u8>, source: NonNull<u8>) -> bool {
        if !self.is_leaf(target) || !self.is_leaf(source) {
            return false;
        }
        if node::len(target) + node::len(source) > self.leaf_layout.cap as usize {
            return false;
        }
        self.merge_leaf_into(target, source);
        self.free_emptied_leaf(source);
        true
    }

    /// Free the old root branch and install `survivor` in its place.
    unsafe fn replace_root(&mut self, root: NonNull<u8>, survivor: NonNull<u8>) {
        #[cfg(feature = "delete_profile")]
        {
            self.delete_profile.root_collapses += 1;
        }

        // Unlike the merge paths, a collapsing root still owns its
        // separators: nothing moved them elsewhere.
        self.empty_branch(root);
        if self.is_leaf(survivor) {
            self.make_leaf_root(survivor);
        }
        self.root = Some(survivor);
        self.free_emptied_branch(root);
    }

    #[inline(always)]
    unsafe fn is_leaf(&self, node: NonNull<u8>) -> bool {
        node::tag(node) == NodeTag::Leaf
    }

    unsafe fn make_leaf_root(&self, leaf: NonNull<u8>) {
        self.leaf(leaf).set_prev(None);
    }

    /// Unlink an emptied leaf from the sibling chain and free its memory.
    /// The caller must already have moved every item out: this frees memory
    /// only, it never drops contents (contrast `drop_subtree`).
    unsafe fn free_emptied_leaf(&mut self, leaf: NonNull<u8>) {
        debug_assert_eq!(
            node::len(leaf),
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
    /// Lean: `mergeLeafPair_window` (`Proofs/Delete.lean`) shows the two fit
    /// whenever `plan_rebalance` chose to merge them.
    unsafe fn merge_leaf_into(&mut self, target: NonNull<u8>, source: NonNull<u8>) {
        #[cfg(feature = "delete_profile")]
        {
            self.delete_profile.leaf_merges += 1;
        }

        let t = self.leaf(target);
        let s = self.leaf(source);
        debug_assert!(
            t.len() + s.len() <= t.cap(),
            "leaf merge would overflow: callers merge only when both halves \
             are at or below the minimum fill"
        );

        s.move_tail_to(0, t, t.len(), s.len());
    }

    /// Branch counterpart of `merge_leaf_into`: append `separator` and every
    /// entry of `source` onto the end of `target`, leaving `source` empty.
    /// The separator moves down to sit between target's old last child and
    /// source's first child (leaf merges drop it instead: leaf keys carry
    /// their own ordering).
    /// Lean: `mergeBranchPair_window` (`Proofs/Delete.lean`), likewise.
    unsafe fn merge_branch_into(&mut self, target: NonNull<u8>, separator: K, source: NonNull<u8>) {
        #[cfg(feature = "delete_profile")]
        {
            self.delete_profile.branch_merges += 1;
        }

        let t = self.branch(target);
        let s = self.branch(source);
        debug_assert!(
            t.len() + 1 + s.len() <= t.cap(),
            "branch merge would overflow: callers merge only when both halves \
             are at or below the minimum fill"
        );

        t.absorb(separator, s);
    }

    /// Repair one known-underfull child. Returns whether repairing it made the
    /// containing branch underfull in turn.
    ///
    /// A branch holds at least one separator and `child_idx` addresses one
    /// of its `len + 1` children (`fixBranchChild_spec` in
    /// `lean/BPlusTree/Proofs/Delete.lean`).
    /// Lean: `fixBranchChildH_sim` (`Proofs/HeapRemove.lean`): on the heap
    /// model the repair never faults, returns the same verdict, and touches
    /// only the two siblings, this branch, and the successor leaf's `prev`.
    unsafe fn fix_branch_child(&mut self, branch: NonNull<u8>, child_idx: usize) -> bool {
        let b = self.branch(branch);
        let len = b.len();
        debug_assert!(len > 0, "fix_branch_child on an empty branch");
        debug_assert!(child_idx <= len, "child index out of range");

        let branch_lost_child = match node::tag(b.child(child_idx)) {
            NodeTag::Leaf => self.rebalance_leaf_child(branch, child_idx, len),
            NodeTag::Branch => self.rebalance_branch_child(branch, child_idx, len),
        };
        branch_lost_child && len - 1 < self.min_branch_len()
    }

    /// Restore minimum fill for `children[child_idx]` after a removal:
    /// borrow from a sibling that can spare an entry, else merge with one.
    /// `rebalance_branch_child` is its structural twin; both defer the
    /// decision to `plan_rebalance` and only supply the leaf or branch
    /// flavour of each repair. Returns whether the repair merged two children
    /// and therefore removed one entry from their parent branch.
    /// Lean: `fixBranchChild_spec` (`Proofs/Delete.lean`) dispatches on
    /// `planRebalance_spec` to the four leaf repairs' `_window` lemmas.
    unsafe fn rebalance_leaf_child(
        &mut self,
        branch: NonNull<u8>,
        child_idx: usize,
        branch_len: usize,
    ) -> bool {
        #[cfg(feature = "delete_profile")]
        {
            self.delete_profile.leaf_rebalance_checks += 1;
        }

        let repair = self.plan_rebalance(branch, child_idx, branch_len, self.min_leaf_len());
        match repair {
            Rebalance::BorrowFromLeft => self.rotate_leaf_right(branch, child_idx - 1),
            Rebalance::BorrowFromRight => self.rotate_leaf_left(branch, child_idx),
            Rebalance::MergeWithLeft => self.merge_leaf_pair(branch, child_idx - 1),
            Rebalance::MergeWithRight => self.merge_leaf_pair(branch, child_idx),
        }
        repair.merges_siblings()
    }

    /// Structural twin of `rebalance_leaf_child`, with the same merge result.
    /// Lean: the branch half of `fixBranchChild_spec`.
    unsafe fn rebalance_branch_child(
        &mut self,
        branch: NonNull<u8>,
        child_idx: usize,
        branch_len: usize,
    ) -> bool {
        #[cfg(feature = "delete_profile")]
        {
            self.delete_profile.branch_rebalance_checks += 1;
        }

        let repair = self.plan_rebalance(branch, child_idx, branch_len, self.min_branch_len());
        match repair {
            Rebalance::BorrowFromLeft => self.rotate_branch_right(branch, child_idx - 1),
            Rebalance::BorrowFromRight => self.rotate_branch_left(branch, child_idx),
            Rebalance::MergeWithLeft => self.merge_branch_pair(branch, child_idx - 1),
            Rebalance::MergeWithRight => self.merge_branch_pair(branch, child_idx),
        }
        repair.merges_siblings()
    }

    /// Decide how to refill the underfull `children[child_idx]`: prefer
    /// borrowing from a sibling that holds more than `min` (left first),
    /// else merge with the left sibling, else the right. Every sibling the
    /// plan looks at is present (`planRebalance_spec` and
    /// `fixBranchChild_spec` in `lean/BPlusTree/Proofs/Delete.lean`).
    unsafe fn plan_rebalance(
        &self,
        branch: NonNull<u8>,
        child_idx: usize,
        branch_len: usize,
        min: usize,
    ) -> Rebalance {
        let b = self.branch(branch);
        let has_left = child_idx > 0;
        let has_right = child_idx < branch_len;

        debug_assert!(
            node::len(b.child(child_idx)) < min,
            "child must be underfull"
        );
        if has_left && node::len(b.child(child_idx - 1)) > min {
            return Rebalance::BorrowFromLeft;
        }
        if has_right && node::len(b.child(child_idx + 1)) > min {
            return Rebalance::BorrowFromRight;
        }
        if has_left {
            return Rebalance::MergeWithLeft;
        }
        debug_assert!(has_right, "a child in a nonempty branch has a sibling");
        Rebalance::MergeWithRight
    }

    /// Rotate one entry rightward through separator `sep_idx`: the left
    /// child's last key moves up to the parent, the old separator moves down
    /// as the right child's first key, and the left child's last subtree
    /// travels with it. A pass-through: contrast the leaf rotations, which
    /// re-derive the separator from data.
    /// Lean: `rotateBranchRight_window` (`Proofs/Delete.lean`): both children
    /// well-formed afterwards, the new separator strictly between them;
    /// `rotateBranchRightH_sim` (`Proofs/HeapRemove.lean`) for the records.
    unsafe fn rotate_branch_right(&mut self, branch: NonNull<u8>, sep_idx: usize) {
        #[cfg(feature = "delete_profile")]
        {
            self.delete_profile.branch_borrows += 1;
        }

        let b = self.branch(branch);
        let l = self.branch(b.child(sep_idx));
        let r = self.branch(b.child(sep_idx + 1));
        debug_assert!(l.len() > 1, "donor would fall below minimum fill");

        let moved_child = l.child(l.len());
        let promoted = l.remove_entry(l.len() - 1);
        let old_sep = b.replace_key(sep_idx, promoted);
        r.push_front(old_sep, moved_child);
    }

    /// Mirror of `rotate_branch_right`: the right child's first key moves up,
    /// the old separator moves down as the left child's last key, and the
    /// right child's first subtree travels with it.
    /// Lean: `rotateBranchLeft_window`; `rotateBranchLeftH_sim` on the heap.
    unsafe fn rotate_branch_left(&mut self, branch: NonNull<u8>, sep_idx: usize) {
        #[cfg(feature = "delete_profile")]
        {
            self.delete_profile.branch_borrows += 1;
        }

        let b = self.branch(branch);
        let l = self.branch(b.child(sep_idx));
        let r = self.branch(b.child(sep_idx + 1));
        debug_assert!(r.len() > 1, "donor would fall below minimum fill");

        let (promoted, moved_child) = r.pop_front();
        let old_sep = b.replace_key(sep_idx, promoted);
        l.push_entry(old_sep, moved_child);
    }

    /// Merge the two children flanking separator `left_idx`:
    /// `children[left_idx]` absorbs `children[left_idx + 1]`, and the
    /// separator, taken out of the branch, moves down between them.
    /// Lean: `mergeBranchPair_window`; `mergeBranchPairH_sim` on the heap
    /// (the right child is freed, nothing else is).
    unsafe fn merge_branch_pair(&mut self, branch: NonNull<u8>, left_idx: usize) {
        let b = self.branch(branch);
        let left = b.child(left_idx);
        let right = b.child(left_idx + 1);

        let separator = b.remove_entry(left_idx);
        self.merge_branch_into(left, separator, right);
        self.free_emptied_branch(right);
    }

    /// Free an emptied branch's memory. Like `free_emptied_leaf`, the caller
    /// must already have moved or dropped every separator; use `empty_branch`
    /// for a branch that still owns its keys.
    unsafe fn free_emptied_branch(&mut self, node: NonNull<u8>) {
        debug_assert_eq!(
            node::len(node),
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
        self.branch(node).drop_keys();
    }

    /// Rotate one item rightward through separator `sep_idx`: the left
    /// child's last item becomes the right child's first. Leaves re-derive
    /// the separator from the right child's new first key (contrast the
    /// branch rotations, which pass the separator through).
    /// Lean: `rotateLeafRight_window` (`Proofs/Delete.lean`);
    /// `rotateLeafRightH_sim` (`Proofs/HeapRemove.lean`) on the heap.
    unsafe fn rotate_leaf_right(&mut self, branch: NonNull<u8>, sep_idx: usize) {
        #[cfg(feature = "delete_profile")]
        {
            self.delete_profile.leaf_borrows += 1;
        }

        let b = self.branch(branch);
        let l = self.leaf(b.child(sep_idx));
        let r = self.leaf(b.child(sep_idx + 1));
        debug_assert!(l.len() > 1, "donor would fall below minimum fill");

        let (key, value) = l.remove(l.len() - 1);
        r.insert(0, key, value);

        let new_sep = r.key(0).clone();
        drop(b.replace_key(sep_idx, new_sep));
    }

    /// Mirror of `rotate_leaf_right`: the right child's first item becomes
    /// the left child's last, and the separator is re-derived from the right
    /// child's new first key.
    /// Lean: `rotateLeafLeft_window`; `rotateLeafLeftH_sim` on the heap.
    unsafe fn rotate_leaf_left(&mut self, branch: NonNull<u8>, sep_idx: usize) {
        #[cfg(feature = "delete_profile")]
        {
            self.delete_profile.leaf_borrows += 1;
        }

        let b = self.branch(branch);
        let l = self.leaf(b.child(sep_idx));
        let r = self.leaf(b.child(sep_idx + 1));
        debug_assert!(r.len() > 1, "donor would fall below minimum fill");

        let (key, value) = r.remove(0);
        l.insert(l.len(), key, value);

        let new_sep = r.key(0).clone();
        drop(b.replace_key(sep_idx, new_sep));
    }

    /// Merge the two children flanking separator `left_idx`:
    /// `children[left_idx]` absorbs `children[left_idx + 1]`. Leaf keys carry
    /// their own ordering, so the separator is redundant and dropped.
    /// Lean: `mergeLeafPair_window`; `mergeLeafPairH_sim` on the heap (the
    /// right leaf is unlinked and freed, its successor's `prev` moves).
    unsafe fn merge_leaf_pair(&mut self, branch: NonNull<u8>, left_idx: usize) {
        let b = self.branch(branch);
        let left = b.child(left_idx);
        let right = b.child(left_idx + 1);

        self.merge_leaf_into(left, right);
        self.free_emptied_leaf(right);
        drop(b.remove_entry(left_idx));
    }

    /// Remove below `node`; on success, also report whether `node` became
    /// underfull and therefore needs repair by its parent.
    /// Lean: `removeRec_spec` (`Proofs/Delete.lean`): below the root the node
    /// is at most one short of minimum fill, and the flag is exact.
    /// `removeRecH_sim` (`Proofs/HeapRemove.lean`) is the same recursion on
    /// the heap model: ids only shrink, freed ids are exactly the dropped
    /// ones, and nothing outside the subtree changes.
    unsafe fn remove_rec<Q>(
        &mut self,
        node: NonNull<u8>,
        key: &Q,
        node_underflowed: &mut bool,
    ) -> Option<(K, V)>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        match node::tag(node) {
            NodeTag::Leaf => {
                let entry = self.leaf_remove(node, key)?;
                *node_underflowed = node::len(node) < self.min_leaf_len();
                Some(entry)
            }
            NodeTag::Branch => {
                let (child, idx) = self.child_for_key(node, key);
                let mut child_underflowed = false;
                let entry = self.remove_rec(child, key, &mut child_underflowed)?;
                *node_underflowed = child_underflowed && self.fix_branch_child(node, idx);
                Some(entry)
            }
        }
    }

    /// Lean: `leafRemove_spec` (`Proofs/Delete.lean`).
    unsafe fn leaf_remove<Q>(&mut self, leaf: NonNull<u8>, key: &Q) -> Option<(K, V)>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        let l = self.leaf(leaf);
        let idx = self.binary_search_keys(l.keys(), key).ok()?;
        Some(l.remove(idx))
    }
}
