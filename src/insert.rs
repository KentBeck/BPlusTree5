use core::ptr::NonNull;

use crate::layout::NodeTag;
use crate::node;
use crate::node_alloc::{alloc_branch_block, alloc_leaf_block};
use crate::BPlusTreeMap;

pub(crate) enum InsertResult<K, V> {
    NoSplit(Option<V>),
    Split {
        sep_key: K,
        right: NonNull<u8>,
        old_value: Option<V>,
    },
}

impl<K: Ord + Clone, V> BPlusTreeMap<K, V> {
    /// Lean: `insertTree_wf` and `insertTree_toList` (`Proofs/Tree.lean`): the
    /// tree stays well-formed, its entries become `insertSorted k v` of the
    /// old ones, and the returned value is the one stored under `key`;
    /// `Map.insert_wf` (`Proofs/Check.lean`) carries `entry_count` along.
    /// On the heap model, `insertH_sim` (`Proofs/Heap.lean`): no fault, the
    /// store holds exactly the reachable nodes, the sibling chain intact.
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        self.insert_at(key, value).1
    }

    /// Insert, and also hand back a pointer to the value's slot.
    ///
    /// The entry API uses this so that filling a vacant entry costs one
    /// descent instead of an insert followed by a lookup. The pointer stays
    /// valid until the next mutation: a leaf split moves the value into
    /// whichever half it sorts into before this returns, and the branch
    /// splits above a leaf never touch leaf payloads.
    pub(crate) fn insert_at(&mut self, key: K, value: V) -> (*mut V, Option<V>) {
        let (slot, old_value) = self.insert_inner(key, value);
        if old_value.is_none() {
            self.entry_count += 1;
        }
        (slot, old_value)
    }

    fn insert_inner(&mut self, key: K, value: V) -> (*mut V, Option<V>) {
        let root = match self.root {
            Some(p) => p,
            None => unsafe { alloc_leaf_block(&self.leaf_layout).expect("alloc leaf") },
        };
        if self.root.is_none() {
            self.root = Some(root);
        }

        let mut slot: *mut V = core::ptr::null_mut();
        let old_value = match unsafe { self.insert_rec(root, key, value, &mut slot) } {
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
        };
        debug_assert!(!slot.is_null(), "every insert lands in some leaf slot");
        (slot, old_value)
    }

    /// Insert below `node`; on a split, hand the separator and new right
    /// sibling up for the parent to absorb. Mirror of `remove_rec`: descend
    /// on the way down, repair on the way up. Depth is logarithmic in the
    /// entry count (non-root branches hold at least two keys), so the
    /// recursion is shallow.
    /// Lean: `insertRec_wf` and `insertRec_toList` (`Proofs/Tree.lean`), with
    /// `front_lt_of_route` for the descent through `child_for_key`;
    /// `insertRecH_sim` (`Proofs/Heap.lean`) is the same recursion on the heap.
    unsafe fn insert_rec(
        &mut self,
        node: NonNull<u8>,
        key: K,
        value: V,
        slot: &mut *mut V,
    ) -> InsertResult<K, V> {
        match node::tag(node) {
            NodeTag::Leaf => self.leaf_insert_or_split(node, key, value, slot),
            NodeTag::Branch => {
                let (child, child_idx) = self.child_for_key(node, &key);
                match self.insert_rec(child, key, value, slot) {
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
    /// Lean: `growRoot_spec` (`Proofs/Branch.lean`); `insertTree_wf` shows the
    /// result well-formed one level higher.
    unsafe fn grow_root(&mut self, old_root: NonNull<u8>, sep_key: K, right: NonNull<u8>) {
        let branch = alloc_branch_block(&self.branch_layout).expect("alloc new root branch");
        let b = self.branch(branch);
        b.set_child(0, old_root);
        b.push_entry(sep_key, right);
        self.root = Some(branch);
    }

    /// Absorb a child split into `node` at `child_idx`: insert the separator
    /// and right-sibling pointer, splitting this branch too if it is full.
    /// Lean: `branchApplySplit_noSplit` and `branchApplySplit_split`
    /// (`Proofs/Branch.lean`); the separator fits strictly between its
    /// neighbours by `sepFits_of_strict` (`Proofs/Tree.lean`).
    unsafe fn branch_apply_split(
        &mut self,
        node: NonNull<u8>,
        child_idx: usize,
        sep_key: K,
        right: NonNull<u8>,
        old_value: Option<V>,
    ) -> InsertResult<K, V> {
        let b = self.branch(node);
        if !b.is_full() {
            b.insert_entry(child_idx, sep_key, right);
            InsertResult::NoSplit(old_value)
        } else {
            self.branch_insert_and_split(node, child_idx, sep_key, right, old_value)
        }
    }

    /// Lean: `cutInsert_eq` (`Proofs/Branch.lean`) shows the `left_keep`
    /// arithmetic below equals "insert, then cut at `(len + 1) / 2`", and
    /// `branchApplySplit_split` gives both halves between `cap / 2` and `cap`
    /// with the promoted key strictly between them, for every `cap >= 1`.
    unsafe fn branch_insert_and_split(
        &mut self,
        node: NonNull<u8>,
        insert_idx: usize,
        ins_key: K,
        ins_right: NonNull<u8>,
        old_value: Option<V>,
    ) -> InsertResult<K, V> {
        let b = self.branch(node);
        let len = b.len();

        let right_node = alloc_branch_block(&self.branch_layout).expect("alloc right branch");
        let rb = self.branch(right_node);

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
        b.split_tail_to(left_keep, rb);

        // Insert the new entry into whichever side it sorts into.
        if insert_idx < left_count {
            b.insert_entry(insert_idx, ins_key, ins_right);
        } else {
            rb.insert_entry(insert_idx - left_keep, ins_key, ins_right);
        }

        // Promote the boundary: the right node's first entry's key goes up,
        // and its child becomes the right node's leftmost child (the same
        // close-slot-0 move as rotate_branch_left's pop).
        let sep_key = rb.pop_front_key();

        InsertResult::Split {
            sep_key,
            right: right_node,
            old_value,
        }
    }

    /// Lean: `leafInsertOrSplit_noSplit` and `leafInsertOrSplit_split`
    /// (`Proofs/Leaf.lean`) for the shapes; `leafInsertOrSplit_noSplit_eq` and
    /// `leafInsertOrSplit_split_eq` (`Proofs/Spec.lean`) for the entries.
    unsafe fn leaf_insert_or_split(
        &mut self,
        leaf: NonNull<u8>,
        key: K,
        value: V,
        slot: &mut *mut V,
    ) -> InsertResult<K, V> {
        let l = self.leaf(leaf);
        match self.binary_search_keys(l.keys(), &key) {
            Ok(idx) => {
                let old = l.replace_val(idx, value);
                *slot = l.val_ptr(idx);
                InsertResult::NoSplit(Some(old))
            }
            Err(idx) => {
                if !l.is_full() {
                    *slot = l.insert(idx, key, value);
                    return InsertResult::NoSplit(None);
                }

                // The leaf is full: split it first, then run the ordinary
                // insert on whichever half the key sorts into. A key below
                // the separator keeps its slot in the left half; a key
                // above it lands in the right half past slot 0, so the
                // separator read at the split stays the right half's first
                // key.
                let (right, sep) = self.split_leaf(leaf);
                let left_len = l.len();
                *slot = if key < sep {
                    l.insert(idx, key, value)
                } else {
                    self.leaf(right).insert(idx - left_len, key, value)
                };
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
    /// Lean: `leafSplit_*` and `leafInsertOrSplit_split` (`Proofs/Leaf.lean`):
    /// both halves hold between `cap / 2` and `cap` items for every `cap >= 2`.
    unsafe fn split_leaf(&mut self, leaf: NonNull<u8>) -> (NonNull<u8>, K) {
        let l = self.leaf(leaf);
        let len = l.len();
        let left_len = (len + 1) / 2;

        let right = alloc_leaf_block(&self.leaf_layout).expect("alloc right leaf");
        let r = self.leaf(right);
        // Moved-from slots stay physically populated; hdr.len excludes them.
        l.move_tail_to(left_len, r, 0, len - left_len);
        self.link_leaf_after(leaf, right);

        let sep = r.key(0).clone();
        (right, sep)
    }
}
