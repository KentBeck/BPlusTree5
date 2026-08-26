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
        // 64 levels is unreachable for any branch fanout >= 2.
        const MAX_DEPTH: usize = 64;

        let root = match self.root {
            Some(p) => p,
            None => unsafe { alloc_leaf_block(&self.leaf_layout).expect("alloc leaf") },
        };
        if self.root.is_none() {
            self.root = Some(root);
        }

        unsafe {
            // Iterative descent, recording (branch, child_idx) for the way up.
            let mut path: [core::mem::MaybeUninit<(NonNull<u8>, usize)>; MAX_DEPTH] =
                [core::mem::MaybeUninit::uninit(); MAX_DEPTH];
            let mut depth = 0usize;
            let mut node = root;
            loop {
                let hdr = &*(node.as_ptr() as *const NodeHdr);
                match hdr.tag {
                    NodeTag::Leaf => break,
                    NodeTag::Branch => {
                        let (child, child_idx) =
                            self.child_for_key(node, &key).expect("child must exist");
                        debug_assert!(depth < MAX_DEPTH);
                        path[depth].write((node, child_idx));
                        depth += 1;
                        node = child;
                    }
                }
            }

            let mut res = self.leaf_insert_or_split(node, key, value);

            // Apply split fixups bottom-up; stop as soon as a level absorbs it.
            while depth > 0 {
                match res {
                    InsertResult::NoSplit(old) => return old,
                    InsertResult::Split {
                        sep_key,
                        right,
                        old_value,
                    } => {
                        depth -= 1;
                        let (branch, child_idx) = path[depth].assume_init();
                        res = self.branch_apply_split(branch, child_idx, sep_key, right, old_value);
                    }
                }
            }

            match res {
                InsertResult::NoSplit(old) => old,
                InsertResult::Split {
                    sep_key,
                    right,
                    old_value,
                } => {
                    // The root itself split: grow the tree by one level.
                    let old_root = self.root.expect("root exists");
                    let branch =
                        alloc_branch_block(&self.branch_layout).expect("alloc new root branch");
                    let b = layout::carve_branch::<K>(branch, &self.branch_layout);
                    let bhdr = &mut *b.hdr;
                    bhdr.len = 1;
                    self.write_key_at(b.keys_ptr as *mut K, 0, sep_key);
                    let c0 = b.children_ptr as *mut *mut u8;
                    let c1 = c0.add(1);
                    *c0 = old_root.as_ptr();
                    *c1 = right.as_ptr();
                    self.root = Some(branch);
                    old_value
                }
            }
        }
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
    #[inline(always)]
    unsafe fn shift_and_write(
        &self,
        keys_ptr: *mut K,
        vals_ptr: *mut V,
        idx: usize,
        cur_len: usize,
        key: K,
        value: V,
    ) {
        self.shift_right(keys_ptr, vals_ptr, idx, cur_len);
        self.write_kv_at(keys_ptr, vals_ptr, idx, key, value);
    }

    unsafe fn leaf_insert_or_split(
        &mut self,
        leaf: NonNull<u8>,
        key: K,
        value: V,
    ) -> InsertResult<K, V> {
        let parts = layout::carve_leaf::<K, V>(leaf, &self.leaf_layout);
        let hdr = &mut *parts.hdr;
        let len = hdr.len as usize;
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
                    InsertResult::NoSplit(None)
                } else {
                    // Zero-allocation in-place split: move the upper half to the right
                    // leaf and insert the new item. Moved-from slots stay
                    // physically populated; each node's hdr.len excludes them.
                    let total_items = len + 1;
                    let left_count = total_items / 2;
                    let right_count = total_items - left_count;

                    // Determine insertion position (idx from Err was computed above as `idx`)
                    let insert_pos = idx;

                    // Allocate right node and carve
                    let right = alloc_leaf_block(&self.leaf_layout).expect("alloc right leaf");
                    let r = layout::carve_leaf::<K, V>(right, &self.leaf_layout);

                    // Decide how many existing items remain on the left before insertion
                    let left_keep = if insert_pos < left_count {
                        left_count - 1
                    } else {
                        left_count
                    };

                    // Move items [left_keep..len) to the right leaf: the
                    // inverse of merge_leaf_into.
                    let move_count = len - left_keep;
                    self.move_kv_range(
                        parts.keys_ptr as *const K,
                        parts.vals_ptr as *const V,
                        left_keep,
                        r.keys_ptr as *mut K,
                        r.vals_ptr as *mut V,
                        0,
                        move_count,
                    );
                    let right_len = move_count;

                    // Insert new item into the correct side
                    if insert_pos < left_count {
                        // Insert into left: shift [insert_pos..left_keep) right by 1, then write
                        self.shift_and_write(
                            parts.keys_ptr as *mut K,
                            parts.vals_ptr as *mut V,
                            insert_pos,
                            left_keep,
                            key,
                            value,
                        );
                        // Left now has left_count items; right already has right_count
                        hdr.len = left_count as u16;
                        (*r.hdr).len = right_count as u16;
                    } else {
                        // Insert into right
                        let right_insert = insert_pos - left_keep; // position within right
                        self.shift_and_write(
                            r.keys_ptr as *mut K,
                            r.vals_ptr as *mut V,
                            right_insert,
                            right_len,
                            key,
                            value,
                        );
                        hdr.len = left_keep as u16; // equals left_count
                        (*r.hdr).len = (right_len + 1) as u16; // equals right_count
                    }

                    self.link_leaf_after(leaf, right);

                    let sep = self.key_clone_at(r.keys_ptr as *const K, 0);
                    InsertResult::Split {
                        sep_key: sep,
                        right,
                        old_value: None,
                    }
                }
            }
        }
    }
}
