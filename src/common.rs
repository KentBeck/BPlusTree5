use core::borrow::Borrow;
use core::ptr::NonNull;

use crate::layout::NodeTag;
use crate::node::{self, BranchRef, LeafRef};
use crate::BPlusTreeMap;

impl<K, V> BPlusTreeMap<K, V> {
    /// View `node` as a leaf of this map.
    ///
    /// SAFETY: `node` must be a live leaf of this map; see [`LeafRef::new`].
    #[inline(always)]
    pub(crate) unsafe fn leaf(&self, node: NonNull<u8>) -> LeafRef<K, V> {
        LeafRef::new(node, &self.leaf_layout)
    }

    /// View `node` as a branch of this map.
    ///
    /// SAFETY: `node` must be a live branch of this map; see
    /// [`BranchRef::new`].
    #[inline(always)]
    pub(crate) unsafe fn branch(&self, node: NonNull<u8>) -> BranchRef<K> {
        BranchRef::new(node, &self.branch_layout)
    }

    /// Number of keys a node currently holds. The header is shared by both
    /// node kinds, so this works for leaves and branches alike.
    #[inline(always)]
    pub(crate) unsafe fn node_len(&self, node: NonNull<u8>) -> usize {
        node::len(node)
    }

    /// Centralized binary search for keys in a node.
    /// This function will be optimized for performance in future iterations.
    #[inline(always)]
    pub(crate) fn binary_search_keys<T, Q>(&self, keys: &[T], target: &Q) -> Result<usize, usize>
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        keys.binary_search_by(|k| k.borrow().cmp(target))
    }

    /// Splice `new_right` into the leaf chain immediately after `leaf`.
    /// Inverse of `unlink_leaf`; the two are the only places that edit the
    /// sibling chain, so the doubly-linked invariant is auditable here.
    #[inline]
    pub(crate) unsafe fn link_leaf_after(&self, leaf: NonNull<u8>, new_right: NonNull<u8>) {
        let l = self.leaf(leaf);
        let r = self.leaf(new_right);
        let old_next = l.next();

        l.set_next(Some(new_right));
        r.set_next(old_next);
        r.set_prev(Some(leaf));
        if let Some(old) = old_next {
            self.leaf(old).set_prev(Some(new_right));
        }
    }

    /// Splice `leaf` out of the leaf chain and clear its own links.
    /// Inverse of `link_leaf_after`.
    #[inline]
    pub(crate) unsafe fn unlink_leaf(&self, leaf: NonNull<u8>) {
        let l = self.leaf(leaf);
        let next = l.next();
        let prev = l.prev();

        if let Some(prev_leaf) = prev {
            self.leaf(prev_leaf).set_next(next);
        }
        if let Some(next_leaf) = next {
            self.leaf(next_leaf).set_prev(prev);
        }

        l.set_next(None);
        l.set_prev(None);
    }
}

impl<K: Ord, V> BPlusTreeMap<K, V> {
    /// The child after the separators `<= key`. Lean: `lastChild` of the
    /// `sepLE` prefix, the descent `insertRec`, `removeRec` and `leafForKey`
    /// share; `front_lt_of_route` (`Proofs/Tree.lean`) is what it guarantees.
    /// The slot is never null: a branch holds `len + 1` children and the
    /// index is at most `len`, and on the heap model the same descent never
    /// meets a missing node (`insertRecH_sim`, `removeRecH_sim`,
    /// `leafForKeyH_sim`).
    #[inline(always)]
    pub(crate) unsafe fn child_for_key<Q>(
        &self,
        branch: NonNull<u8>,
        key: &Q,
    ) -> (NonNull<u8>, usize)
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        let b = self.branch(branch);
        let child_idx = match self.binary_search_keys(b.keys(), key) {
            Ok(i) => i + 1,
            Err(i) => i,
        };
        debug_assert!(child_idx <= b.len(), "child index out of range");
        (b.child(child_idx), child_idx)
    }

    /// Lean: `leafForKey_spec` (`Proofs/Read.lean`): the entries split into
    /// those before this leaf (all below `key`), the leaf, and those after
    /// (all above), so any entry with this key is in the leaf reached.
    /// Lean: `leafForKeyH_sim` (`Proofs/HeapRead.lean`): the leaf reached
    /// splits the sibling chain where `leafForKey` splits the entries.
    #[inline(always)]
    pub(crate) fn leaf_for_key<Q>(&self, key: &Q) -> Option<NonNull<u8>>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        let mut cur = self.root?;
        unsafe {
            loop {
                match node::tag(cur) {
                    NodeTag::Leaf => return Some(cur),
                    NodeTag::Branch => cur = self.child_for_key(cur, key).0,
                }
            }
        }
    }

    /// Lean: `leftmostLeaf_spec` (`Proofs/Read.lean`): it starts the entry
    /// list and is nonempty unless it is the root.
    #[inline]
    pub(crate) fn leftmost_leaf(&self) -> Option<NonNull<u8>> {
        let mut cur = self.root?;
        unsafe {
            loop {
                match node::tag(cur) {
                    NodeTag::Leaf => return Some(cur),
                    NodeTag::Branch => cur = self.branch(cur).child_or_null(0)?,
                }
            }
        }
    }
}

impl<K: Ord + Clone, V> BPlusTreeMap<K, V> {
    /// Lean: `rightmostLeaf_spec` (`Proofs/Read.lean`), the mirror image.
    #[inline]
    pub(crate) fn rightmost_leaf(&self) -> Option<NonNull<u8>> {
        let mut cur = self.root?;
        unsafe {
            loop {
                match node::tag(cur) {
                    NodeTag::Leaf => return Some(cur),
                    NodeTag::Branch => {
                        let b = self.branch(cur);
                        cur = b.child_or_null(b.len())?;
                    }
                }
            }
        }
    }

    /// Lean: `minLeafLen`, the leaf fill `WF` requires below the root.
    #[inline(always)]
    pub(crate) fn min_leaf_len(&self) -> usize {
        let cap = self.leaf_layout.cap as usize;
        cap / 2
    }

    /// Lean: `minBranchLen_eq` (`Proofs/Delete.lean`): for `cap >= 3` this is
    /// `cap / 2`, the branch fill `WF` requires; `with_caps` enforces 4, so
    /// the `cap <= 2` arm is unreachable.
    #[inline(always)]
    pub(crate) fn min_branch_len(&self) -> usize {
        let cap = self.branch_layout.cap as usize;
        if cap <= 2 {
            1
        } else {
            cap / 2
        }
    }
}
