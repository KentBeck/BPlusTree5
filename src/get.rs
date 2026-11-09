use core::borrow::Borrow;

use crate::node::LeafRef;
use crate::BPlusTreeMap;

impl<K: Ord + Clone, V> BPlusTreeMap<K, V> {
    /// Lean: `getTree_spec` (`Proofs/Read.lean`): `Some(v)` exactly when
    /// `(key, v)` is one of the tree's entries; `getH_sim`
    /// (`Proofs/HeapRead.lean`) for the same descent over node ids.
    pub fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        let (leaf, idx) = self.leaf_search(key)?;
        Some(leaf.val(idx))
    }

    pub fn get_mut<Q>(&mut self, key: &Q) -> Option<&mut V>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        let (leaf, idx) = self.leaf_search(key)?;
        unsafe { Some(&mut *leaf.val_ptr(idx)) }
    }

    /// The stored key and its value. One descent: both come from the slot
    /// the search landed on.
    pub fn get_key_value<Q>(&self, key: &Q) -> Option<(&K, &V)>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        let (leaf, idx) = self.leaf_search(key)?;
        Some((leaf.key(idx), leaf.val(idx)))
    }

    pub fn contains_key<Q>(&self, key: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.leaf_search(key).is_some()
    }

    /// The leaf holding `key` and the key's index in it.
    /// Lean: `leafSearch_some` and `leafSearch_none` (`Proofs/Read.lean`).
    pub(crate) fn leaf_search<Q>(&self, key: &Q) -> Option<(LeafRef<K, V>, usize)>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        let leaf = self.leaf_for_key(key)?;
        unsafe {
            let leaf = self.leaf(leaf);
            let idx = self.binary_search_keys(leaf.keys(), key).ok()?;
            Some((leaf, idx))
        }
    }
}
