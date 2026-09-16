use core::borrow::Borrow;

use crate::layout;
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
        let (parts, idx) = self.leaf_search(key)?;
        unsafe { Some(&*(parts.vals_ptr.add(idx) as *const V)) }
    }

    pub fn get_mut<Q>(&mut self, key: &Q) -> Option<&mut V>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        let (parts, idx) = self.leaf_search(key)?;
        unsafe { Some(&mut *(parts.vals_ptr.add(idx) as *mut V)) }
    }

    /// The stored key and its value. One descent: both come from the slot
    /// the search landed on.
    pub fn get_key_value<Q>(&self, key: &Q) -> Option<(&K, &V)>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        let (parts, idx) = self.leaf_search(key)?;
        unsafe {
            Some((
                &*(parts.keys_ptr.add(idx) as *const K),
                &*(parts.vals_ptr.add(idx) as *const V),
            ))
        }
    }

    pub fn contains_key<Q>(&self, key: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.leaf_search(key).is_some()
    }

    /// Lean: `leafSearch_some` and `leafSearch_none` (`Proofs/Read.lean`).
    pub(crate) fn leaf_search<Q>(&self, key: &Q) -> Option<(layout::LeafParts<K, V>, usize)>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        let leaf = self.leaf_for_key(key)?;
        unsafe {
            let parts = layout::carve_leaf::<K, V>(leaf, &self.leaf_layout);
            let len = (*parts.hdr).len as usize;
            let keys = core::slice::from_raw_parts(parts.keys_ptr as *const K, len);
            let idx = self.binary_search_keys(keys, key).ok()?;
            Some((parts, idx))
        }
    }
}
