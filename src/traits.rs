//! The trait impls `std::collections::BTreeMap` carries.

use core::borrow::Borrow;
use core::cmp::Ordering;
use core::fmt;
use core::hash::{Hash, Hasher};
use core::ops::Index;

use crate::iterate::{Iter, IterMut};
use crate::owned::IntoIter;
use crate::BPlusTreeMap;

impl<K: Ord + Clone, V> Default for BPlusTreeMap<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K: Ord + Clone, V: Clone> Clone for BPlusTreeMap<K, V> {
    /// Entries are re-inserted in key order, which is the tree's cheapest
    /// insertion path: every insert lands at the end of the last leaf.
    fn clone(&self) -> Self {
        let mut out = self.empty_like();
        for (key, value) in self.iter() {
            out.insert(key.clone(), value.clone());
        }
        out
    }
}

impl<K: Ord + Clone + fmt::Debug, V: fmt::Debug> fmt::Debug for BPlusTreeMap<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

impl<K: Ord + Clone, V: PartialEq> PartialEq for BPlusTreeMap<K, V> {
    fn eq(&self, other: &Self) -> bool {
        self.len() == other.len() && self.iter().eq(other.iter())
    }
}

impl<K: Ord + Clone, V: Eq> Eq for BPlusTreeMap<K, V> {}

impl<K: Ord + Clone, V: PartialOrd> PartialOrd for BPlusTreeMap<K, V> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.iter().partial_cmp(other.iter())
    }
}

impl<K: Ord + Clone, V: Ord> Ord for BPlusTreeMap<K, V> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.iter().cmp(other.iter())
    }
}

impl<K: Ord + Clone + Hash, V: Hash> Hash for BPlusTreeMap<K, V> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write_usize(self.len());
        for entry in self.iter() {
            entry.hash(state);
        }
    }
}

impl<K: Ord + Clone, V> FromIterator<(K, V)> for BPlusTreeMap<K, V> {
    fn from_iter<I: IntoIterator<Item = (K, V)>>(iter: I) -> Self {
        let mut out = Self::new();
        out.extend(iter);
        out
    }
}

impl<K: Ord + Clone, V> Extend<(K, V)> for BPlusTreeMap<K, V> {
    fn extend<I: IntoIterator<Item = (K, V)>>(&mut self, iter: I) {
        for (key, value) in iter {
            self.insert(key, value);
        }
    }
}

impl<'a, K: Ord + Clone + Copy, V: Copy> Extend<(&'a K, &'a V)> for BPlusTreeMap<K, V> {
    fn extend<I: IntoIterator<Item = (&'a K, &'a V)>>(&mut self, iter: I) {
        for (key, value) in iter {
            self.insert(*key, *value);
        }
    }
}

impl<K: Ord + Clone, V, const N: usize> From<[(K, V); N]> for BPlusTreeMap<K, V> {
    fn from(entries: [(K, V); N]) -> Self {
        entries.into_iter().collect()
    }
}

impl<K, Q, V> Index<&Q> for BPlusTreeMap<K, V>
where
    K: Ord + Clone + Borrow<Q>,
    Q: Ord + ?Sized,
{
    type Output = V;

    /// Panics if the key is not present.
    fn index(&self, key: &Q) -> &V {
        self.get(key).expect("no entry found for key")
    }
}

impl<'a, K: Ord + Clone, V> IntoIterator for &'a BPlusTreeMap<K, V> {
    type Item = (&'a K, &'a V);
    type IntoIter = Iter<'a, K, V>;

    fn into_iter(self) -> Iter<'a, K, V> {
        self.iter()
    }
}

impl<'a, K: Ord + Clone, V> IntoIterator for &'a mut BPlusTreeMap<K, V> {
    type Item = (&'a K, &'a mut V);
    type IntoIter = IterMut<'a, K, V>;

    fn into_iter(self) -> IterMut<'a, K, V> {
        self.iter_mut()
    }
}

impl<K: Ord + Clone, V> IntoIterator for BPlusTreeMap<K, V> {
    type Item = (K, V);
    type IntoIter = IntoIter<K, V>;

    /// The map's nodes are handed to the iterator, which walks the leaf
    /// chain and frees each leaf as it is emptied.
    fn into_iter(mut self) -> IntoIter<K, V> {
        // `new` takes the nodes and empties the map, so dropping `self`
        // here frees nothing.
        IntoIter::new(&mut self)
    }
}
