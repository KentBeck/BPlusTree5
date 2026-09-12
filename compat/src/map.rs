use core::borrow::Borrow;
use core::cmp::Ordering;
use core::fmt;
use core::hash::{Hash, Hasher};
use core::ops::{Bound, Index, RangeBounds};

use bplustree::BPlusTreeMap;

/// Ordered map with the `std::collections::BTreeMap` API, stored in a
/// [`BPlusTreeMap`].
///
/// Node capacities come from [`BPlusTreeMap::recommended`], which sizes
/// leaves and branches to fixed byte budgets for the given `K` and `V`.
pub struct BTreeMap<K, V> {
    inner: BPlusTreeMap<K, V>,
}

impl<K: Ord + Clone, V> BTreeMap<K, V> {
    /// An empty map. Nothing is allocated until the first insert.
    ///
    /// Leaf and branch capacities come from
    /// [`BPlusTreeMap::recommended`].
    pub fn new() -> Self {
        Self {
            inner: BPlusTreeMap::recommended().expect("recommended capacities are always valid"),
        }
    }

    /// An empty map whose leaves and branches hold `capacity` slots each.
    pub fn with_node_capacity(capacity: usize) -> Self {
        Self {
            inner: BPlusTreeMap::new(capacity).expect("invalid node capacity"),
        }
    }

    /// The tree underneath, for callers that want the native API.
    pub fn as_tree(&self) -> &BPlusTreeMap<K, V> {
        &self.inner
    }

    pub fn as_tree_mut(&mut self) -> &mut BPlusTreeMap<K, V> {
        &mut self.inner
    }

    pub fn len(&self) -> usize {
        self.inner.len()
    }

    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    pub fn clear(&mut self) {
        self.inner.clear()
    }

    pub fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.inner.get(key)
    }

    pub fn get_key_value<Q>(&self, key: &Q) -> Option<(&K, &V)>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.inner
            .range((Bound::Included(key), Bound::Included(key)))
            .next()
    }

    pub fn get_mut<Q>(&mut self, key: &Q) -> Option<&mut V>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.inner.get_mut(key)
    }

    pub fn contains_key<Q>(&self, key: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.inner.contains_key(key)
    }

    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        self.inner.insert(key, value)
    }

    pub fn remove<Q>(&mut self, key: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.inner.remove(key)
    }

    /// Two descents: one to clone the stored key, one to remove it.
    pub fn remove_entry<Q>(&mut self, key: &Q) -> Option<(K, V)>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        let k = self.get_key_value(key)?.0.clone();
        let v = self.inner.remove(key)?;
        Some((k, v))
    }

    pub fn iter(&self) -> Iter<'_, K, V> {
        Iter {
            inner: self.inner.items(),
            remaining: self.inner.len(),
        }
    }

    pub fn iter_mut(&mut self) -> IterMut<'_, K, V> {
        let remaining = self.inner.len();
        IterMut {
            inner: self.inner.items_mut(),
            remaining,
        }
    }

    pub fn keys(&self) -> Keys<'_, K, V> {
        Keys { inner: self.iter() }
    }

    pub fn values(&self) -> Values<'_, K, V> {
        Values { inner: self.iter() }
    }

    pub fn values_mut(&mut self) -> ValuesMut<'_, K, V> {
        ValuesMut {
            inner: self.iter_mut(),
        }
    }

    pub fn range<Q, R>(&self, range: R) -> Range<'_, K, V>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
        R: RangeBounds<Q>,
    {
        Range {
            inner: self.inner.range(range),
        }
    }

    pub fn range_mut<Q, R>(&mut self, range: R) -> RangeMut<'_, K, V>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
        R: RangeBounds<Q>,
    {
        RangeMut {
            inner: self.inner.range_mut(range),
        }
    }

    pub fn first_key_value(&self) -> Option<(&K, &V)> {
        self.inner.first()
    }

    pub fn last_key_value(&self) -> Option<(&K, &V)> {
        self.inner.last()
    }

    /// Clones the first key, then removes it: two descents.
    pub fn pop_first(&mut self) -> Option<(K, V)> {
        let k = self.inner.first()?.0.clone();
        let v = self.inner.remove(&k)?;
        Some((k, v))
    }

    /// Clones the last key, then removes it: two descents.
    pub fn pop_last(&mut self) -> Option<(K, V)> {
        let k = self.inner.last()?.0.clone();
        let v = self.inner.remove(&k)?;
        Some((k, v))
    }

    pub fn first_entry(&mut self) -> Option<OccupiedEntry<'_, K, V>> {
        let key = self.inner.first()?.0.clone();
        Some(OccupiedEntry { map: self, key })
    }

    pub fn last_entry(&mut self) -> Option<OccupiedEntry<'_, K, V>> {
        let key = self.inner.last()?.0.clone();
        Some(OccupiedEntry { map: self, key })
    }

    /// The entry stores the key and re-descends on each use; it is a
    /// convenience, not a cursor.
    pub fn entry(&mut self, key: K) -> Entry<'_, K, V> {
        if self.inner.contains_key(&key) {
            Entry::Occupied(OccupiedEntry { map: self, key })
        } else {
            Entry::Vacant(VacantEntry { map: self, key })
        }
    }

    /// One pass to find the rejected keys, then one removal per key.
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&K, &mut V) -> bool,
    {
        let doomed: Vec<K> = self
            .inner
            .items_mut()
            .filter_map(|(k, v)| (!f(k, v)).then(|| k.clone()))
            .collect();
        for k in &doomed {
            self.inner.remove(k);
        }
    }

    /// Moves every entry of `other` into `self`, one pop and insert each.
    pub fn append(&mut self, other: &mut Self) {
        while let Some((k, v)) = other.pop_first() {
            self.inner.insert(k, v);
        }
    }

    /// Moves every entry at or after `key` into a new map: the tail is
    /// popped off the back and inserted into the new map.
    pub fn split_off<Q>(&mut self, key: &Q) -> Self
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        let mut tail = Vec::new();
        while let Some((k, _)) = self.inner.last() {
            if k.borrow() < key {
                break;
            }
            let k: K = k.clone();
            let v = self.inner.remove::<K>(&k).expect("key just observed");
            tail.push((k, v));
        }
        let mut out = Self::new();
        for (k, v) in tail.into_iter().rev() {
            out.inner.insert(k, v);
        }
        out
    }

    pub fn into_keys(self) -> IntoKeys<K, V> {
        IntoKeys {
            inner: self.into_iter(),
        }
    }

    pub fn into_values(self) -> IntoValues<K, V> {
        IntoValues {
            inner: self.into_iter(),
        }
    }
}

impl<K: Ord + Clone, V> Default for BTreeMap<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K: Ord + Clone, V: Clone> Clone for BTreeMap<K, V> {
    fn clone(&self) -> Self {
        let mut out = Self {
            inner: BPlusTreeMap::with_caps(
                self.inner.leaf_layout().cap as usize,
                self.inner.branch_layout().cap as usize,
            )
            .expect("capacities came from a live map"),
        };
        for (k, v) in self.iter() {
            out.inner.insert(k.clone(), v.clone());
        }
        out
    }
}

impl<K: Ord + Clone + fmt::Debug, V: fmt::Debug> fmt::Debug for BTreeMap<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

impl<K: Ord + Clone, V: PartialEq> PartialEq for BTreeMap<K, V> {
    fn eq(&self, other: &Self) -> bool {
        self.len() == other.len() && self.iter().zip(other.iter()).all(|(a, b)| a == b)
    }
}

impl<K: Ord + Clone, V: Eq> Eq for BTreeMap<K, V> {}

impl<K: Ord + Clone, V: PartialOrd> PartialOrd for BTreeMap<K, V> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.iter().partial_cmp(other.iter())
    }
}

impl<K: Ord + Clone, V: Ord> Ord for BTreeMap<K, V> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.iter().cmp(other.iter())
    }
}

impl<K: Ord + Clone + Hash, V: Hash> Hash for BTreeMap<K, V> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write_usize(self.len());
        for kv in self.iter() {
            kv.hash(state);
        }
    }
}

impl<K: Ord + Clone, V> FromIterator<(K, V)> for BTreeMap<K, V> {
    fn from_iter<I: IntoIterator<Item = (K, V)>>(iter: I) -> Self {
        let mut out = Self::new();
        out.extend(iter);
        out
    }
}

impl<K: Ord + Clone, V> Extend<(K, V)> for BTreeMap<K, V> {
    fn extend<I: IntoIterator<Item = (K, V)>>(&mut self, iter: I) {
        for (k, v) in iter {
            self.inner.insert(k, v);
        }
    }
}

impl<'a, K: Ord + Clone, V: Clone> Extend<(&'a K, &'a V)> for BTreeMap<K, V> {
    fn extend<I: IntoIterator<Item = (&'a K, &'a V)>>(&mut self, iter: I) {
        for (k, v) in iter {
            self.inner.insert(k.clone(), v.clone());
        }
    }
}

impl<K: Ord + Clone, V, const N: usize> From<[(K, V); N]> for BTreeMap<K, V> {
    fn from(arr: [(K, V); N]) -> Self {
        arr.into_iter().collect()
    }
}

impl<K, Q, V> Index<&Q> for BTreeMap<K, V>
where
    K: Ord + Clone + Borrow<Q>,
    Q: Ord + ?Sized,
{
    type Output = V;

    fn index(&self, key: &Q) -> &V {
        self.get(key).expect("no entry found for key")
    }
}

impl<'a, K: Ord + Clone, V> IntoIterator for &'a BTreeMap<K, V> {
    type Item = (&'a K, &'a V);
    type IntoIter = Iter<'a, K, V>;

    fn into_iter(self) -> Iter<'a, K, V> {
        self.iter()
    }
}

impl<'a, K: Ord + Clone, V> IntoIterator for &'a mut BTreeMap<K, V> {
    type Item = (&'a K, &'a mut V);
    type IntoIter = IterMut<'a, K, V>;

    fn into_iter(self) -> IterMut<'a, K, V> {
        self.iter_mut()
    }
}

impl<K: Ord + Clone, V> IntoIterator for BTreeMap<K, V> {
    type Item = (K, V);
    type IntoIter = IntoIter<K, V>;

    /// Owned iteration pops entries off either end as it goes: one clone
    /// of the key plus one removal per item.
    fn into_iter(self) -> IntoIter<K, V> {
        IntoIter { map: self }
    }
}

// ----- iterators -----

pub struct Iter<'a, K, V> {
    inner: bplustree::Items<'a, K, V>,
    remaining: usize,
}

impl<'a, K: Ord, V> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        let item = self.inner.next()?;
        self.remaining -= 1;
        Some(item)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.remaining, Some(self.remaining))
    }
}

impl<'a, K: Ord, V> DoubleEndedIterator for Iter<'a, K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        let item = self.inner.next_back()?;
        self.remaining -= 1;
        Some(item)
    }
}

impl<'a, K: Ord, V> ExactSizeIterator for Iter<'a, K, V> {}

pub struct IterMut<'a, K, V> {
    inner: bplustree::ItemsMut<'a, K, V>,
    remaining: usize,
}

impl<'a, K: Ord, V> Iterator for IterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);

    fn next(&mut self) -> Option<Self::Item> {
        let item = self.inner.next()?;
        self.remaining -= 1;
        Some(item)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.remaining, Some(self.remaining))
    }
}

impl<'a, K: Ord, V> DoubleEndedIterator for IterMut<'a, K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        let item = self.inner.next_back()?;
        self.remaining -= 1;
        Some(item)
    }
}

impl<'a, K: Ord, V> ExactSizeIterator for IterMut<'a, K, V> {}

macro_rules! projecting_iter {
    ($name:ident, $inner:ident, $item:ty, |$kv:ident| $project:expr) => {
        pub struct $name<'a, K, V> {
            inner: $inner<'a, K, V>,
        }

        impl<'a, K: Ord, V> Iterator for $name<'a, K, V> {
            type Item = $item;

            fn next(&mut self) -> Option<Self::Item> {
                self.inner.next().map(|$kv| $project)
            }

            fn size_hint(&self) -> (usize, Option<usize>) {
                self.inner.size_hint()
            }
        }

        impl<'a, K: Ord, V> DoubleEndedIterator for $name<'a, K, V> {
            fn next_back(&mut self) -> Option<Self::Item> {
                self.inner.next_back().map(|$kv| $project)
            }
        }
    };
}

projecting_iter!(Keys, Iter, &'a K, |kv| kv.0);
projecting_iter!(Values, Iter, &'a V, |kv| kv.1);
projecting_iter!(ValuesMut, IterMut, &'a mut V, |kv| kv.1);

impl<'a, K: Ord, V> ExactSizeIterator for Keys<'a, K, V> {}
impl<'a, K: Ord, V> ExactSizeIterator for Values<'a, K, V> {}
impl<'a, K: Ord, V> ExactSizeIterator for ValuesMut<'a, K, V> {}

pub struct Range<'a, K, V> {
    inner: bplustree::Items<'a, K, V>,
}

impl<'a, K: Ord, V> Iterator for Range<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }
}

impl<'a, K: Ord, V> DoubleEndedIterator for Range<'a, K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner.next_back()
    }
}

pub struct RangeMut<'a, K, V> {
    inner: bplustree::ItemsMut<'a, K, V>,
}

impl<'a, K: Ord, V> Iterator for RangeMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }
}

impl<'a, K: Ord, V> DoubleEndedIterator for RangeMut<'a, K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner.next_back()
    }
}

pub struct IntoIter<K, V> {
    map: BTreeMap<K, V>,
}

impl<K: Ord + Clone, V> Iterator for IntoIter<K, V> {
    type Item = (K, V);

    fn next(&mut self) -> Option<Self::Item> {
        self.map.pop_first()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.map.len(), Some(self.map.len()))
    }
}

impl<K: Ord + Clone, V> DoubleEndedIterator for IntoIter<K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.map.pop_last()
    }
}

impl<K: Ord + Clone, V> ExactSizeIterator for IntoIter<K, V> {}

pub struct IntoKeys<K, V> {
    inner: IntoIter<K, V>,
}

impl<K: Ord + Clone, V> Iterator for IntoKeys<K, V> {
    type Item = K;

    fn next(&mut self) -> Option<K> {
        self.inner.next().map(|(k, _)| k)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

pub struct IntoValues<K, V> {
    inner: IntoIter<K, V>,
}

impl<K: Ord + Clone, V> Iterator for IntoValues<K, V> {
    type Item = V;

    fn next(&mut self) -> Option<V> {
        self.inner.next().map(|(_, v)| v)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

// ----- entry API -----

pub enum Entry<'a, K, V> {
    Vacant(VacantEntry<'a, K, V>),
    Occupied(OccupiedEntry<'a, K, V>),
}

pub struct VacantEntry<'a, K, V> {
    map: &'a mut BTreeMap<K, V>,
    key: K,
}

pub struct OccupiedEntry<'a, K, V> {
    map: &'a mut BTreeMap<K, V>,
    key: K,
}

impl<'a, K: Ord + Clone, V> Entry<'a, K, V> {
    pub fn or_insert(self, default: V) -> &'a mut V {
        match self {
            Entry::Occupied(e) => e.into_mut(),
            Entry::Vacant(e) => e.insert(default),
        }
    }

    pub fn or_insert_with<F: FnOnce() -> V>(self, default: F) -> &'a mut V {
        match self {
            Entry::Occupied(e) => e.into_mut(),
            Entry::Vacant(e) => e.insert(default()),
        }
    }

    pub fn or_insert_with_key<F: FnOnce(&K) -> V>(self, default: F) -> &'a mut V {
        match self {
            Entry::Occupied(e) => e.into_mut(),
            Entry::Vacant(e) => {
                let v = default(&e.key);
                e.insert(v)
            }
        }
    }

    pub fn or_default(self) -> &'a mut V
    where
        V: Default,
    {
        self.or_insert_with(V::default)
    }

    pub fn key(&self) -> &K {
        match self {
            Entry::Occupied(e) => e.key(),
            Entry::Vacant(e) => e.key(),
        }
    }

    pub fn and_modify<F: FnOnce(&mut V)>(self, f: F) -> Self {
        match self {
            Entry::Occupied(mut e) => {
                f(e.get_mut());
                Entry::Occupied(e)
            }
            Entry::Vacant(e) => Entry::Vacant(e),
        }
    }
}

impl<'a, K: Ord + Clone, V> VacantEntry<'a, K, V> {
    pub fn key(&self) -> &K {
        &self.key
    }

    pub fn into_key(self) -> K {
        self.key
    }

    /// Inserts, then descends again to hand back the slot.
    pub fn insert(self, value: V) -> &'a mut V {
        let key = self.key;
        self.map.inner.insert(key.clone(), value);
        self.map.inner.get_mut(&key).expect("just inserted")
    }
}

impl<'a, K: Ord + Clone, V> OccupiedEntry<'a, K, V> {
    pub fn key(&self) -> &K {
        &self.key
    }

    pub fn get(&self) -> &V {
        self.map.inner.get(&self.key).expect("occupied entry")
    }

    pub fn get_mut(&mut self) -> &mut V {
        self.map.inner.get_mut(&self.key).expect("occupied entry")
    }

    pub fn into_mut(self) -> &'a mut V {
        self.map.inner.get_mut(&self.key).expect("occupied entry")
    }

    pub fn insert(&mut self, value: V) -> V {
        core::mem::replace(self.get_mut(), value)
    }

    pub fn remove(self) -> V {
        self.map.inner.remove(&self.key).expect("occupied entry")
    }

    pub fn remove_entry(self) -> (K, V) {
        let v = self.map.inner.remove(&self.key).expect("occupied entry");
        (self.key, v)
    }
}

// ----- serde -----

#[cfg(feature = "serde")]
impl<K, V> serde::Serialize for BTreeMap<K, V>
where
    K: Ord + Clone + serde::Serialize,
    V: serde::Serialize,
{
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.collect_map(self.iter())
    }
}

#[cfg(feature = "serde")]
impl<'de, K, V> serde::Deserialize<'de> for BTreeMap<K, V>
where
    K: Ord + Clone + serde::Deserialize<'de>,
    V: serde::Deserialize<'de>,
{
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        struct Visitor<K, V>(core::marker::PhantomData<(K, V)>);

        impl<'de, K, V> serde::de::Visitor<'de> for Visitor<K, V>
        where
            K: Ord + Clone + serde::Deserialize<'de>,
            V: serde::Deserialize<'de>,
        {
            type Value = BTreeMap<K, V>;

            fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.write_str("a map")
            }

            fn visit_map<A: serde::de::MapAccess<'de>>(
                self,
                mut access: A,
            ) -> Result<Self::Value, A::Error> {
                let mut map = BTreeMap::new();
                while let Some((k, v)) = access.next_entry()? {
                    map.insert(k, v);
                }
                Ok(map)
            }
        }

        deserializer.deserialize_map(Visitor(core::marker::PhantomData))
    }
}
