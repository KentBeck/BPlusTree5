use core::borrow::Borrow;
use core::cmp::Ordering;
use core::fmt;
use core::hash::{Hash, Hasher};
use core::ops::RangeBounds;

use crate::map::{BTreeMap, IntoIter, Iter, Range};

/// Ordered set with the `std::collections::BTreeSet` API, stored as a
/// [`BTreeMap`] with unit values.
pub struct BTreeSet<T> {
    map: BTreeMap<T, ()>,
}

impl<T: Ord + Clone> BTreeSet<T> {
    pub fn new() -> Self {
        Self {
            map: BTreeMap::new(),
        }
    }

    pub fn with_node_capacity(capacity: usize) -> Self {
        Self {
            map: BTreeMap::with_node_capacity(capacity),
        }
    }

    pub fn len(&self) -> usize {
        self.map.len()
    }

    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    pub fn clear(&mut self) {
        self.map.clear()
    }

    pub fn contains<Q>(&self, value: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.map.contains_key(value)
    }

    pub fn get<Q>(&self, value: &Q) -> Option<&T>
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.map.get_key_value(value).map(|(k, _)| k)
    }

    /// Returns whether the value was newly inserted.
    pub fn insert(&mut self, value: T) -> bool {
        self.map.insert(value, ()).is_none()
    }

    /// Replaces an equal value, returning the old one.
    pub fn replace(&mut self, value: T) -> Option<T> {
        let old = self.map.remove_entry(&value).map(|(k, _)| k);
        self.map.insert(value, ());
        old
    }

    pub fn remove<Q>(&mut self, value: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.map.remove(value).is_some()
    }

    pub fn take<Q>(&mut self, value: &Q) -> Option<T>
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.map.remove_entry(value).map(|(k, _)| k)
    }

    pub fn iter(&self) -> SetIter<'_, T> {
        SetIter {
            inner: self.map.iter(),
        }
    }

    pub fn range<Q, R>(&self, range: R) -> SetRange<'_, T>
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
        R: RangeBounds<Q>,
    {
        SetRange {
            inner: self.map.range(range),
        }
    }

    pub fn first(&self) -> Option<&T> {
        self.map.first_key_value().map(|(k, _)| k)
    }

    pub fn last(&self) -> Option<&T> {
        self.map.last_key_value().map(|(k, _)| k)
    }

    pub fn pop_first(&mut self) -> Option<T> {
        self.map.pop_first().map(|(k, _)| k)
    }

    pub fn pop_last(&mut self) -> Option<T> {
        self.map.pop_last().map(|(k, _)| k)
    }

    pub fn retain<F: FnMut(&T) -> bool>(&mut self, mut f: F) {
        self.map.retain(|k, _| f(k))
    }

    pub fn append(&mut self, other: &mut Self) {
        self.map.append(&mut other.map)
    }

    pub fn split_off<Q>(&mut self, value: &Q) -> Self
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        Self {
            map: self.map.split_off(value),
        }
    }

    pub fn is_subset(&self, other: &Self) -> bool {
        self.iter().all(|v| other.contains(v))
    }

    pub fn is_superset(&self, other: &Self) -> bool {
        other.is_subset(self)
    }

    pub fn is_disjoint(&self, other: &Self) -> bool {
        !self.iter().any(|v| other.contains(v))
    }

    pub fn union<'a>(&'a self, other: &'a Self) -> impl Iterator<Item = &'a T> + 'a {
        let mut merged: Vec<&'a T> = self.iter().chain(other.iter()).collect();
        merged.sort();
        merged.dedup();
        merged.into_iter()
    }

    pub fn intersection<'a>(&'a self, other: &'a Self) -> impl Iterator<Item = &'a T> + 'a {
        self.iter().filter(move |v| other.contains(*v))
    }

    pub fn difference<'a>(&'a self, other: &'a Self) -> impl Iterator<Item = &'a T> + 'a {
        self.iter().filter(move |v| !other.contains(*v))
    }
}

impl<T: Ord + Clone> Default for BTreeSet<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Ord + Clone> Clone for BTreeSet<T> {
    fn clone(&self) -> Self {
        Self {
            map: self.map.clone(),
        }
    }
}

impl<T: Ord + Clone + fmt::Debug> fmt::Debug for BTreeSet<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_set().entries(self.iter()).finish()
    }
}

impl<T: Ord + Clone> PartialEq for BTreeSet<T> {
    fn eq(&self, other: &Self) -> bool {
        self.map == other.map
    }
}

impl<T: Ord + Clone> Eq for BTreeSet<T> {}

impl<T: Ord + Clone> PartialOrd for BTreeSet<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<T: Ord + Clone> Ord for BTreeSet<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.iter().cmp(other.iter())
    }
}

impl<T: Ord + Clone + Hash> Hash for BTreeSet<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write_usize(self.len());
        for v in self.iter() {
            v.hash(state);
        }
    }
}

impl<T: Ord + Clone> FromIterator<T> for BTreeSet<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut out = Self::new();
        out.extend(iter);
        out
    }
}

impl<T: Ord + Clone> Extend<T> for BTreeSet<T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        for v in iter {
            self.map.insert(v, ());
        }
    }
}

impl<'a, T: Ord + Clone> Extend<&'a T> for BTreeSet<T> {
    fn extend<I: IntoIterator<Item = &'a T>>(&mut self, iter: I) {
        for v in iter {
            self.map.insert(v.clone(), ());
        }
    }
}

impl<T: Ord + Clone, const N: usize> From<[T; N]> for BTreeSet<T> {
    fn from(arr: [T; N]) -> Self {
        arr.into_iter().collect()
    }
}

impl<'a, T: Ord + Clone> IntoIterator for &'a BTreeSet<T> {
    type Item = &'a T;
    type IntoIter = SetIter<'a, T>;

    fn into_iter(self) -> SetIter<'a, T> {
        self.iter()
    }
}

impl<T: Ord + Clone> IntoIterator for BTreeSet<T> {
    type Item = T;
    type IntoIter = SetIntoIter<T>;

    fn into_iter(self) -> SetIntoIter<T> {
        SetIntoIter {
            inner: self.map.into_iter(),
        }
    }
}

pub struct SetIter<'a, T> {
    inner: Iter<'a, T, ()>,
}

impl<'a, T: Ord> Iterator for SetIter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        self.inner.next().map(|(k, _)| k)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<'a, T: Ord> DoubleEndedIterator for SetIter<'a, T> {
    fn next_back(&mut self) -> Option<&'a T> {
        self.inner.next_back().map(|(k, _)| k)
    }
}

impl<'a, T: Ord> ExactSizeIterator for SetIter<'a, T> {}

pub struct SetRange<'a, T> {
    inner: Range<'a, T, ()>,
}

impl<'a, T: Ord> Iterator for SetRange<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        self.inner.next().map(|(k, _)| k)
    }
}

impl<'a, T: Ord> DoubleEndedIterator for SetRange<'a, T> {
    fn next_back(&mut self) -> Option<&'a T> {
        self.inner.next_back().map(|(k, _)| k)
    }
}

pub struct SetIntoIter<T> {
    inner: IntoIter<T, ()>,
}

impl<T: Ord + Clone> Iterator for SetIntoIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<T> {
        self.inner.next().map(|(k, _)| k)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<T: Ord + Clone> DoubleEndedIterator for SetIntoIter<T> {
    fn next_back(&mut self) -> Option<T> {
        self.inner.next_back().map(|(k, _)| k)
    }
}

impl<T: Ord + Clone> ExactSizeIterator for SetIntoIter<T> {}

#[cfg(feature = "serde")]
impl<T: Ord + Clone + serde::Serialize> serde::Serialize for BTreeSet<T> {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.collect_seq(self.iter())
    }
}

#[cfg(feature = "serde")]
impl<'de, T: Ord + Clone + serde::Deserialize<'de>> serde::Deserialize<'de> for BTreeSet<T> {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        struct Visitor<T>(core::marker::PhantomData<T>);

        impl<'de, T: Ord + Clone + serde::Deserialize<'de>> serde::de::Visitor<'de> for Visitor<T> {
            type Value = BTreeSet<T>;

            fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.write_str("a sequence")
            }

            fn visit_seq<A: serde::de::SeqAccess<'de>>(
                self,
                mut access: A,
            ) -> Result<Self::Value, A::Error> {
                let mut set = BTreeSet::new();
                while let Some(v) = access.next_element()? {
                    set.insert(v);
                }
                Ok(set)
            }
        }

        deserializer.deserialize_seq(Visitor(core::marker::PhantomData))
    }
}
