//! An ordered set with the API of `std::collections::BTreeSet`, stored as a
//! [`BPlusTreeMap`] whose values are `()`.

use core::borrow::Borrow;
use core::cmp::Ordering;
use core::fmt;
use core::hash::{Hash, Hasher};
use core::iter::{FusedIterator, Peekable};
use core::ops::{BitAnd, BitOr, BitXor, RangeBounds, Sub};

use crate::BPlusTreeMap;

/// An ordered set, stored as a B+ tree.
///
/// See the [crate documentation](crate) for how this differs from
/// `std::collections::BTreeSet`.
pub struct BPlusTreeSet<T> {
    map: BPlusTreeMap<T, ()>,
}

impl<T: Ord + Clone> BPlusTreeSet<T> {
    /// An empty set.
    pub fn new() -> Self {
        Self {
            map: BPlusTreeMap::new(),
        }
    }

    /// The number of elements.
    pub fn len(&self) -> usize {
        self.map.len()
    }

    /// Whether the set holds no elements.
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    /// Remove every element.
    pub fn clear(&mut self) {
        self.map.clear()
    }

    /// Whether `value` is in the set.
    pub fn contains<Q>(&self, value: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.map.contains_key(value)
    }

    /// The element equal to `value`.
    pub fn get<Q>(&self, value: &Q) -> Option<&T>
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.map.get_key_value(value).map(|(k, _)| k)
    }

    /// Add `value`; returns whether it was newly inserted.
    pub fn insert(&mut self, value: T) -> bool {
        self.map.insert(value, ()).is_none()
    }

    /// Add `value`, returning the element it replaced.
    pub fn replace(&mut self, value: T) -> Option<T> {
        let old = self.map.remove_entry::<T>(&value).map(|(k, _)| k);
        self.map.insert(value, ());
        old
    }

    /// Remove `value`; returns whether it was present.
    pub fn remove<Q>(&mut self, value: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.map.remove(value).is_some()
    }

    /// Remove and return the element equal to `value`.
    pub fn take<Q>(&mut self, value: &Q) -> Option<T>
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.map.remove_entry(value).map(|(k, _)| k)
    }

    /// Iterate over the elements in order.
    pub fn iter(&self) -> Iter<'_, T> {
        Iter {
            inner: self.map.keys(),
        }
    }

    /// Iterate over the elements within `range`, in order.
    pub fn range<Q, R>(&self, range: R) -> Range<'_, T>
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
        R: RangeBounds<Q>,
    {
        Range {
            inner: self.map.range(range),
        }
    }

    /// The smallest element.
    pub fn first(&self) -> Option<&T> {
        self.map.first_key_value().map(|(k, _)| k)
    }

    /// The largest element.
    pub fn last(&self) -> Option<&T> {
        self.map.last_key_value().map(|(k, _)| k)
    }

    /// Remove and return the smallest element.
    pub fn pop_first(&mut self) -> Option<T> {
        self.map.pop_first().map(|(k, _)| k)
    }

    /// Remove and return the largest element.
    pub fn pop_last(&mut self) -> Option<T> {
        self.map.pop_last().map(|(k, _)| k)
    }

    /// Keep only the elements `f` returns true for.
    pub fn retain<F: FnMut(&T) -> bool>(&mut self, mut f: F) {
        self.map.retain(|k, _| f(k))
    }

    /// Move every element of `other` into this set, leaving `other` empty.
    pub fn append(&mut self, other: &mut Self) {
        self.map.append(&mut other.map)
    }

    /// Split the set in two: everything below `value` stays, everything
    /// from `value` on is returned.
    pub fn split_off<Q>(&mut self, value: &Q) -> Self
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        Self {
            map: self.map.split_off(value),
        }
    }

    /// The elements in either set, in order.
    pub fn union<'a>(&'a self, other: &'a Self) -> Union<'a, T> {
        Union(Merge::new(self, other))
    }

    /// The elements in both sets, in order.
    pub fn intersection<'a>(&'a self, other: &'a Self) -> Intersection<'a, T> {
        Intersection(Merge::new(self, other))
    }

    /// The elements in this set and not the other, in order.
    pub fn difference<'a>(&'a self, other: &'a Self) -> Difference<'a, T> {
        Difference(Merge::new(self, other))
    }

    /// The elements in exactly one of the sets, in order.
    pub fn symmetric_difference<'a>(&'a self, other: &'a Self) -> SymmetricDifference<'a, T> {
        SymmetricDifference(Merge::new(self, other))
    }

    /// Whether the two sets share no elements.
    pub fn is_disjoint(&self, other: &Self) -> bool {
        self.intersection(other).next().is_none()
    }

    /// Whether every element of this set is in `other`.
    pub fn is_subset(&self, other: &Self) -> bool {
        self.len() <= other.len() && self.iter().all(|v| other.contains(v))
    }

    /// Whether every element of `other` is in this set.
    pub fn is_superset(&self, other: &Self) -> bool {
        other.is_subset(self)
    }
}

/// Two sets walked in lockstep, in key order.
struct Merge<'a, T> {
    a: Peekable<Iter<'a, T>>,
    b: Peekable<Iter<'a, T>>,
}

impl<'a, T: Ord + Clone> Merge<'a, T> {
    fn new(a: &'a BPlusTreeSet<T>, b: &'a BPlusTreeSet<T>) -> Self {
        Merge {
            a: a.iter().peekable(),
            b: b.iter().peekable(),
        }
    }

    /// Which side holds the next element, or `None` when both are spent.
    fn step(&mut self) -> Option<Ordering> {
        match (self.a.peek(), self.b.peek()) {
            (None, None) => None,
            (Some(_), None) => Some(Ordering::Less),
            (None, Some(_)) => Some(Ordering::Greater),
            (Some(x), Some(y)) => Some(x.cmp(y)),
        }
    }
}

/// An iterator over the union of two sets.
pub struct Union<'a, T>(Merge<'a, T>);
/// An iterator over the intersection of two sets.
pub struct Intersection<'a, T>(Merge<'a, T>);
/// An iterator over the elements of one set that are not in another.
pub struct Difference<'a, T>(Merge<'a, T>);
/// An iterator over the elements in exactly one of two sets.
pub struct SymmetricDifference<'a, T>(Merge<'a, T>);

impl<'a, T: Ord + Clone> Iterator for Union<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        match self.0.step()? {
            Ordering::Less => self.0.a.next(),
            Ordering::Greater => self.0.b.next(),
            Ordering::Equal => {
                self.0.b.next();
                self.0.a.next()
            }
        }
    }
}

impl<'a, T: Ord + Clone> Iterator for Intersection<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        loop {
            match self.0.step()? {
                Ordering::Less => {
                    self.0.a.next();
                }
                Ordering::Greater => {
                    self.0.b.next();
                }
                Ordering::Equal => {
                    self.0.b.next();
                    return self.0.a.next();
                }
            }
        }
    }
}

impl<'a, T: Ord + Clone> Iterator for Difference<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        loop {
            match self.0.step()? {
                Ordering::Less => return self.0.a.next(),
                Ordering::Greater => {
                    self.0.b.next();
                }
                Ordering::Equal => {
                    self.0.a.next();
                    self.0.b.next();
                }
            }
        }
    }
}

impl<'a, T: Ord + Clone> Iterator for SymmetricDifference<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        loop {
            match self.0.step()? {
                Ordering::Less => return self.0.a.next(),
                Ordering::Greater => return self.0.b.next(),
                Ordering::Equal => {
                    self.0.a.next();
                    self.0.b.next();
                }
            }
        }
    }
}

/// An iterator over a set's elements, in order.
pub struct Iter<'a, T> {
    inner: crate::iterate::Keys<'a, T, ()>,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        self.inner.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<T> DoubleEndedIterator for Iter<'_, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner.next_back()
    }
}

impl<T> ExactSizeIterator for Iter<'_, T> {
    fn len(&self) -> usize {
        self.inner.len()
    }
}

impl<T> FusedIterator for Iter<'_, T> {}

/// An iterator over a range of a set's elements.
pub struct Range<'a, T> {
    inner: crate::iterate::Range<'a, T, ()>,
}

impl<'a, T> Iterator for Range<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        self.inner.next().map(|(k, _)| k)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<T> DoubleEndedIterator for Range<'_, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner.next_back().map(|(k, _)| k)
    }
}

impl<T> FusedIterator for Range<'_, T> {}

/// An owning iterator over a set's elements, in order.
pub struct IntoIter<T> {
    inner: crate::owned::IntoIter<T, ()>,
}

impl<T> Iterator for IntoIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<T> {
        self.inner.next().map(|(k, _)| k)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<T> DoubleEndedIterator for IntoIter<T> {
    fn next_back(&mut self) -> Option<T> {
        self.inner.next_back().map(|(k, _)| k)
    }
}

impl<T> ExactSizeIterator for IntoIter<T> {
    fn len(&self) -> usize {
        self.inner.len()
    }
}

impl<T> FusedIterator for IntoIter<T> {}

impl<T: Ord + Clone> Default for BPlusTreeSet<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Ord + Clone> Clone for BPlusTreeSet<T> {
    fn clone(&self) -> Self {
        Self {
            map: self.map.clone(),
        }
    }
}

impl<T: Ord + Clone + fmt::Debug> fmt::Debug for BPlusTreeSet<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_set().entries(self.iter()).finish()
    }
}

impl<T: Ord + Clone> PartialEq for BPlusTreeSet<T> {
    fn eq(&self, other: &Self) -> bool {
        self.map == other.map
    }
}

impl<T: Ord + Clone> Eq for BPlusTreeSet<T> {}

impl<T: Ord + Clone> PartialOrd for BPlusTreeSet<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<T: Ord + Clone> Ord for BPlusTreeSet<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.iter().cmp(other.iter())
    }
}

impl<T: Ord + Clone + Hash> Hash for BPlusTreeSet<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write_usize(self.len());
        for value in self.iter() {
            value.hash(state);
        }
    }
}

impl<T: Ord + Clone> FromIterator<T> for BPlusTreeSet<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut out = Self::new();
        out.extend(iter);
        out
    }
}

impl<T: Ord + Clone> Extend<T> for BPlusTreeSet<T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        for value in iter {
            self.map.insert(value, ());
        }
    }
}

impl<'a, T: Ord + Clone + Copy> Extend<&'a T> for BPlusTreeSet<T> {
    fn extend<I: IntoIterator<Item = &'a T>>(&mut self, iter: I) {
        for value in iter {
            self.map.insert(*value, ());
        }
    }
}

impl<T: Ord + Clone, const N: usize> From<[T; N]> for BPlusTreeSet<T> {
    fn from(values: [T; N]) -> Self {
        values.into_iter().collect()
    }
}

impl<'a, T: Ord + Clone> IntoIterator for &'a BPlusTreeSet<T> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Iter<'a, T> {
        self.iter()
    }
}

impl<T: Ord + Clone> IntoIterator for BPlusTreeSet<T> {
    type Item = T;
    type IntoIter = IntoIter<T>;

    fn into_iter(self) -> IntoIter<T> {
        IntoIter {
            inner: self.map.into_iter(),
        }
    }
}

macro_rules! set_operator {
    ($trait:ident, $method:ident, $op:ident, $doc:literal) => {
        impl<T: Ord + Clone> $trait<&BPlusTreeSet<T>> for &BPlusTreeSet<T> {
            type Output = BPlusTreeSet<T>;

            #[doc = $doc]
            fn $method(self, other: &BPlusTreeSet<T>) -> BPlusTreeSet<T> {
                self.$op(other).cloned().collect()
            }
        }
    };
}

set_operator!(BitOr, bitor, union, "The union of the two sets.");
set_operator!(
    BitAnd,
    bitand,
    intersection,
    "The intersection of the two sets."
);
set_operator!(
    BitXor,
    bitxor,
    symmetric_difference,
    "The symmetric difference of the two sets."
);
set_operator!(Sub, sub, difference, "The difference of the two sets.");
