use core::borrow::Borrow;
use core::fmt;
use core::iter::FusedIterator;
use core::marker::PhantomData;
use core::ops::{Bound, RangeBounds};
use core::ptr::NonNull;

use crate::layout;
use crate::BPlusTreeMap;

/// A resolved window over the leaves, walked from both ends.
///
/// Both endpoints are resolved to concrete (leaf, index) positions at
/// construction, so per-item work is an index compare plus two pointer
/// reads — no key comparisons, no re-carving the leaf. The front and back
/// cursors meet in the middle; `front_leaf == None` means exhausted.
///
/// The cursor yields raw slot pointers. The iterators wrap it and choose
/// what to hand out: shared references for [`Iter`] and [`Range`], unique
/// ones for [`IterMut`] and [`RangeMut`], which is sound because those are
/// built from a `&mut` borrow of the map.
pub(crate) struct Cursor<K, V> {
    leaf_layout: layout::LeafLayout,
    front_leaf: Option<NonNull<u8>>,
    front_idx: usize,
    front_len: usize,
    front_keys: *const K,
    front_vals: *const V,
    // Meaningful only while front_leaf is Some.
    back_leaf: NonNull<u8>,
    back_idx: usize,
    back_keys: *const K,
    back_vals: *const V,
}

impl<K, V> Cursor<K, V> {
    fn empty(leaf_layout: layout::LeafLayout) -> Self {
        Cursor {
            leaf_layout,
            front_leaf: None,
            front_idx: 0,
            front_len: 0,
            front_keys: core::ptr::null(),
            front_vals: core::ptr::null(),
            back_leaf: NonNull::dangling(),
            back_idx: 0,
            back_keys: core::ptr::null(),
            back_vals: core::ptr::null(),
        }
    }

    /// Step the front cursor, returning the key and value slot pointers.
    fn next_ptrs(&mut self) -> Option<(*const K, *mut V)> {
        loop {
            let leaf = self.front_leaf?;
            let same = leaf == self.back_leaf;
            let limit = if same { self.back_idx } else { self.front_len };

            if self.front_idx < limit {
                unsafe {
                    let k = self.front_keys.add(self.front_idx);
                    let v = self.front_vals.add(self.front_idx) as *mut V;
                    self.front_idx += 1;
                    return Some((k, v));
                }
            }

            if same {
                self.front_leaf = None;
                return None;
            }

            // Hop to the next leaf and refresh the cached view.
            unsafe {
                let parts = layout::carve_leaf::<K, V>(leaf, &self.leaf_layout);
                match NonNull::new(*parts.next_ptr) {
                    None => {
                        self.front_leaf = None;
                        return None;
                    }
                    Some(next) => {
                        let np = layout::carve_leaf::<K, V>(next, &self.leaf_layout);
                        self.front_leaf = Some(next);
                        self.front_idx = 0;
                        self.front_len = (*np.hdr).len as usize;
                        self.front_keys = np.keys_ptr as *const K;
                        self.front_vals = np.vals_ptr as *const V;
                    }
                }
            }
        }
    }

    /// Step the back cursor; see [`Cursor::next_ptrs`].
    fn next_back_ptrs(&mut self) -> Option<(*const K, *mut V)> {
        loop {
            let fleaf = self.front_leaf?;
            let same = fleaf == self.back_leaf;
            let lower = if same { self.front_idx } else { 0 };

            if self.back_idx > lower {
                unsafe {
                    self.back_idx -= 1;
                    let k = self.back_keys.add(self.back_idx);
                    let v = self.back_vals.add(self.back_idx) as *mut V;
                    return Some((k, v));
                }
            }

            if same {
                self.front_leaf = None;
                return None;
            }

            // Hop to the previous leaf and refresh the cached view.
            unsafe {
                let parts = layout::carve_leaf::<K, V>(self.back_leaf, &self.leaf_layout);
                let prev = parts.prev_ptr.and_then(|p| NonNull::new(*p));
                match prev {
                    None => {
                        self.front_leaf = None;
                        return None;
                    }
                    Some(prev) => {
                        let pp = layout::carve_leaf::<K, V>(prev, &self.leaf_layout);
                        self.back_leaf = prev;
                        self.back_idx = (*pp.hdr).len as usize;
                        self.back_keys = pp.keys_ptr as *const K;
                        self.back_vals = pp.vals_ptr as *const V;
                    }
                }
            }
        }
    }
}

/// Define an iterator that walks a [`Cursor`] and projects each slot.
macro_rules! cursor_iter {
    (
        $(#[$meta:meta])*
        $name:ident, $item:ty, $exact:tt, |$k:ident, $v:ident| $project:expr
    ) => {
        $(#[$meta])*
        pub struct $name<'a, K, V> {
            pub(crate) cur: Cursor<K, V>,
            pub(crate) remaining: usize,
            pub(crate) _marker: PhantomData<&'a mut (K, V)>,
        }

        impl<'a, K, V> Iterator for $name<'a, K, V> {
            type Item = $item;

            fn next(&mut self) -> Option<Self::Item> {
                let ($k, $v) = self.cur.next_ptrs()?;
                self.remaining = self.remaining.saturating_sub(1);
                unsafe { Some($project) }
            }

            fn size_hint(&self) -> (usize, Option<usize>) {
                cursor_iter!(@hint self, $exact)
            }

            fn last(mut self) -> Option<Self::Item> {
                self.next_back()
            }
        }

        impl<'a, K, V> DoubleEndedIterator for $name<'a, K, V> {
            fn next_back(&mut self) -> Option<Self::Item> {
                let ($k, $v) = self.cur.next_back_ptrs()?;
                self.remaining = self.remaining.saturating_sub(1);
                unsafe { Some($project) }
            }
        }

        impl<'a, K, V> FusedIterator for $name<'a, K, V> {}

        cursor_iter!(@exact $name, $exact);
    };
    (@hint $self:ident, exact) => {
        ($self.remaining, Some($self.remaining))
    };
    (@hint $self:ident, inexact) => {
        // The map's length bounds any range; the exact count is unknown
        // without walking, so only the upper bound is reported.
        (0, Some($self.remaining))
    };
    (@exact $name:ident, exact) => {
        impl<'a, K, V> ExactSizeIterator for $name<'a, K, V> {
            fn len(&self) -> usize {
                self.remaining
            }
        }
    };
    (@exact $name:ident, inexact) => {};
}

cursor_iter!(
    /// Iterator over a map's entries, in key order.
    Iter, (&'a K, &'a V), exact, |k, v| (&*k, &*v)
);
cursor_iter!(
    /// Iterator over a map's entries with mutable values, in key order.
    IterMut, (&'a K, &'a mut V), exact, |k, v| (&*k, &mut *v)
);
cursor_iter!(
    /// Iterator over a range of a map's entries.
    Range, (&'a K, &'a V), inexact, |k, v| (&*k, &*v)
);
cursor_iter!(
    /// Iterator over a range of a map's entries with mutable values.
    RangeMut, (&'a K, &'a mut V), inexact, |k, v| (&*k, &mut *v)
);

/// Define an iterator that projects one half of another iterator's item.
macro_rules! projecting_iter {
    (
        $(#[$meta:meta])*
        $name:ident, $inner:ident, $item:ty, $exact:tt, |$kv:ident| $project:expr
    ) => {
        $(#[$meta])*
        pub struct $name<'a, K, V> {
            pub(crate) inner: $inner<'a, K, V>,
        }

        impl<'a, K, V> Iterator for $name<'a, K, V> {
            type Item = $item;

            fn next(&mut self) -> Option<Self::Item> {
                self.inner.next().map(|$kv| $project)
            }

            fn size_hint(&self) -> (usize, Option<usize>) {
                self.inner.size_hint()
            }
        }

        impl<'a, K, V> DoubleEndedIterator for $name<'a, K, V> {
            fn next_back(&mut self) -> Option<Self::Item> {
                self.inner.next_back().map(|$kv| $project)
            }
        }

        impl<'a, K, V> FusedIterator for $name<'a, K, V> {}

        projecting_iter!(@exact $name, $exact);
    };
    (@exact $name:ident, exact) => {
        impl<'a, K, V> ExactSizeIterator for $name<'a, K, V> {
            fn len(&self) -> usize {
                self.inner.len()
            }
        }
    };
    (@exact $name:ident, inexact) => {};
}

projecting_iter!(
    /// Iterator over a map's keys, in order.
    Keys, Iter, &'a K, exact, |kv| kv.0
);
projecting_iter!(
    /// Iterator over a map's values, in key order.
    Values, Iter, &'a V, exact, |kv| kv.1
);
projecting_iter!(
    /// Iterator over a map's values with mutable access, in key order.
    ValuesMut, IterMut, &'a mut V, exact, |kv| kv.1
);

// Each iterator borrows the map for 'a and only reads through pointers
// into its nodes, so it carries the thread-safety of the borrow itself.
unsafe impl<K: Sync, V: Sync> Send for Iter<'_, K, V> {}
unsafe impl<K: Sync, V: Sync> Sync for Iter<'_, K, V> {}
unsafe impl<K: Sync, V: Send> Send for IterMut<'_, K, V> {}
unsafe impl<K: Sync, V: Sync> Sync for IterMut<'_, K, V> {}
unsafe impl<K: Sync, V: Sync> Send for Range<'_, K, V> {}
unsafe impl<K: Sync, V: Sync> Sync for Range<'_, K, V> {}
unsafe impl<K: Sync, V: Send> Send for RangeMut<'_, K, V> {}
unsafe impl<K: Sync, V: Sync> Sync for RangeMut<'_, K, V> {}

impl<K: fmt::Debug, V: fmt::Debug> fmt::Debug for Iter<'_, K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Iter").finish_non_exhaustive()
    }
}

impl<K: Ord + Clone, V> BPlusTreeMap<K, V> {
    /// Resolve the start bound to the position of the first in-range item.
    /// Lean: `resolveFront_spec` (`Proofs/Read.lean`): the position is the
    /// number of entries below the start bound; `resolveFrontH_sim`
    /// (`Proofs/HeapRead.lean`) maps the `(leaf, index)` pair to it.
    unsafe fn resolve_front<Q>(&self, start: Bound<&Q>) -> Option<(NonNull<u8>, usize)>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        let Some(k) = bound_key(start) else {
            let leaf = self.leftmost_leaf()?;
            // Only a root leaf can be empty, and it has no siblings.
            return (self.node_len(leaf) > 0).then_some((leaf, 0));
        };
        // An excluded start skips an exact match, so the cut sits after it.
        let after_equal = matches!(start, Bound::Excluded(_));
        let (leaf, idx, len) = self.cut_in_leaf(k, after_equal)?;
        if idx < len {
            return Some((leaf, idx));
        }
        // The cut is past this leaf's last key: start at the next leaf
        // (never empty, being non-root).
        let parts = layout::carve_leaf::<K, V>(leaf, &self.leaf_layout);
        NonNull::new(*parts.next_ptr).map(|next| (next, 0))
    }

    /// Resolve the end bound to the position one past the last in-range item.
    /// Lean: `resolveBack_spec`: the number of entries within the end bound;
    /// `resolveBackH_sim` on the heap.
    unsafe fn resolve_back<Q>(&self, end: Bound<&Q>) -> Option<(NonNull<u8>, usize)>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        let Some(k) = bound_key(end) else {
            let leaf = self.rightmost_leaf()?;
            let len = self.node_len(leaf);
            return (len > 0).then_some((leaf, len));
        };
        // An included end keeps an exact match, so the cut sits after it.
        let after_equal = matches!(end, Bound::Included(_));
        let (leaf, idx, _) = self.cut_in_leaf(k, after_equal)?;
        if idx > 0 {
            return Some((leaf, idx));
        }
        // The cut is before this leaf's first key: end at the end of the
        // previous leaf (never empty, being non-root).
        let parts = layout::carve_leaf::<K, V>(leaf, &self.leaf_layout);
        let prev = parts.prev_ptr.and_then(|p| NonNull::new(*p))?;
        Some((prev, self.node_len(prev)))
    }

    /// Find the leaf that would hold `k` and the index that cuts its keys
    /// into those before `k` and those after. With `after_equal` an exact
    /// match falls before the cut, otherwise after it. Returns
    /// `(leaf, cut, len)`; the cut may equal 0 or `len`.
    /// Lean: `cutInLeaf_spec`: the cut counts the leaf's keys on one side.
    unsafe fn cut_in_leaf<Q>(&self, k: &Q, after_equal: bool) -> Option<(NonNull<u8>, usize, usize)>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        let leaf = self.leaf_for_key(k)?;
        let parts = layout::carve_leaf::<K, V>(leaf, &self.leaf_layout);
        let len = (*parts.hdr).len as usize;
        let keys = core::slice::from_raw_parts(parts.keys_ptr as *const K, len);
        let cut = if after_equal {
            keys.partition_point(|x| x.borrow() <= k)
        } else {
            keys.partition_point(|x| x.borrow() < k)
        };
        Some((leaf, cut, len))
    }

    /// Lean: `rangeTree_spec` (`Proofs/Read.lean`): the items yielded are
    /// exactly the entries between the bounds, inverted bounds included;
    /// `itemsTree_spec` for `iter`. On the heap model, `rangeH_sim`
    /// (`Proofs/HeapRead.lean`): hopping along `next` from the front leaf to
    /// the back leaf (`drainH_sim`) reads exactly that slice of the entries.
    pub(crate) fn cursor<Q>(&self, start: Bound<&Q>, end: Bound<&Q>) -> Cursor<K, V>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        unsafe {
            let (front_leaf, front_idx) = match self.resolve_front(start) {
                Some(pos) => pos,
                None => return Cursor::empty(self.leaf_layout),
            };
            let (back_leaf, back_idx) = match self.resolve_back(end) {
                Some(pos) => pos,
                None => return Cursor::empty(self.leaf_layout),
            };

            let fp = layout::carve_leaf::<K, V>(front_leaf, &self.leaf_layout);
            let front_keys = fp.keys_ptr as *const K;
            let front_vals = fp.vals_ptr as *const V;

            // The front cursor points at the first key satisfying the start
            // bound; if that key violates the end bound the range is empty
            // (this also covers inverted bounds). Otherwise the front
            // position is strictly before the back position.
            let first_key: &Q = (*front_keys.add(front_idx)).borrow();
            let in_range = match end {
                Bound::Unbounded => true,
                Bound::Included(e) => first_key <= e,
                Bound::Excluded(e) => first_key < e,
            };
            if !in_range {
                return Cursor::empty(self.leaf_layout);
            }

            let bp = layout::carve_leaf::<K, V>(back_leaf, &self.leaf_layout);
            Cursor {
                leaf_layout: self.leaf_layout,
                front_leaf: Some(front_leaf),
                front_idx,
                front_len: (*fp.hdr).len as usize,
                front_keys,
                front_vals,
                back_leaf,
                back_idx,
                back_keys: bp.keys_ptr as *const K,
                back_vals: bp.vals_ptr as *const V,
            }
        }
    }

    fn full_cursor(&self) -> Cursor<K, V> {
        self.cursor::<K>(Bound::Unbounded, Bound::Unbounded)
    }

    pub fn iter(&self) -> Iter<'_, K, V> {
        Iter {
            cur: self.full_cursor(),
            remaining: self.len(),
            _marker: PhantomData,
        }
    }

    pub fn iter_mut(&mut self) -> IterMut<'_, K, V> {
        IterMut {
            cur: self.full_cursor(),
            remaining: self.len(),
            _marker: PhantomData,
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
            cur: self.cursor(range.start_bound(), range.end_bound()),
            remaining: self.len(),
            _marker: PhantomData,
        }
    }

    pub fn range_mut<Q, R>(&mut self, range: R) -> RangeMut<'_, K, V>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
        R: RangeBounds<Q>,
    {
        let remaining = self.len();
        RangeMut {
            cur: self.cursor(range.start_bound(), range.end_bound()),
            remaining,
            _marker: PhantomData,
        }
    }

    /// Lean: `firstTree_spec` (`Proofs/Read.lean`): the first entry;
    /// `firstH_sim` (`Proofs/HeapRead.lean`) on the heap.
    pub fn first_key_value(&self) -> Option<(&K, &V)> {
        let leaf = self.leftmost_leaf()?;
        unsafe {
            let parts = layout::carve_leaf::<K, V>(leaf, &self.leaf_layout);
            if (*parts.hdr).len == 0 {
                return None;
            }
            Some((
                &*(parts.keys_ptr as *const K),
                &*(parts.vals_ptr as *const V),
            ))
        }
    }

    /// Lean: `lastTree_spec` (`Proofs/Read.lean`): the last entry;
    /// `lastH_sim` (`Proofs/HeapRead.lean`) on the heap.
    pub fn last_key_value(&self) -> Option<(&K, &V)> {
        let leaf = self.rightmost_leaf()?;
        unsafe {
            let parts = layout::carve_leaf::<K, V>(leaf, &self.leaf_layout);
            let len = (*parts.hdr).len as usize;
            // Only a root leaf can be empty; non-root leaves hold >= min_leaf_len.
            if len == 0 {
                return None;
            }
            Some((
                &*(parts.keys_ptr.add(len - 1) as *const K),
                &*(parts.vals_ptr.add(len - 1) as *const V),
            ))
        }
    }

    /// Remove and return the first entry. Two descents: one to read the
    /// key, one to remove it.
    pub fn pop_first(&mut self) -> Option<(K, V)> {
        let key = self.first_key_value()?.0.clone();
        self.remove_entry::<K>(&key)
    }

    /// Remove and return the last entry. Two descents: one to read the key,
    /// one to remove it.
    pub fn pop_last(&mut self) -> Option<(K, V)> {
        let key = self.last_key_value()?.0.clone();
        self.remove_entry::<K>(&key)
    }
}

/// The key a bound is anchored on, or `None` for `Unbounded`.
fn bound_key<T: ?Sized>(bound: Bound<&T>) -> Option<&T> {
    match bound {
        Bound::Included(k) | Bound::Excluded(k) => Some(k),
        Bound::Unbounded => None,
    }
}
