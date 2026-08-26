use core::ops::{Bound, RangeBounds};
use core::ptr::NonNull;

use crate::layout;
use crate::BPlusTreeMap;

/// Lazy double-ended iterator over key/value pairs.
///
/// Both endpoints are resolved to concrete (leaf, index) positions at
/// construction, so per-item work is an index compare plus two pointer
/// reads — no key comparisons, no re-carving the leaf. The front and back
/// cursors meet in the middle; `front_leaf == None` means exhausted.
pub struct Items<'a, K, V> {
    tree: &'a BPlusTreeMap<K, V>,
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

impl<'a, K: Ord, V> Iterator for Items<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let leaf = self.front_leaf?;
            let same = leaf == self.back_leaf;
            let limit = if same { self.back_idx } else { self.front_len };

            if self.front_idx < limit {
                unsafe {
                    let k = &*self.front_keys.add(self.front_idx);
                    let v = &*self.front_vals.add(self.front_idx);
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
                let parts = layout::carve_leaf::<K, V>(leaf, &self.tree.leaf_layout);
                match NonNull::new(*parts.next_ptr) {
                    None => {
                        self.front_leaf = None;
                        return None;
                    }
                    Some(next) => {
                        let np = layout::carve_leaf::<K, V>(next, &self.tree.leaf_layout);
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

    fn size_hint(&self) -> (usize, Option<usize>) {
        if self.front_leaf.is_none() {
            (0, Some(0))
        } else {
            (0, None)
        }
    }
}

impl<'a, K: Ord, V> DoubleEndedIterator for Items<'a, K, V> {
    fn next_back(&mut self) -> Option<<Self as Iterator>::Item> {
        loop {
            let fleaf = self.front_leaf?;
            let same = fleaf == self.back_leaf;
            let lower = if same { self.front_idx } else { 0 };

            if self.back_idx > lower {
                unsafe {
                    self.back_idx -= 1;
                    let k = &*self.back_keys.add(self.back_idx);
                    let v = &*self.back_vals.add(self.back_idx);
                    return Some((k, v));
                }
            }

            if same {
                self.front_leaf = None;
                return None;
            }

            // Hop to the previous leaf and refresh the cached view.
            unsafe {
                let parts = layout::carve_leaf::<K, V>(self.back_leaf, &self.tree.leaf_layout);
                let prev = parts.prev_ptr.and_then(|p| NonNull::new(*p));
                match prev {
                    None => {
                        self.front_leaf = None;
                        return None;
                    }
                    Some(prev) => {
                        let pp = layout::carve_leaf::<K, V>(prev, &self.tree.leaf_layout);
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

pub struct Keys<'a, K, V> {
    pub(crate) inner: Items<'a, K, V>,
}

impl<'a, K: Ord, V> Iterator for Keys<'a, K, V> {
    type Item = &'a K;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(k, _)| k)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<'a, K: Ord, V> DoubleEndedIterator for Keys<'a, K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner.next_back().map(|(k, _)| k)
    }
}

pub struct Values<'a, K, V> {
    pub(crate) inner: Items<'a, K, V>,
}

impl<'a, K: Ord, V> Iterator for Values<'a, K, V> {
    type Item = &'a V;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(_, v)| v)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<'a, K: Ord, V> DoubleEndedIterator for Values<'a, K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner.next_back().map(|(_, v)| v)
    }
}

impl<K: Ord + Clone, V> BPlusTreeMap<K, V> {
    fn empty_items(&self) -> Items<'_, K, V> {
        Items {
            tree: self,
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

    /// Resolve the start bound to the position of the first in-range item.
    unsafe fn resolve_front(&self, start: Bound<&K>) -> Option<(NonNull<u8>, usize)> {
        match start {
            Bound::Unbounded => {
                let leaf = self.leftmost_leaf()?;
                let parts = layout::carve_leaf::<K, V>(leaf, &self.leaf_layout);
                // Only a root leaf can be empty, and it has no siblings.
                if (*parts.hdr).len == 0 {
                    return None;
                }
                Some((leaf, 0))
            }
            Bound::Included(k) | Bound::Excluded(k) => {
                let excluded = matches!(start, Bound::Excluded(_));
                let leaf = self.leaf_for_key(k)?;
                let parts = layout::carve_leaf::<K, V>(leaf, &self.leaf_layout);
                let len = (*parts.hdr).len as usize;
                let keys = core::slice::from_raw_parts(parts.keys_ptr as *const K, len);
                let idx = match keys.binary_search(k) {
                    Ok(i) => {
                        if excluded {
                            i + 1
                        } else {
                            i
                        }
                    }
                    Err(i) => i,
                };
                if idx < len {
                    Some((leaf, idx))
                } else {
                    // Non-root leaves are never empty.
                    NonNull::new(*parts.next_ptr).map(|next| (next, 0))
                }
            }
        }
    }

    /// Resolve the end bound to the position one past the last in-range item.
    unsafe fn resolve_back(&self, end: Bound<&K>) -> Option<(NonNull<u8>, usize)> {
        match end {
            Bound::Unbounded => {
                let leaf = self.rightmost_leaf()?;
                let parts = layout::carve_leaf::<K, V>(leaf, &self.leaf_layout);
                let len = (*parts.hdr).len as usize;
                if len == 0 {
                    return None;
                }
                Some((leaf, len))
            }
            Bound::Included(k) | Bound::Excluded(k) => {
                let excluded = matches!(end, Bound::Excluded(_));
                let leaf = self.leaf_for_key(k)?;
                let parts = layout::carve_leaf::<K, V>(leaf, &self.leaf_layout);
                let len = (*parts.hdr).len as usize;
                let keys = core::slice::from_raw_parts(parts.keys_ptr as *const K, len);
                let idx = match keys.binary_search(k) {
                    Ok(i) => {
                        if excluded {
                            i
                        } else {
                            i + 1
                        }
                    }
                    Err(i) => i,
                };
                if idx > 0 {
                    Some((leaf, idx))
                } else {
                    // End position is the boundary before this leaf: the end of
                    // the previous leaf (never empty, being non-root).
                    let prev = parts.prev_ptr.and_then(|p| NonNull::new(*p))?;
                    let pp = layout::carve_leaf::<K, V>(prev, &self.leaf_layout);
                    Some((prev, (*pp.hdr).len as usize))
                }
            }
        }
    }

    fn make_items(&self, start: Bound<&K>, end: Bound<&K>) -> Items<'_, K, V> {
        unsafe {
            let (front_leaf, front_idx) = match self.resolve_front(start) {
                Some(pos) => pos,
                None => return self.empty_items(),
            };
            let (back_leaf, back_idx) = match self.resolve_back(end) {
                Some(pos) => pos,
                None => return self.empty_items(),
            };

            let fp = layout::carve_leaf::<K, V>(front_leaf, &self.leaf_layout);
            let front_keys = fp.keys_ptr as *const K;
            let front_vals = fp.vals_ptr as *const V;

            // The front cursor points at the first key satisfying the start
            // bound; if that key violates the end bound the range is empty
            // (this also covers inverted bounds). Otherwise the front
            // position is strictly before the back position.
            let first_key = &*front_keys.add(front_idx);
            let in_range = match end {
                Bound::Unbounded => true,
                Bound::Included(e) => first_key <= e,
                Bound::Excluded(e) => first_key < e,
            };
            if !in_range {
                return self.empty_items();
            }

            let bp = layout::carve_leaf::<K, V>(back_leaf, &self.leaf_layout);
            Items {
                tree: self,
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

    pub fn items(&self) -> Items<'_, K, V> {
        self.make_items(Bound::Unbounded, Bound::Unbounded)
    }

    pub fn keys(&self) -> Keys<'_, K, V> {
        Keys {
            inner: self.items(),
        }
    }

    pub fn values(&self) -> Values<'_, K, V> {
        Values {
            inner: self.items(),
        }
    }

    pub fn items_range(&self, start: Option<&K>, end: Option<&K>) -> Items<'_, K, V> {
        let sb = start.map_or(Bound::Unbounded, Bound::Included);
        let eb = end.map_or(Bound::Unbounded, Bound::Excluded);
        self.make_items(sb, eb)
    }

    pub fn range<R: RangeBounds<K>>(&self, r: R) -> Items<'_, K, V> {
        self.make_items(r.start_bound(), r.end_bound())
    }

    pub fn first(&self) -> Option<(&K, &V)> {
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

    pub fn last(&self) -> Option<(&K, &V)> {
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
}
