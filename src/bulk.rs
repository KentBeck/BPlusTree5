//! Operations over many entries at once.

use alloc::vec::Vec;
use core::borrow::Borrow;
use core::ops::Bound;

use crate::owned::{IntoKeys, IntoValues};
use crate::BPlusTreeMap;

impl<K: Ord + Clone, V> BPlusTreeMap<K, V> {
    /// Keep only the entries `f` returns true for.
    ///
    /// One pass names the entries to drop, then each is removed. Values are
    /// visited in key order.
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&K, &mut V) -> bool,
    {
        let doomed: Vec<K> = self
            .iter_mut()
            .filter_map(|(k, v)| (!f(k, v)).then(|| k.clone()))
            .collect();
        for key in &doomed {
            self.remove::<K>(key);
        }
    }

    /// Move every entry of `other` into this map, leaving `other` empty.
    ///
    /// Keys present in both end up with `other`'s value, as in std.
    pub fn append(&mut self, other: &mut Self) {
        if other.is_empty() {
            return;
        }
        let taken = core::mem::replace(other, other.empty_like());
        for (key, value) in taken {
            self.insert(key, value);
        }
    }

    /// Split the map in two: everything below `key` stays, everything from
    /// `key` on is returned.
    pub fn split_off<Q>(&mut self, key: &Q) -> Self
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        let tail: Vec<K> = self
            .range((Bound::Included(key), Bound::Unbounded))
            .map(|(k, _)| k.clone())
            .collect();
        let mut out = self.empty_like();
        for key in tail {
            let (key, value) = self
                .remove_entry::<K>(&key)
                .expect("key came from this map's own range");
            out.insert(key, value);
        }
        out
    }

    /// Consume the map, iterating over its keys in order.
    pub fn into_keys(self) -> IntoKeys<K, V> {
        IntoKeys {
            inner: self.into_iter(),
        }
    }

    /// Consume the map, iterating over its values in key order.
    pub fn into_values(self) -> IntoValues<K, V> {
        IntoValues {
            inner: self.into_iter(),
        }
    }
}
