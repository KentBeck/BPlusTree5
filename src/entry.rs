//! In-place access to a single entry, found once.
//!
//! The lookup that decides vacant from occupied also remembers where the
//! value sits, so reading or replacing it costs no second descent. Filling
//! a vacant entry descends once, because the insert hands back the slot it
//! wrote (see `BPlusTreeMap::insert_at`).

use core::fmt;
use core::mem;
use core::ptr::NonNull;

use crate::layout;
use crate::BPlusTreeMap;

/// Which end of a leaf [`BPlusTreeMap::edge_slot`] reads.
enum Edge {
    First,
    Last,
}

/// A view into a single entry, which may be vacant or occupied.
pub enum Entry<'a, K, V> {
    /// A vacant entry.
    Vacant(VacantEntry<'a, K, V>),
    /// An occupied entry.
    Occupied(OccupiedEntry<'a, K, V>),
}

/// A view into a vacant entry.
pub struct VacantEntry<'a, K, V> {
    pub(crate) map: &'a mut BPlusTreeMap<K, V>,
    pub(crate) key: K,
}

/// A view into an occupied entry.
pub struct OccupiedEntry<'a, K, V> {
    pub(crate) map: &'a mut BPlusTreeMap<K, V>,
    pub(crate) key: K,
    /// The value's slot, found by the lookup that built this entry. The
    /// entry holds the map exclusively, so nothing can move the value
    /// while the slot is held.
    pub(crate) slot: *mut V,
}

impl<'a, K: Ord + Clone, V> Entry<'a, K, V> {
    /// The value for this entry, inserting `default` if vacant.
    pub fn or_insert(self, default: V) -> &'a mut V {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => entry.insert(default),
        }
    }

    /// The value for this entry, inserting the result of `default` if
    /// vacant.
    pub fn or_insert_with<F: FnOnce() -> V>(self, default: F) -> &'a mut V {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => entry.insert(default()),
        }
    }

    /// The value for this entry, inserting the result of `default` applied
    /// to the key if vacant.
    pub fn or_insert_with_key<F: FnOnce(&K) -> V>(self, default: F) -> &'a mut V {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => {
                let value = default(&entry.key);
                entry.insert(value)
            }
        }
    }

    /// The value for this entry, inserting `V::default()` if vacant.
    pub fn or_default(self) -> &'a mut V
    where
        V: Default,
    {
        self.or_insert_with(V::default)
    }

    /// The key this entry was looked up with.
    pub fn key(&self) -> &K {
        match self {
            Entry::Occupied(entry) => entry.key(),
            Entry::Vacant(entry) => entry.key(),
        }
    }

    /// Run `f` on the value if the entry is occupied.
    pub fn and_modify<F: FnOnce(&mut V)>(self, f: F) -> Self {
        match self {
            Entry::Occupied(mut entry) => {
                f(entry.get_mut());
                Entry::Occupied(entry)
            }
            Entry::Vacant(entry) => Entry::Vacant(entry),
        }
    }
}

impl<'a, K: Ord + Clone, V> VacantEntry<'a, K, V> {
    /// The key this entry was looked up with.
    pub fn key(&self) -> &K {
        &self.key
    }

    /// Take back the key.
    pub fn into_key(self) -> K {
        self.key
    }

    /// Insert `value` under this entry's key and return a reference to it.
    pub fn insert(self, value: V) -> &'a mut V {
        let (slot, old) = self.map.insert_at(self.key, value);
        debug_assert!(old.is_none(), "vacant entry found an occupied slot");
        unsafe { &mut *slot }
    }
}

impl<'a, K: Ord + Clone, V> OccupiedEntry<'a, K, V> {
    /// The key this entry was looked up with.
    pub fn key(&self) -> &K {
        &self.key
    }

    /// The value in the entry.
    pub fn get(&self) -> &V {
        unsafe { &*self.slot }
    }

    /// The value in the entry, mutably.
    pub fn get_mut(&mut self) -> &mut V {
        unsafe { &mut *self.slot }
    }

    /// The value in the entry, with the lifetime of the map borrow.
    pub fn into_mut(self) -> &'a mut V {
        unsafe { &mut *self.slot }
    }

    /// Replace the value, returning the old one.
    pub fn insert(&mut self, value: V) -> V {
        mem::replace(self.get_mut(), value)
    }

    /// Take the value out of the map.
    pub fn remove(self) -> V {
        self.remove_entry().1
    }

    /// Take the key and value out of the map.
    pub fn remove_entry(self) -> (K, V) {
        self.map
            .remove_entry::<K>(&self.key)
            .expect("occupied entry names a present key")
    }
}

impl<K: Ord + Clone, V> BPlusTreeMap<K, V> {
    /// A view into the entry for `key`, for in-place inspection or insertion.
    pub fn entry(&mut self, key: K) -> Entry<'_, K, V> {
        let slot = self
            .leaf_search(&key)
            .map(|(parts, idx)| unsafe { parts.vals_ptr.add(idx) as *mut V });
        match slot {
            Some(slot) => Entry::Occupied(OccupiedEntry {
                map: self,
                key,
                slot,
            }),
            None => Entry::Vacant(VacantEntry { map: self, key }),
        }
    }

    /// An occupied entry for the first key, or `None` if the map is empty.
    pub fn first_entry(&mut self) -> Option<OccupiedEntry<'_, K, V>> {
        let leaf = self.leftmost_leaf()?;
        let (key, slot) = unsafe { self.edge_slot(leaf, Edge::First)? };
        Some(OccupiedEntry {
            map: self,
            key,
            slot,
        })
    }

    /// An occupied entry for the last key, or `None` if the map is empty.
    pub fn last_entry(&mut self) -> Option<OccupiedEntry<'_, K, V>> {
        let leaf = self.rightmost_leaf()?;
        let (key, slot) = unsafe { self.edge_slot(leaf, Edge::Last)? };
        Some(OccupiedEntry {
            map: self,
            key,
            slot,
        })
    }

    /// The key and the value's slot at one end of `leaf`.
    ///
    /// The slot pointer is carved straight out of the node allocation. A
    /// pointer taken instead from a `&V` would only carry read permission,
    /// and writing through it would be undefined behaviour.
    unsafe fn edge_slot(&self, leaf: NonNull<u8>, edge: Edge) -> Option<(K, *mut V)> {
        let parts = layout::carve_leaf::<K, V>(leaf, &self.leaf_layout);
        let len = (*parts.hdr).len as usize;
        // Only a root leaf can be empty.
        if len == 0 {
            return None;
        }
        let idx = match edge {
            Edge::First => 0,
            Edge::Last => len - 1,
        };
        let key = (*(parts.keys_ptr.add(idx) as *const K)).clone();
        Some((key, parts.vals_ptr.add(idx) as *mut V))
    }
}

impl<K: fmt::Debug + Ord + Clone, V: fmt::Debug> fmt::Debug for Entry<'_, K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Entry::Vacant(entry) => f.debug_tuple("Entry").field(entry).finish(),
            Entry::Occupied(entry) => f.debug_tuple("Entry").field(entry).finish(),
        }
    }
}

impl<K: fmt::Debug + Ord + Clone, V> fmt::Debug for VacantEntry<'_, K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("VacantEntry").field(self.key()).finish()
    }
}

impl<K: fmt::Debug + Ord + Clone, V: fmt::Debug> fmt::Debug for OccupiedEntry<'_, K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("OccupiedEntry")
            .field("key", self.key())
            .field("value", self.get())
            .finish()
    }
}
