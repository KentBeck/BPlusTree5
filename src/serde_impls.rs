//! `Serialize`/`Deserialize` for the map and set, matching how
//! `std::collections::BTreeMap` and `BTreeSet` are represented.

#![cfg(feature = "serde")]

use core::fmt;
use core::marker::PhantomData;

use serde::de::{MapAccess, SeqAccess, Visitor};
use serde::{Deserialize, Deserializer, Serialize, Serializer};

use crate::{BPlusTreeMap, BPlusTreeSet};

impl<K: Ord + Clone + Serialize, V: Serialize> Serialize for BPlusTreeMap<K, V> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.collect_map(self.iter())
    }
}

struct MapVisitor<K, V>(PhantomData<(K, V)>);

impl<'de, K, V> Visitor<'de> for MapVisitor<K, V>
where
    K: Ord + Clone + Deserialize<'de>,
    V: Deserialize<'de>,
{
    type Value = BPlusTreeMap<K, V>;

    fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("a map")
    }

    fn visit_map<A: MapAccess<'de>>(self, mut access: A) -> Result<Self::Value, A::Error> {
        let mut map = BPlusTreeMap::new();
        while let Some((key, value)) = access.next_entry()? {
            map.insert(key, value);
        }
        Ok(map)
    }
}

impl<'de, K, V> Deserialize<'de> for BPlusTreeMap<K, V>
where
    K: Ord + Clone + Deserialize<'de>,
    V: Deserialize<'de>,
{
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        deserializer.deserialize_map(MapVisitor(PhantomData))
    }
}

impl<T: Ord + Clone + Serialize> Serialize for BPlusTreeSet<T> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.collect_seq(self.iter())
    }
}

struct SetVisitor<T>(PhantomData<T>);

impl<'de, T: Ord + Clone + Deserialize<'de>> Visitor<'de> for SetVisitor<T> {
    type Value = BPlusTreeSet<T>;

    fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("a sequence")
    }

    fn visit_seq<A: SeqAccess<'de>>(self, mut access: A) -> Result<Self::Value, A::Error> {
        let mut set = BPlusTreeSet::new();
        while let Some(value) = access.next_element()? {
            set.insert(value);
        }
        Ok(set)
    }
}

impl<'de, T: Ord + Clone + Deserialize<'de>> Deserialize<'de> for BPlusTreeSet<T> {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        deserializer.deserialize_seq(SetVisitor(PhantomData))
    }
}
