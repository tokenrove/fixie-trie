
use std::collections::btree_set::BTreeSet;
use std::collections::hash_set::HashSet;
use std::collections::btree_map::BTreeMap;
use std::collections::hash_map::HashMap;

extern crate fixie_trie;
use fixie_trie::{FixieTrie, FixedLengthKey};

pub trait Set<T> {
    fn contains(&self, value: &T) -> bool;
    fn insert(&mut self, value: T) -> bool;
}

impl<T: FixedLengthKey> Set<T> for FixieTrie<T, ()> {
    fn contains(&self, value: &T) -> bool { self.get(value).is_some() }
    fn insert(&mut self, value: T) -> bool {
        FixieTrie::insert(self, value, ()).is_none()
    }
}

impl<T: ::std::cmp::Ord> Set<T> for BTreeSet<T> {
    fn contains(&self, value: &T) -> bool { BTreeSet::contains(self, value) }
    fn insert(&mut self, value: T) -> bool { BTreeSet::insert(self, value) }
}

impl<T: ::std::cmp::Eq + ::std::hash::Hash> Set<T> for HashSet<T> {
    fn contains(&self, value: &T) -> bool { HashSet::contains(self, value) }
    fn insert(&mut self, value: T) -> bool { HashSet::insert(self, value) }
}

pub trait Map<K,V> {
    fn get(&self, key: &K) -> Option<&V>;
    fn insert(&mut self, key: K, value: V) -> Option<V>;
}

impl<K: fixie_trie::FixedLengthKey, V> Map<K,V> for FixieTrie<K,V> {
    fn get(&self, key: &K) -> Option<&V> { FixieTrie::get(self, key) }
    fn insert(&mut self, key: K, value: V) -> Option<V> { FixieTrie::insert(self, key, value) }
}

impl<K: ::std::cmp::Ord, V> Map<K,V> for BTreeMap<K,V> {
    fn get(&self, key: &K) -> Option<&V> { BTreeMap::get(self, key) }
    fn insert(&mut self, key: K, value: V) -> Option<V> { BTreeMap::insert(self, key, value) }
}

impl<K: ::std::cmp::Eq + ::std::hash::Hash, V> Map<K,V> for HashMap<K,V> {
    fn get(&self, key: &K) -> Option<&V> { HashMap::get(self, key) }
    fn insert(&mut self, key: K, value: V) -> Option<V> { HashMap::insert(self, key, value) }
}
