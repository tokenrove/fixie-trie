#![feature(inclusive_range_syntax)]

#![feature(test)]
extern crate test;

extern crate rand;
use rand::Rng;

extern crate fixie_trie;
use fixie_trie::FixieTrie;

use std::collections::btree_set::BTreeSet;
use std::collections::hash_set::HashSet;
use std::collections::btree_map::BTreeMap;
use std::collections::hash_map::HashMap;

trait Set<T> {
    fn contains(&self, value: &T) -> bool;
    fn insert(&mut self, value: T) -> bool;
}

impl<T: fixie_trie::FixedLengthKey> Set<T> for FixieTrie<T, ()> {
    fn contains(&self, value: &T) -> bool { FixieTrie::contains(self, value) }
    fn insert(&mut self, value: T) -> bool {
        FixieTrie::insert(self, value, ()).is_none()
    }
}

impl<T: std::cmp::Ord> Set<T> for BTreeSet<T> {
    fn contains(&self, value: &T) -> bool { BTreeSet::contains(self, value) }
    fn insert(&mut self, value: T) -> bool { BTreeSet::insert(self, value) }
}

impl<T: std::cmp::Eq + std::hash::Hash> Set<T> for HashSet<T> {
    fn contains(&self, value: &T) -> bool { HashSet::contains(self, value) }
    fn insert(&mut self, value: T) -> bool { HashSet::insert(self, value) }
}

fn test_set_insertions<S: Set<u64>>(n_insertions: usize, mut s: S)
{
    let mut rng = rand::thread_rng();
    for _ in 0..n_insertions { s.insert(rng.gen()); }
}

trait Map<K,V> {
    fn get(&self, key: &K) -> Option<&V>;
    fn insert(&mut self, key: K, value: V) -> Option<V>;
}

impl<K: fixie_trie::FixedLengthKey, V> Map<K,V> for FixieTrie<K,V> {
    fn get(&self, key: &K) -> Option<&V> { FixieTrie::get(self, key) }
    fn insert(&mut self, key: K, value: V) -> Option<V> { FixieTrie::insert(self, key, value) }
}

impl<K: std::cmp::Ord, V> Map<K,V> for BTreeMap<K,V> {
    fn get(&self, key: &K) -> Option<&V> { BTreeMap::get(self, key) }
    fn insert(&mut self, key: K, value: V) -> Option<V> { BTreeMap::insert(self, key, value) }
}

impl<K: std::cmp::Eq + std::hash::Hash, V> Map<K,V> for HashMap<K,V> {
    fn get(&self, key: &K) -> Option<&V> { HashMap::get(self, key) }
    fn insert(&mut self, key: K, value: V) -> Option<V> { HashMap::insert(self, key, value) }
}

fn test_map_insertions<M: Map<u64, u32>>(n_insertions: usize, mut m: M)
{
    let mut rng = rand::thread_rng();
    for _ in 0..n_insertions { m.insert(rng.gen(), rng.gen()); }
}

extern crate qp_trie;
use qp_trie::Trie as QpTrie;

fn test_qptrie_set_insertions(n_insertions: usize)
{
    let mut t = QpTrie::new();
    let mut rng = rand::thread_rng();
    for _ in 0..n_insertions {
        t.insert(rng.gen::<[u8;8]>(), ());
    }
}

fn test_qptrie_map_insertions(n_insertions: usize)
{
    let mut t = QpTrie::new();
    let mut rng = rand::thread_rng();
    for _ in 0..n_insertions {
        t.insert(rng.gen::<[u8;8]>(), rng.gen::<[u8;4]>());
    }
}

fn main() {
    let mut args = std::env::args();
    let name = args.next().unwrap();
    let strategy = args.next().unwrap();
    let n_insertions = args.next().unwrap().parse().unwrap();
    if args.next().is_some() {
        panic!("usage: {} STRATEGY N_INSERTIONS", name);
    }
    match strategy.as_str() {
        "btree_set" => test_set_insertions(n_insertions, BTreeSet::new()),
        "fixie_trie_set" => test_set_insertions(n_insertions, FixieTrie::new()),
        "hash_set" => test_set_insertions(n_insertions, HashSet::new()),
        "qp_trie_set" => test_qptrie_set_insertions(n_insertions),
        "btree_map" => test_map_insertions(n_insertions, BTreeMap::new()),
        "fixie_trie" => test_map_insertions(n_insertions, FixieTrie::new()),
        "hash_map" => test_map_insertions(n_insertions, HashMap::new()),
        "qp_trie" => test_qptrie_map_insertions(n_insertions),
        _ => panic!("unknown strategy: {}", strategy),
    };
}
