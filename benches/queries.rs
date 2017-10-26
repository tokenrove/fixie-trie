#![feature(test)]
#![feature(inclusive_range_syntax)]

extern crate test;
use test::Bencher;

extern crate rand;
use rand::{Rand, Rng};

extern crate fixie_trie;
use fixie_trie::FixieTrie;

extern crate qp_trie;
use qp_trie::Trie as QpTrie;

use std::collections::btree_set::BTreeSet;
use std::collections::hash_set::HashSet;
use std::collections::btree_map::BTreeMap;
use std::collections::hash_map::HashMap;

mod common;
use common::{Set, Map};

const N_INSERTS: usize = 100000;

fn random_queries_on_a_set<T: Rand, S: Set<T>>(b: &mut Bencher, mut s: S)
{
    let mut rng = rand::thread_rng();
    for _ in 0..N_INSERTS { s.insert(rng.gen()); }
    b.iter(|| { s.contains(&(rng.gen())); });
}

fn random_queries_on_a_map<K: Rand, V: Rand, M: Map<K,V>>(b: &mut Bencher, mut m: M)
{
    let mut rng = rand::thread_rng();
    for _ in 0..N_INSERTS { m.insert(rng.gen(), rng.gen()); }
    b.iter(|| { m.get(&(rng.gen())); });
}

#[bench]
fn u32_random_queries_on_a_qp_trie_set(b: &mut Bencher)
{
    let mut rng = rand::thread_rng();
    let mut s = QpTrie::new();
    for _ in 0..N_INSERTS { s.insert(rng.gen::<[u8; 4]>(), ()); }
    b.iter(|| { s.get(&(rng.gen::<[u8; 4]>())); });
}

#[bench]
fn u64_random_queries_on_fixie_trie_set(b: &mut Bencher)
{
    random_queries_on_a_set::<u64, _>(b, FixieTrie::new());
}

#[bench]
fn u64_random_queries_on_btree_set(b: &mut Bencher)
{
    random_queries_on_a_set::<u64, _>(b, BTreeSet::new());
}

#[bench]
fn u64_random_queries_on_hash_set(b: &mut Bencher)
{
    random_queries_on_a_set::<u64, _>(b, HashSet::new());
}

#[bench]
fn u64_random_queries_on_fixie_trie(b: &mut Bencher)
{
    random_queries_on_a_map::<u64, u32, _>(b, FixieTrie::new());
}

#[bench]
fn u64_random_queries_on_btree_map(b: &mut Bencher)
{
    random_queries_on_a_map::<u64, u32, _>(b, BTreeMap::new());
}

#[bench]
fn u64_random_queries_on_hash_map(b: &mut Bencher)
{
    random_queries_on_a_map::<u64, u32, _>(b, HashMap::new());
}



#[bench]
fn u32_random_queries_on_fixie_trie_set(b: &mut Bencher)
{
    random_queries_on_a_set::<u32, _>(b, FixieTrie::new());
}

#[bench]
fn u32_random_queries_on_btree_set(b: &mut Bencher)
{
    random_queries_on_a_set::<u32, _>(b, BTreeSet::new());
}

#[bench]
fn u32_random_queries_on_hash_set(b: &mut Bencher)
{
    random_queries_on_a_set::<u32, _>(b, HashSet::new());
}


fn random_queries_on_complete_u16_set<S: Set<u16>>(b: &mut Bencher, mut s: S)
{
    for i in 0..=u16::max_value() { s.insert(i); }
    let mut rng = rand::thread_rng();
    b.iter(|| { s.contains(&(rng.gen())); });
}

#[bench]
fn random_queries_on_complete_u16_qp_trie_set(b: &mut Bencher)
{
    let mut s = QpTrie::new();
    for i in 0..=u16::max_value() {
        s.insert([i as u8, (i>>8) as u8], ());
    }
    let mut rng = rand::thread_rng();
    b.iter(|| { s.get(&(rng.gen::<[u8; 2]>())); });
}

#[bench]
fn random_queries_on_complete_u16_fixie_trie_set(b: &mut Bencher)
{
    random_queries_on_complete_u16_set(b, FixieTrie::new());
}

#[bench]
fn random_queries_on_complete_u16_btree_set(b: &mut Bencher)
{
    random_queries_on_complete_u16_set(b, BTreeSet::new());
}

#[bench]
fn random_queries_on_complete_u16_hash_set(b: &mut Bencher)
{
    random_queries_on_complete_u16_set(b, HashSet::new());
}
