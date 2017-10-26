#![feature(test)]

extern crate test;
use test::Bencher;

extern crate fixie_trie;
use fixie_trie::FixieTrie;

extern crate rand;
use rand::{Rand, Rng};

use std::collections::btree_set::BTreeSet;
use std::collections::hash_set::HashSet;
use std::collections::btree_map::BTreeMap;
use std::collections::hash_map::HashMap;

mod common;
use common::{Set, Map};

const N_INSERTS: usize = 10000;

fn random_insertions_on_a_set<T: Rand, S: Set<T>>(b: &mut Bencher, new: fn () -> S)
{
    let mut rng = rand::thread_rng();
    let mut s = new();
    for _ in 0..N_INSERTS {
        s.insert(rng.gen());
    }

    // This seems to be the most congruent way to use cargo bench, as
    // it isn't possible to insert untimed setup/teardown outside of
    // an iteration, but it is methodologically flawed: we are
    // changing the structure as we go, so we are not measuring the
    // same thing every iteration.  If we try to build up a set in the
    // iter loop, we end up measuring the time of setting up and
    // tearing down the structure.
    b.iter(|| { s.insert(rng.gen()); });
}

#[bench]
fn random_u64_insertions_on_fixie_trie_as_set(b: &mut Bencher)
{
    random_insertions_on_a_set::<u64, _>(b, FixieTrie::new);
}

#[bench]
fn random_u64_insertions_on_btree_set(b: &mut Bencher)
{
    random_insertions_on_a_set::<u64, _>(b, BTreeSet::new);
}

#[bench]
fn random_u64_insertions_on_hash_set(b: &mut Bencher)
{
    random_insertions_on_a_set::<u64, _>(b, HashSet::new);
}

#[bench]
fn random_u32_insertions_on_fixie_trie_as_set(b: &mut Bencher)
{
    random_insertions_on_a_set::<u32, _>(b, FixieTrie::new);
}

#[bench]
fn random_u32_insertions_on_btree_set(b: &mut Bencher)
{
    random_insertions_on_a_set::<u32, _>(b, BTreeSet::new);
}

#[bench]
fn random_u32_insertions_on_hash_set(b: &mut Bencher)
{
    random_insertions_on_a_set::<u32, _>(b, HashSet::new);
}

fn random_insertions_on_a_map<K: Rand, V: Rand, M: Map<K,V>>(b: &mut Bencher, new: fn () -> M)
{
    let mut rng = rand::thread_rng();
    let mut m = new();
    for _ in 0..N_INSERTS { m.insert(rng.gen(), rng.gen()); }
    // See comments in random_insertions_on_a_set.
    b.iter(|| { m.insert(rng.gen(), rng.gen()); });
}

#[bench]
fn random_u64_insertions_on_fixie_trie_as_map(b: &mut Bencher)
{
    random_insertions_on_a_map::<u64, u32, _>(b, FixieTrie::new);
}

#[bench]
fn random_u64_insertions_on_btree_map(b: &mut Bencher)
{
    random_insertions_on_a_map::<u64, u32, _>(b, BTreeMap::new);
}

#[bench]
fn random_u64_insertions_on_hash_map(b: &mut Bencher)
{
    random_insertions_on_a_map::<u64, u32, _>(b, HashMap::new);
}
