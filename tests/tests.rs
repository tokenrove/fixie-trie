#![feature(inclusive_range_syntax)]

#[macro_use]
extern crate quickcheck;
use quickcheck::{Arbitrary, Gen};

extern crate rand;
use rand::Rand;

extern crate fixie_trie;
use fixie_trie::{FixieTrie, FixedLengthKey};
use std::fmt;
use std::collections::BTreeMap;

#[derive(PartialEq,Debug)]
struct ExplicitDrop<'a>(&'a mut bool);

impl<'a> Drop for ExplicitDrop<'a> {
    fn drop(&mut self) { *self.0 = true; }
}

#[test]
fn explicit_drop_test() {
    let mut canary = false;
    {
        let mut t = FixieTrie::new();
        assert_eq!(None, t.insert(42, ExplicitDrop(&mut canary)));
    }
    assert!(canary);
}

#[test]
fn full_occupancy() {
    let mut t = FixieTrie::new();
    for i in 0..=u16::max_value() {
        assert_eq!(None, t.insert(i, ()));
    }
    assert!(t.keys().zip(0..=u16::max_value()).all(|(a,b)| a == b));
    for i in 0..=u16::max_value() {
        assert!(t.contains(&i));
    }
}

#[test]
fn full_occupancy_u8() {
    let mut t = FixieTrie::new();
    for i in 0..=u8::max_value() {
        assert_eq!(None, t.insert(i, ()));
        for j in 0..=i {
            assert!(t.contains(&j), "{} {}", i, j);
        }
    }
    assert!(t.keys().zip(0..=u8::max_value()).all(|(a,b)| a == b));
    for i in 0..=u8::max_value() {
        assert!(t.contains(&i), "{}", i);
    }
}

fn insertion_test_helper<K,V>(v: Vec<(K,V)>) -> bool
    where K: FixedLengthKey + Ord,
          V: PartialEq + fmt::Debug {
    let mut t = FixieTrie::new();
    let mut bt = BTreeMap::new();
    for &(i,ref j) in v.iter() { assert_eq!(t.insert(i, j), bt.insert(i, j)); }
    for &(i,_) in v.iter() { assert_eq!(t.get(&i), bt.get(&i)); }
    true
}

#[derive(Copy, Clone, Debug)]
enum SetOperation<T: FixedLengthKey> {
    Insert(T),
    Remove(T),
    Query(T),
}

impl<T: Arbitrary + FixedLengthKey + Rand> Arbitrary for SetOperation<T> {
    fn arbitrary<G: Gen>(g: &mut G) -> SetOperation<T> {
        use self::SetOperation::*;
        match g.gen_range(0,3) {
            0 => Insert(g.gen()),
            1 => Remove(g.gen()),
            2 => Query(g.gen()),
            _ => panic!()
        }
    }
}

#[derive(Copy, Clone, Debug)]
enum MapOperation<K: FixedLengthKey, V> {
    Insert(K,V),
    Remove(K),
    Query(K),
}

impl<K,V> Arbitrary for MapOperation<K,V>
    where K: Arbitrary + FixedLengthKey + Rand,
          V: Arbitrary + Rand {
    fn arbitrary<G: Gen>(g: &mut G) -> MapOperation<K,V> {
        use self::MapOperation::*;
        match g.gen_range(0,3) {
            0 => Insert(g.gen(), g.gen()),
            1 => Remove(g.gen()),
            2 => Query(g.gen()),
            _ => panic!()
        }
    }
}

quickcheck! {
    fn droppable_insertion(v: Vec<u64>) -> bool {
        {
            let mut t = FixieTrie::new();
            for &i in v.iter() { t.insert(i, "leak memory".to_owned()); }
        }
        true
    }

    fn u16_insertion(v: Vec<(u16,u64)>) -> bool { insertion_test_helper(v) }
    fn u32_insertion(v: Vec<(u32,u64)>) -> bool { insertion_test_helper(v) }
    fn u64_insertion(v: Vec<(u64,u64)>) -> bool { insertion_test_helper(v) }

    #[cfg(feature = "i128")]
    fn u128_insertion(v: Vec<u32>) -> bool {
        // TODO BurntSushi/quickcheck#162
        use rand::Rng;
        let mut gen = ::rand::thread_rng();
        insertion_test(v.iter()
                       .map(|value| ((gen.next_u64() as u128) << 64 |
                                     gen.next_u64() as u128, value))
                       .collect::<Vec<_>>())
    }

    fn iteration_over_elements_in_sorted_order(v: Vec<u64>) -> bool {
        let mut t = FixieTrie::new();
        for &i in v.iter() { t.insert(i, ()); }
        let mut u = v.clone();
        u.sort();
        u.dedup();
        t.keys().zip(u.iter()).all(|(a,&b)| a == b)
    }

    fn equivalence_with_set(ops: Vec<SetOperation<u16>>) -> bool {
        use self::SetOperation::*;
        let mut us = FixieTrie::new();
        let mut them = ::std::collections::btree_set::BTreeSet::new();
        for op in ops {
            match op {
                Insert(k) => { assert_eq!(us.insert(k, ()).is_none(), them.insert(k)) },
                Remove(_k) => { //assert_eq!(us.remove(k), them.remove(k))
                },
                Query(k) => { assert_eq!(us.contains(&k), them.contains(&k)) },
            }
        }
        us.keys().zip(them.iter()).all(|(a,&b)| a == b)
    }

    fn equivalence_with_map(ops: Vec<MapOperation<u32,u64>>) -> bool {
        use self::MapOperation::*;
        let mut us = FixieTrie::new();
        let mut them = ::std::collections::btree_map::BTreeMap::new();
        for op in ops {
            match op {
                Insert(k, v) => { assert_eq!(us.insert(k, v), them.insert(k,v)) },
                Remove(_k) => { //assert_eq!(us.remove(k), them.remove(k))
                },
                Query(k) => { assert_eq!(us.get(&k), them.get(&k)) },
            }
        }
        us.keys().zip(them.keys()).all(|(a,&b)| us.get(&a) == them.get(&b))
    }

    fn repeatedly_replace_key(k: u32, vs: Vec<u32>, others: Vec<(u32,u32)>) -> bool {
        let mut t = FixieTrie::new();
        for (k,v) in others { t.insert(k,v); }
        let last =
            vs.iter().fold(t.get(&k).map(|&v|v), |expected_old, &v| {
                let actual_old = t.insert(k, v);
                assert_eq!(expected_old, actual_old);
                Some(v)
            });
        t.get(&k) == last.as_ref()
    }
}

#[test]
fn regression_on_sets() {
    let mut t = FixieTrie::new();
    assert_eq!(None, t.insert(0, ()));
    assert_eq!(None, t.insert(1, ()));
    assert!(t.contains(&0), "{:?}", t);
    assert!(t.contains(&1), "{:?}", t);
    assert!(!t.contains(&2), "{:?}", t);
    assert!(!t.contains(&3), "{:?}", t);
    assert!(!t.contains(&42), "{:?}", t);
    assert!(!t.contains(&4000), "{:?}", t);
}
