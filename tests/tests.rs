#![feature(inclusive_range_syntax)]

#[macro_use]
extern crate quickcheck;
#[cfg(all(feature = "i128", test))]
extern crate rand;

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
        assert_eq!(None, t.insert(i, Box::new(())));
    }
    assert!(t.keys().zip(0..=u16::max_value()).all(|(a,b)| a == b));
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

    // repeatedly replace key
}
