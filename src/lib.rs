//! Popcount-array radix tries for fixed-length keys.

#![warn(
    missing_copy_implementations,
    missing_docs,
    trivial_numeric_casts,
    unused_extern_crates,
    unused_import_braces,
    variant_size_differences,
)]

#![feature(allocator_api)]
#![cfg_attr(feature = "i128", feature(i128_type))]

// For valgrind, because of rust-lang/rust#28224
//#![cfg_attr(test, feature(alloc_system))]

#[cfg(test)]
#[macro_use]
extern crate quickcheck;
#[cfg(all(feature = "i128", test))]
extern crate rand;

use std::heap::{Heap, Alloc, Layout};

use std::{fmt, mem, ptr, slice};
use std::marker::PhantomData;

#[cfg(all(target_pointer_width = "64", target_arch = "x86_64"))]
type TriePtr = u64;

/// A key that can be used with a `FixieTrie`.  We need to be able to
/// get nibbles out of it and reconstruct it from nibbles.
///
/// XXX Properly the construction interface should be something
/// cleaner rather requiring you to mutate an instance of this.
pub trait FixedLengthKey: PartialEq + Copy {
    /// How many nibbles are in this key?
    fn levels() -> usize;
    /// The `idx`th nibble.
    fn nibble(&self, idx: usize) -> u8;
    /// An empty key to be fed nibbles via `concat_nibble`.
    fn empty() -> Self;
    /// Append `nibble` to this key.
    fn concat_nibble(&mut self, nibble: u8);
}

// It should be possible to implement this for arbitrary types
// implementing BitAnd and friends, but my attempts to do so were
// constantly thwarted.
macro_rules! trivial_fixed_length_key_impl {
    ($($name:ident,)*) => {
        $(#[allow(trivial_numeric_casts)] impl FixedLengthKey for $name {
            fn levels() -> usize { 2 * mem::size_of::<Self>() }
            fn nibble(&self, idx: usize) -> u8 {
                ((*self >> (4*(Self::levels()-idx-1))) & 15) as u8
            }
            fn empty() -> Self { 0 }
            fn concat_nibble(&mut self, nibble: u8) {
                *self = (*self << 4) | (nibble as Self)
            }
        })*
    }
}

trivial_fixed_length_key_impl! {
    u8, u16, u32, u64,
    i16, i32, i64,
}
#[cfg(feature = "i128")]
trivial_fixed_length_key_impl! {
    i128, u128,
}

/// A popcount-array radix trie with fixed-length keys.
pub struct FixieTrie<K, V> where K: FixedLengthKey {
    root: TriePtr,
    phantom: PhantomData<(K, V)>,
}

fn is_empty(p: TriePtr) -> bool { 0 == p }
fn is_branch(p: TriePtr) -> bool { 1 == 1 & p }

fn branch_count(p: TriePtr) -> usize {
    assert!(is_branch(p));
    (p >> 48).count_ones() as usize
}

fn twigs_of_branch<'a>(p: TriePtr) -> &'a mut [TriePtr] {
    unsafe { slice::from_raw_parts_mut(ptr_of_branch(p), branch_count(p)) }
}

fn encode_branch(bitmap: u16, q: TriePtr) -> TriePtr {
    assert_eq!(0, q >> 48);
    1 | q | ((bitmap as u64) << 48)
}

fn bitmap_of_branch(p: TriePtr) -> u16 {
    assert!(is_branch(p));
    (p >> 48) as u16
}

fn ptr_of_branch(p: TriePtr) -> *mut TriePtr {
    (p & 0x0000_ffff_ffff_fffe) as *mut TriePtr
}

fn bits_in_branch(p: TriePtr, bit: u8) -> Option<usize> {
    assert!(is_branch(p));
    let map = p >> 48;
    assert!(bit < 16);
    let i = 1_u64 << bit;
    if i != map & i { return None }
    Some((map & (i-1)).count_ones() as usize)
}

#[test]
fn bits_in_branch_sanity_checks() {
    assert_eq!(None, bits_in_branch(encode_branch(0,0), 0b0100));
    assert_eq!(None, bits_in_branch(encode_branch(0b0000_0000_0001_0000, 0),
                                    0b0101));
    assert_eq!(Some(0), bits_in_branch(encode_branch(0b0000_0000_0001_0000, 0),
                                       0b0100));
    assert_eq!(Some(4), bits_in_branch(encode_branch(0b0000_0000_0001_1111, 0),
                                       0b0100));
}

fn layout(size: usize, align: usize) -> Layout {
    Layout::from_size_align(size, align).expect("Invalid memory layout.")
}

#[inline]
unsafe fn allocate(size: usize, align: usize) -> *mut u8 {
    Heap.alloc(layout(size, align)).expect("Heap allocation failed.")
}

#[inline]
unsafe fn reallocate(ptr: *mut u8, old_size: usize, new_size: usize, align: usize) -> *mut u8 {
    Heap.realloc(ptr, layout(old_size, align), layout(new_size, align))
        .expect("Heap reallocation failed.")
}

#[inline]
unsafe fn deallocate(ptr: *mut u8, size: usize, align: usize) {
    Heap.dealloc(ptr, layout(size, align));
}

impl<'a, K, V> FixieTrie<K, V> where K: FixedLengthKey {
    /// Constructs an empty fixie trie.
    pub fn new() -> Self {
        Self {
            root: 0,
            phantom: PhantomData,
        }
    }

    fn new_tuple_twig(key: K, value: V) -> TriePtr {
        unsafe {
            let p = allocate(mem::size_of::<(K,V)>(), mem::align_of::<(K,V)>()) as *mut (K,V);
            assert!(!p.is_null());
            ptr::write(p, (key, value));
            p as u64
        }
    }

    fn new_value(value: V) -> TriePtr {
        if mem::size_of::<V>() == 0 { return 0 }
        unsafe {
            let new = allocate(mem::size_of::<V>(), mem::align_of::<V>()) as *mut V;
            assert!(!new.is_null());
            ptr::write(new, value);
            new as TriePtr
        }
    }

    fn new_twig(level: usize, key: K, value: V) -> TriePtr {
        if level == K::levels()-1 {
            Self::new_value(value)
        } else {
            Self::new_tuple_twig(key, value)
        }
    }

    fn value_of_leaf(p: TriePtr) -> Option<&'a V> {
        unsafe { (p as *const V).as_ref() }
    }

    fn value_of_leaf_mut(p: TriePtr) -> Option<&'a mut V> {
        unsafe { (p as *mut V).as_mut() }
    }

    fn tuple_of_leaf(p: TriePtr) -> Option<&'a (K, V)> {
        unsafe { (p as *const (K,V)).as_ref() }
    }

    fn tuple_of_leaf_mut(p: TriePtr) -> Option<&'a mut (K, V)> {
        unsafe { (p as *mut (K,V)).as_mut() }
    }

    fn branch_elt(p: TriePtr, level: usize, key: &K) -> Option<TriePtr> {
        bits_in_branch(p, key.nibble(level)).map(|i| twigs_of_branch(p)[i])
    }

    fn find_leaf_and_level(&self, key: &K) -> (TriePtr, usize) {
        let mut p = self.root;
        let mut level = 0;
        while is_branch(p) {
            assert!(level < K::levels());
            if let Some(q) = Self::branch_elt(p, level, key) {
                p = q;
            } else { return (0, level) }
            level += 1;
        }
        (p, level)
    }

    /// Gets the value associated with `key`.
    pub fn get(&self, key: &K) -> Option<&V> {
        let (p, level) = self.find_leaf_and_level(key);
        if p == 0 { return None }
        if level == K::levels() { return Self::value_of_leaf(p) }

        match Self::tuple_of_leaf(p) {
            Some(&(ref other_key, ref value)) if key == other_key =>
                Some(value),
            _ => None,
        }
    }

    /// Gets the value associated with `key`.
    pub fn get_mut(&mut self, key: &K) -> Option<&mut V> {
        let (p, level) = self.find_leaf_and_level(key);
        if p == 0 { return None }
        if level == K::levels() { return Self::value_of_leaf_mut(p) }
        match Self::tuple_of_leaf_mut(p) {
            Some(&mut (ref other_key, ref mut value)) if key == other_key =>
                Some(value),
            _ => None,
        }
    }

    // extend the trie a level
    fn leaf_into_branch(p: *mut TriePtr, old_bits: u8) -> *mut TriePtr {
        unsafe {
            let q = allocate(mem::size_of::<TriePtr>(), mem::align_of::<TriePtr>()) as *mut TriePtr;
            assert!(!q.is_null());
            ptr::write(q, mem::replace(p.as_mut().unwrap(),
                                       encode_branch((1<<old_bits), q as TriePtr)));
            q
        }
    }

    // Transform a key-value pair into just a value item, at the end
    // of the trie where the key is implicit.
    //
    // It would be nice to realloc here, but we'd have to deal with
    // guarantees like what if the alignment of V is stricter than the
    // alignment of (K,V); perhaps this is always ok, but I haven't
    // thought it through.
    fn tuple_into_value(p: TriePtr) -> TriePtr {
        unsafe {
            let (_key, value) = ptr::read(p as *mut (K,V));
            let new = Self::new_value(value);
            deallocate(p as *mut u8,
                             mem::size_of::<(K,V)>(),
                             mem::align_of::<(K,V)>());
            new
        }
    }

    /// Inserts a mapping from `key` to `value`, returning the old
    /// value associated with `key` if there was one.
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        let mut place = &mut self.root;
        let mut level = 0;
        while is_branch(*place) {
            let bits = key.nibble(level);
            if let Some(i) = bits_in_branch(*place, bits) {
                place = &mut twigs_of_branch(*place)[i];
                level += 1;
            } else {
                *place = Self::expand_branch(*place, level, key, value);
                return None
            }
        }

        if level == K::levels() { // final level, _has_ to be just a *V
            return Self::value_of_leaf_mut(*place).map(|p| mem::replace(p, value))
        }

        if let Some(&mut (other_key, ref mut old_value)) = Self::tuple_of_leaf_mut(*place) {
            if key == other_key {
                return Some(mem::replace(old_value, value))
            }

            loop {
                let old_bits = other_key.nibble(level);
                if key.nibble(level) != old_bits { break; }
                place = unsafe { Self::leaf_into_branch(place, old_bits).as_mut().unwrap() };
                level += 1;
            }
            assert!(level < K::levels());

            if level == K::levels()-1 {
                *place = Self::tuple_into_value(*place);
            }

            let new_branch = unsafe {
                allocate(2*mem::size_of::<TriePtr>(),
                               mem::align_of::<TriePtr>()) as *mut TriePtr
            };
            assert!(!new_branch.is_null());

            let new_bits = key.nibble(level);
            let old_bits = other_key.nibble(level);
            let (old_idx, new_idx) =
                if new_bits > old_bits { (0,1) } else { (1,0) };
            unsafe {
                ptr::write(new_branch.offset(new_idx), Self::new_twig(level, key, value));
                ptr::write(new_branch.offset(old_idx), *place);
            };
            *place = encode_branch((1<<new_bits) | (1<<old_bits), new_branch as TriePtr);
        } else {
            *place = Self::new_tuple_twig(key, value);
        }
        None
    }

    fn expand_branch(branch: TriePtr, level: usize, key: K, value: V) -> TriePtr {
        let tptr_size = mem::size_of::<TriePtr>();
        let bitmap = bitmap_of_branch(branch);
        let count = bitmap.count_ones() as usize;
        let old_size = count * tptr_size;
        let bits = key.nibble(level);
        let bitmap = bitmap | 1<<bits;
        let idx = (bitmap & ((1<<bits) - 1)).count_ones() as isize;
        unsafe {
            let new = reallocate(ptr_of_branch(branch) as *mut u8,
                                       old_size,
                                       old_size + tptr_size,
                                       mem::align_of::<TriePtr>()) as *mut TriePtr;
            assert!(!new.is_null());
            ptr::copy(new.offset(idx),
                      new.offset(1+idx),
                      count - idx as usize);
            ptr::write(new.offset(idx), Self::new_twig(level, key, value));
            encode_branch(bitmap, new as u64)
        }
    }

    /// Is this trie empty?
    pub fn is_empty(&self) -> bool {
        is_empty(self.root)
    }

    /// Creates an iterator over the keys of this trie, in sorted
    /// order.
    pub fn keys(&'a self) -> Keys<'a, K, V> {
        Keys {
            inner: self.iter()
        }
    }

    /// Creates an iterator over the key-value pairs of this trie, in
    /// sorted order.
    pub fn iter(&'a self) -> Iter<'a, K, V> {
        Iter {
            stack: vec![Iteration {
                key: K::empty(),
                level: 0,
                bits: 0,
                place: self.root,
            }],
            phantom: PhantomData,
        }
    }
}

impl<K, V> Drop for FixieTrie<K, V> where K: FixedLengthKey {
    fn drop(&mut self) {
        let mut stack = vec![(0,0,self.root)];
        while let Some((bits, level, p)) = stack.pop() {
            assert!(bits < 16);
            if is_empty(p) { continue }
            if !is_branch(p) { // leaf
                let (size, align) =
                    if level < K::levels() {
                        unsafe {
                            let (_k,v) = ptr::read(p as *mut (K,V));
                            mem::drop(v);
                        };
                        (mem::size_of::<(K,V)>(), mem::align_of::<(K,V)>())
                    } else {
                        if mem::size_of::<V>() == 0 { continue; }
                        unsafe { ptr::drop_in_place(p as *mut V) };
                        (mem::size_of::<V>(), mem::align_of::<V>())
                    };
                unsafe {
                    deallocate(p as *mut u8, size, align);
                };
                continue;
            }

            let mask = (1<<bits)-1;
            let bitmap = bitmap_of_branch(p) & !mask;
            let next_bits = bitmap.trailing_zeros();
            if next_bits < 16 {
                let mask = (1<<next_bits)-1;
                let idx = (bitmap_of_branch(p) & mask).count_ones();
                if next_bits < 15 {
                    stack.push((1+next_bits, level, p));
                }
                unsafe {
                    stack.push((0, 1+level, *ptr_of_branch(p).offset(idx as isize)));
                }
            }
            if next_bits >= 15 {
                unsafe {
                    deallocate(ptr_of_branch(p) as *mut u8,
                                     mem::size_of::<TriePtr>() * branch_count(p),
                                     mem::align_of::<TriePtr>());
                }
            }
        }
     }
}

impl<K, V> fmt::Debug for FixieTrie<K, V>
    where K: FixedLengthKey + fmt::Debug,
          V: fmt::Debug {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> std::result::Result<(), fmt::Error> {
        fmt.debug_map().entries(self.into_iter()).finish()
    }
}

struct Iteration<K> {
    key: K,
    level: usize,
    bits: u32,
    place: TriePtr,
}

/// Iterator over a fixie trie.
pub struct Iter<'a, K, V> where K: 'a, V: 'a {
    stack: Vec<Iteration<K>>,
    phantom: PhantomData<&'a (K, V)>,
}

impl<'a, K: 'a, V: 'a> Iterator for Iter<'a, K, V> where K: FixedLengthKey {
    type Item = (K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(it) = self.stack.pop() {
            let mut key = it.key;
            assert!(it.level <= K::levels());
            assert!(it.bits < 16);
            if is_empty(it.place) { return None }
            if !is_branch(it.place) { // leaf
                let maybe_kv = if it.level == K::levels() {
                    FixieTrie::<K,V>::value_of_leaf(it.place).map(|v| (key, v))
                } else {
                    FixieTrie::<K,V>::tuple_of_leaf(it.place).map(|kv| (kv.0, &kv.1))
                };
                if maybe_kv.is_some() { return maybe_kv }
                continue;
            }

            let mask = (1<<it.bits)-1;
            let bitmap = bitmap_of_branch(it.place) & !mask;
            let next_bits = bitmap.trailing_zeros();
            if next_bits >= 16 { continue; }
            let mask = (1<<next_bits)-1;
            let idx = (bitmap_of_branch(it.place) & mask).count_ones();
            if next_bits < 15 {
                self.stack.push(Iteration {
                    key: it.key,
                    level: it.level,
                    bits: 1+next_bits,
                    place: it.place
                });
            }
            unsafe {
                key.concat_nibble(next_bits as u8);
                self.stack.push(Iteration {
                    key: key,
                    level: 1+it.level,
                    bits: 0,
                    place: *ptr_of_branch(it.place).offset(idx as isize)
                });
            }
        }
        None
    }
}

/// Iterator over keys of a trie.
pub struct Keys<'a, K: 'a, V: 'a> {
    inner: Iter<'a, K, V>,
}

impl<'a, K: 'a, V: 'a> Iterator for Keys<'a, K, V> where K: FixedLengthKey {
    type Item = K;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|o| o.0)
    }
}

impl<'a, K, V> IntoIterator for &'a FixieTrie<K, V>
    where K: FixedLengthKey {
    type Item = (K, &'a V);
    type IntoIter = Iter<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

#[cfg(test)]
mod test {
    use super::{FixieTrie, FixedLengthKey};
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
        use std::u16;
        let mut t = FixieTrie::new();
        for i in 0..u16::MAX {
            assert_eq!(None, t.insert(i, Box::new(())));
        }
        assert!(t.keys().zip(0..u16::MAX).all(|(a,b)| a == b));
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
}
