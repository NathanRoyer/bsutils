//! A HashMap which doesn't store the keys, only their hashes.

use core::{marker::PhantomData, hash::{Hash, BuildHasher, Hasher as _}};
use litemap::LiteMap;

/// A HashMap which doesn't store the keys, only their hashes.
///
/// Here are the steps of a `get` operation:
/// 1. the key/index is hashed
/// 2. the internal LiteMap is searched for the resulting hash (this
///    operation is a [binary search](https://doc.rust-lang.org/nightly/core/primitive.slice.html#method.binary_search_by))
/// 3. the search result is returned
///
/// Note: non-sized keys are supported (`str`, for instance).
#[derive(Debug, Default)]
pub struct HashMap<K: ?Sized, V> {
    pub hash_to_value: LiteMap<u64, V>,
    _data: PhantomData<K>,
}

impl<K: ?Sized, V: Clone> Clone for HashMap<K, V> {
    fn clone(&self) -> Self {
        Self {
            hash_to_value: self.hash_to_value.clone(),
            _data: PhantomData,
        }
    }
}

impl<K: Hash + Ord + ?Sized, V> HashMap<K, V> {
    pub const fn new() -> Self {
        Self {
            hash_to_value: LiteMap::new(),
            _data: PhantomData,
        }
    }

    pub fn len(&self) -> usize {
        self.hash_to_value.len()
    }

    pub fn insert_ref(&mut self, key: &K, value: V) -> Option<V> {
        let mut hasher = super::GEN.build_hasher();
        key.hash(&mut hasher);
        self.hash_to_value.insert(hasher.finish(), value)
    }

    pub fn contains_key(&self, key: &K) -> bool {
        let mut hasher = super::GEN.build_hasher();
        key.hash(&mut hasher);
        self.hash_to_value.contains_key(&hasher.finish())
    }

    pub fn get(&self, key: &K) -> Option<&V> {
        let mut hasher = super::GEN.build_hasher();
        key.hash(&mut hasher);
        self.hash_to_value.get(&hasher.finish())
    }

    pub fn get_mut(&mut self, key: &K) -> Option<&mut V> {
        let mut hasher = super::GEN.build_hasher();
        key.hash(&mut hasher);
        self.hash_to_value.get_mut(&hasher.finish())
    }
}

impl<K: Hash + Ord, V> HashMap<K, V> {
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        self.insert_ref(&key, value)
    }
}
