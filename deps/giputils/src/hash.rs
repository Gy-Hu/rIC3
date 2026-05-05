use ahash::{HashMap, HashSet, RandomState};
use std::{
    collections::{hash_map, hash_set},
    hash::Hash,
    ops::{Deref, DerefMut},
};

#[derive(Debug, Clone)]
pub struct GHashSet<T> {
    h: HashSet<T>,
}

impl<T> GHashSet<T> {
    pub fn new() -> Self {
        let hb = RandomState::with_seeds(0, 0, 0, 0);
        Self {
            h: HashSet::with_hasher(hb),
        }
    }
}

impl<T> Deref for GHashSet<T> {
    type Target = HashSet<T>;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.h
    }
}

impl<T> DerefMut for GHashSet<T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.h
    }
}

impl<T> Default for GHashSet<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> IntoIterator for GHashSet<T> {
    type Item = T;

    type IntoIter = hash_set::IntoIter<T>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.h.into_iter()
    }
}

impl<T: Eq + Hash> FromIterator<T> for GHashSet<T> {
    #[inline]
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let hb = RandomState::with_seeds(0, 0, 0, 0);
        let mut h = HashSet::with_hasher(hb);
        h.extend(iter);
        Self { h }
    }
}

#[derive(Debug, Clone)]
pub struct GHashMap<K, V> {
    h: HashMap<K, V>,
}

impl<K, V> GHashMap<K, V> {
    pub fn new() -> Self {
        let hb = RandomState::with_seeds(0, 0, 0, 0);
        Self {
            h: HashMap::with_hasher(hb),
        }
    }
}

impl<K, V> Deref for GHashMap<K, V> {
    type Target = HashMap<K, V>;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.h
    }
}

impl<K, V> DerefMut for GHashMap<K, V> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.h
    }
}

impl<K, V> Default for GHashMap<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K, V> IntoIterator for GHashMap<K, V> {
    type Item = (K, V);

    type IntoIter = hash_map::IntoIter<K, V>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.h.into_iter()
    }
}

impl<K: Eq + Hash, V> FromIterator<(K, V)> for GHashMap<K, V> {
    #[inline]
    fn from_iter<I: IntoIterator<Item = (K, V)>>(iter: I) -> Self {
        let hb = RandomState::with_seeds(0, 0, 0, 0);
        let mut h = HashMap::with_hasher(hb);
        h.extend(iter);
        Self { h }
    }
}
