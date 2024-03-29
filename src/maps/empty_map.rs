use core::fmt::{Debug, Formatter, Result};
use core::hash::BuildHasher;
use core::marker::PhantomData;

/// A map that holds no items.
pub struct EmptyMap<K, V, BH: BuildHasher> {
    bh: BH,
    key: PhantomData<K>,
    value: PhantomData<V>,
}

impl<K, V, BH: BuildHasher> EmptyMap<K, V, BH> {
    pub const fn new(bh: BH) -> Self {
        Self {
            bh,
            key: PhantomData,
            value: PhantomData,
        }
    }

    pub const fn get(&self, _key: &K) -> Option<&V> {
        None
    }

    pub fn get_mut(&mut self, _key: &K) -> Option<&mut V> {
        None
    }

    pub const fn get_kv(&self, _key: &K) -> Option<(&K, &V)> {
        None
    }

    pub const fn get_by_index(&self, _index: usize) -> Option<(&K, &V)> {
        None
    }

    pub const fn len(&self) -> usize {
        0
    }

    pub const fn hasher(&self) -> &BH {
        &self.bh
    }
}

impl<K, V, BH: BuildHasher> Debug for EmptyMap<K, V, BH> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        f.write_str("{}")
    }
}

#[cfg(test)]
mod tests {
    use std::hash::RandomState;

    use super::EmptyMap;

    #[test]
    fn new_creates_empty_map() {
        let map: EmptyMap<u32, u32, RandomState> = EmptyMap::new(RandomState::new());
        assert_eq!(0, map.len());
    }

    #[test]
    fn get_returns_none() {
        let map = EmptyMap::<u32, u32, RandomState>::new(RandomState::new());
        assert_eq!(None, map.get(&0));
    }

    #[test]
    fn get_mut_returns_none() {
        let mut map = EmptyMap::<u32, u32, RandomState>::new(RandomState::new());
        assert_eq!(None, map.get_mut(&0));
    }

    #[test]
    fn get_key_value_returns_none() {
        let map = EmptyMap::<u32, u32, RandomState>::new(RandomState::new());
        assert_eq!(None, map.get_kv(&0));
    }

    #[test]
    fn get_by_index_returns_none() {
        let map = EmptyMap::<u32, u32, RandomState>::new(RandomState::new());
        assert_eq!(None, map.get_by_index(0));
    }

    #[test]
    fn debug_format_is_empty_braces() {
        let map = EmptyMap::<u32, u32, RandomState>::new(RandomState::new());
        assert_eq!("{}", format!("{map:?}"));
    }
}
