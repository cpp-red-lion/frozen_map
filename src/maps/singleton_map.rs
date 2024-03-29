use core::fmt::{Debug, Formatter, Result};
use core::hash::BuildHasher;

/// A map that holds a single item.
pub struct SingletonMap<K, V, BH: BuildHasher> {
    key: K,
    value: V,
    bh: BH,
}

impl<K, V, BH: BuildHasher> SingletonMap<K, V, BH> {
    pub const fn new(key: K, value: V, bh: BH) -> Self {
        Self { key, value, bh }
    }

    pub fn get(&self, key: &K) -> Option<&V>
    where
        K: Eq,
    {
        if key.eq(&self.key) {
            Some(&self.value)
        } else {
            None
        }
    }

    pub fn get_mut(&mut self, key: &K) -> Option<&mut V>
    where
        K: Eq,
    {
        if key.eq(&self.key) {
            Some(&mut self.value)
        } else {
            None
        }
    }

    pub fn get_kv(&self, key: &K) -> Option<(&K, &V)>
    where
        K: Eq,
    {
        if key.eq(&self.key) {
            Some((&self.key, &self.value))
        } else {
            None
        }
    }

    pub const fn get_by_index(&self, index: usize) -> Option<(&K, &V)> {
        if index == 0 {
            Some((&self.key, &self.value))
        } else {
            None
        }
    }

    pub const fn len(&self) -> usize {
        1
    }

    pub const fn hasher(&self) -> &BH {
        &self.bh
    }
}

impl<K, V, BH> Debug for SingletonMap<K, V, BH>
where
    K: Debug,
    V: Debug,
    BH: BuildHasher,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        f.debug_map().entries([(&self.key, &self.value)]).finish()
    }
}

#[cfg(test)]
mod tests {
    use std::hash::RandomState;

    use super::SingletonMap;

    #[test]
    fn new_creates_singleton_map_with_given_key_value() {
        let map = SingletonMap::new(10, 20, RandomState::new());
        assert_eq!(1, map.len());
        assert_eq!((&10, &20), map.get_kv(&10).unwrap());
    }

    #[test]
    fn get_returns_some_for_existing_key() {
        let map = SingletonMap::new(10, 20, RandomState::new());
        assert_eq!(&20, map.get(&10).unwrap());
    }

    #[test]
    fn get_returns_none_for_non_existing_key() {
        let map = SingletonMap::new(10, 20, RandomState::new());
        assert_eq!(None, map.get(&0));
    }

    #[test]
    fn get_mut_returns_some_for_existing_key() {
        let mut map = SingletonMap::new(10, 20, RandomState::new());
        assert_eq!(&20, map.get_mut(&10).unwrap());
    }

    #[test]
    fn get_mut_returns_none_for_non_existing_key() {
        let mut map = SingletonMap::new(10, 20, RandomState::new());
        assert_eq!(None, map.get_mut(&0));
    }

    #[test]
    fn get_key_value_returns_some_for_existing_key() {
        let map = SingletonMap::new(10, 20, RandomState::new());
        assert_eq!((&10, &20), map.get_kv(&10).unwrap());
    }

    #[test]
    fn get_key_value_returns_none_for_non_existing_key() {
        let map = SingletonMap::new(10, 20, RandomState::new());
        assert_eq!(None, map.get_kv(&0));
    }

    #[test]
    fn get_by_index_returns_some_for_existing_key() {
        let map = SingletonMap::new(10, 20, RandomState::new());
        assert_eq!((&10, &20), map.get_by_index(0).unwrap());
    }

    #[test]
    fn get_key_by_index_returns_none_for_non_existing_key() {
        let map = SingletonMap::new(10, 20, RandomState::new());
        assert_eq!(None, map.get_by_index(1));
    }

    #[test]
    fn debug_format_is_correct() {
        let map = SingletonMap::new(10, 20, RandomState::new());
        assert_eq!("{10: 20}", format!("{map:?}"));
    }
}
