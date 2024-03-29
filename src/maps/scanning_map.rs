use core::fmt::{Debug, Formatter, Result};
use core::hash::BuildHasher;

/// A map that does a linear scan of items, designed for very small maps.
pub struct ScanningMap<K, V, const N: usize, BH: BuildHasher> {
    entries: [(K, V); N],
    bh: BH,
}

impl<K, V, const N: usize, BH: BuildHasher> ScanningMap<K, V, N, BH> {
    pub fn new(payload: Vec<(K, V)>, bh: BH) -> Self {
        Self {
            entries: payload.try_into().unwrap_or_else(|_| unreachable!()),
            bh,
        }
    }

    pub fn get(&self, key: &K) -> Option<&V>
    where
        K: Eq,
    {
        for entry in &self.entries {
            if key.eq(&entry.0) {
                return Some(&entry.1);
            }
        }

        None
    }

    pub fn get_mut(&mut self, key: &K) -> Option<&mut V>
    where
        K: Eq,
    {
        for entry in &mut self.entries {
            if key.eq(&entry.0) {
                return Some(&mut entry.1);
            }
        }

        None
    }

    pub fn get_kv(&self, key: &K) -> Option<(&K, &V)>
    where
        K: Eq,
    {
        for entry in &self.entries {
            if key.eq(&entry.0) {
                return Some((&entry.0, &entry.1));
            }
        }

        None
    }

    pub const fn get_by_index(&self, index: usize) -> Option<(&K, &V)> {
        if index < self.len() {
            Some((&self.entries[index].0, &self.entries[index].1))
        } else {
            None
        }
    }

    pub const fn len(&self) -> usize {
        N
    }

    pub const fn hasher(&self) -> &BH {
        &self.bh
    }
}

impl<K, V, const N: usize, BH> Debug for ScanningMap<K, V, N, BH>
where
    K: Debug,
    V: Debug,
    BH: BuildHasher,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        let pairs = self.entries.iter().map(|x| (&x.0, &x.1));
        f.debug_map().entries(pairs).finish()
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;
    use std::hash::RandomState;

    use super::ScanningMap;

    #[test]
    fn new_creates_scanning_map_with_given_payload() {
        let payload = vec![(10, 20), (30, 40), (50, 60)];
        let map = ScanningMap::<i32, i32, 3, RandomState>::new(payload.clone(), RandomState::new());
        assert_eq!(payload.len(), map.len());
    }

    #[test]
    fn get_returns_some_for_existing_keys() {
        let payload = vec![(10, 20), (30, 40), (50, 60)];
        let map = ScanningMap::<i32, i32, 3, RandomState>::new(payload, RandomState::new());
        assert_eq!(&20, map.get(&10).unwrap());
        assert_eq!(&40, map.get(&30).unwrap());
        assert_eq!(&60, map.get(&50).unwrap());
    }

    #[test]
    fn get_returns_none_for_non_existing_keys() {
        let payload = vec![(10, 20), (30, 40), (50, 60)];
        let map = ScanningMap::<i32, i32, 3, RandomState>::new(payload, RandomState::new());
        assert_eq!(None, map.get(&0));
    }

    #[test]
    fn get_mut_returns_some_for_existing_keys() {
        let payload = vec![(10, 20), (30, 40), (50, 60)];
        let mut map = ScanningMap::<i32, i32, 3, RandomState>::new(payload, RandomState::new());
        assert_eq!(&20, map.get_mut(&10).unwrap());
        assert_eq!(&40, map.get_mut(&30).unwrap());
        assert_eq!(&60, map.get_mut(&50).unwrap());
    }

    #[test]
    fn get_mut_returns_none_for_non_existing_keys() {
        let payload = vec![(10, 20), (30, 40), (50, 60)];
        let mut map = ScanningMap::<i32, i32, 3, RandomState>::new(payload, RandomState::new());
        assert_eq!(None, map.get_mut(&0));
    }

    #[test]
    fn get_key_value_returns_some_for_existing_keys() {
        let payload = vec![(10, 20), (30, 40), (50, 60)];
        let map = ScanningMap::<i32, i32, 3, RandomState>::new(payload, RandomState::new());
        assert_eq!((&10, &20), map.get_kv(&10).unwrap());
        assert_eq!((&30, &40), map.get_kv(&30).unwrap());
        assert_eq!((&50, &60), map.get_kv(&50).unwrap());
    }

    #[test]
    fn get_key_value_returns_none_for_non_existing_keys() {
        let payload = vec![(10, 20), (30, 40), (50, 60)];
        let map = ScanningMap::<i32, i32, 3, RandomState>::new(payload, RandomState::new());
        assert_eq!(None, map.get_kv(&0));
    }

    #[test]
    fn get_by_index_returns_some_for_existing_indices() {
        let payload = vec![
            ("ABC".to_string(), 123),
            ("DEFG".to_string(), 456),
            ("HIJKL".to_string(), 768),
        ];
        let map = ScanningMap::<String, i32, 3, RandomState>::new(payload, RandomState::new());
        let mut hm = HashMap::<String, i32>::new();

        let kv0 = map.get_by_index(0).unwrap();
        let kv1 = map.get_by_index(1).unwrap();
        let kv2 = map.get_by_index(2).unwrap();

        hm.insert(kv0.0.to_string(), *kv0.1);
        hm.insert(kv1.0.to_string(), *kv1.1);
        hm.insert(kv2.0.to_string(), *kv2.1);

        assert_eq!(Some((&"ABC".to_string(), &123)), hm.get_key_value("ABC"));
        assert_eq!(Some((&"DEFG".to_string(), &456)), hm.get_key_value("DEFG"));
        assert_eq!(
            Some((&"HIJKL".to_string(), &768)),
            hm.get_key_value("HIJKL")
        );
    }

    #[test]
    fn get_by_index_returns_none_for_non_existing_indices() {
        let payload = vec![
            ("ABC".to_string(), 123),
            ("DEFG".to_string(), 456),
            ("HIJKL".to_string(), 768),
        ];
        let map = ScanningMap::<String, i32, 3, RandomState>::new(payload, RandomState::new());
        assert_eq!(None, map.get_by_index(3));
    }

    #[test]
    fn debug_format_is_correct() {
        let payload = vec![(10, 20)];
        let map = ScanningMap::<i32, i32, 1, RandomState>::new(payload, RandomState::new());
        assert_eq!("{10: 20}", format!("{map:?}"));
    }
}
