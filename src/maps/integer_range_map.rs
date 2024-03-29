use core::fmt::{Debug, Formatter, Result};
use core::hash::BuildHasher;

use num_traits::PrimInt;

/// A map whose keys are a continuous range of integers.
pub struct IntegerRangeMap<K, V, BH>
where
    K: PrimInt,
    BH: BuildHasher,
{
    min: K,
    max: K,
    values: Vec<V>,
    keys: Vec<K>,
    bh: BH,
}

impl<K, V, BH> IntegerRangeMap<K, V, BH>
where
    K: PrimInt,
    BH: BuildHasher,
{
    pub fn new<T: IntoIterator<Item = V>>(min: K, iter: T, bh: BH) -> Self {
        let values = Vec::from_iter(iter);
        let mut keys = Vec::with_capacity(values.len());

        let mut max = min;
        keys.push(max);
        for _ in 1..values.len() {
            max = max + K::one();
            keys.push(max);
        }

        Self {
            min,
            max,
            values,
            keys,
            bh,
        }
    }

    pub fn get(&self, key: &K) -> Option<&V> {
        if *key >= self.min && *key <= self.max {
            let index = (*key - self.min).to_usize().unwrap();
            Some(&self.values[index])
        } else {
            None
        }
    }

    pub fn get_mut(&mut self, key: &K) -> Option<&mut V> {
        if *key >= self.min && *key <= self.max {
            let index = (*key - self.min).to_usize().unwrap();
            Some(&mut self.values[index])
        } else {
            None
        }
    }

    pub fn get_key_value<'b>(&'b self, key: &'b K) -> Option<(&K, &V)> {
        if *key >= self.min && *key <= self.max {
            let index = (*key - self.min).to_usize().unwrap();
            Some((key, &self.values[index]))
        } else {
            None
        }
    }

    pub fn get_by_index(&self, index: usize) -> Option<(&K, &V)> {
        if index < self.len() {
            Some((&self.keys[index], &self.values[index]))
        } else {
            None
        }
    }

    pub fn len(&self) -> usize {
        self.values.len()
    }

    pub const fn hasher(&self) -> &BH {
        &self.bh
    }
}

impl<K, V, BH> Debug for IntegerRangeMap<K, V, BH>
where
    K: Debug + PrimInt,
    V: Debug,
    BH: BuildHasher,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        let mut v = self.min;
        let pairs = self.values.iter().map(|x| {
            v = v.add(K::one());
            (v.sub(K::one()), x)
        });
        f.debug_map().entries(pairs).finish()
    }
}

#[cfg(test)]
mod test {
    use std::collections::HashMap;
    use std::hash::RandomState;

    use super::IntegerRangeMap;

    #[test]
    fn range_map_test() {
        const MIN: [i32; 5] = [-11, -10, -9, 0, 1];

        for min in MIN {
            let mut m = IntegerRangeMap::<i32, i32, RandomState>::new(
                min,
                [0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
                RandomState::new(),
            );

            assert_eq!(10, m.len());
            for i in 0..9 {
                let index = min + i;
                assert_eq!(i, *m.get(&index).unwrap());
                assert_eq!(i, *m.get_mut(&index).unwrap());

                let (k, v) = m.get_key_value(&index).unwrap();
                assert_eq!((index, i), (*k, *v));
            }

            let below = min - 1;
            assert_eq!(None, m.get(&below));
            assert_eq!(None, m.get_mut(&below));
            assert_eq!(None, m.get_key_value(&below));

            let above = min + 10;
            assert_eq!(None, m.get(&above));
            assert_eq!(None, m.get_mut(&above));
            assert_eq!(None, m.get_key_value(&above));

            if min == -11 {
                assert_eq!(
                    "{-11: 0, -10: 1, -9: 2, -8: 3, -7: 4, -6: 5, -5: 6, -4: 7, -3: 8, -2: 9}",
                    format!("{m:?}")
                );
            }
        }
    }

    #[test]
    fn get_by_index_returns_some_for_existing_indices() {
        let payload = vec![123, 456, 768];
        let map = IntegerRangeMap::<i32, u16, RandomState>::new(10, payload, RandomState::new());
        let mut hm = HashMap::<i32, u16>::new();

        let kv0 = map.get_by_index(0).unwrap();
        let kv1 = map.get_by_index(1).unwrap();
        let kv2 = map.get_by_index(2).unwrap();

        hm.insert(*kv0.0, *kv0.1);
        hm.insert(*kv1.0, *kv1.1);
        hm.insert(*kv2.0, *kv2.1);

        assert_eq!(Some((&10, &123)), hm.get_key_value(&10));
        assert_eq!(Some((&11, &456)), hm.get_key_value(&11));
        assert_eq!(Some((&12, &768)), hm.get_key_value(&12));
    }

    #[test]
    fn get_by_index_returns_none_for_non_existing_indices() {
        let payload = vec![123, 456, 768];
        let map = IntegerRangeMap::<i32, u16, RandomState>::new(10, payload, RandomState::new());
        assert_eq!(None, map.get_by_index(3));
    }
}
