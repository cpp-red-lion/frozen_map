use core::fmt::{Debug, Formatter, Result};
use core::hash::{BuildHasher, Hash};
use core::marker::PhantomData;

use bitvec::macros::internal::funty::Fundamental;
use len_trait::Len;
use num_traits::{PrimInt, ToPrimitive};

pub trait HashHelper<K, BH: BuildHasher> {
    fn hash(&self, key: &K) -> u64;
    fn hasher(&self) -> &BH;
}

pub struct HashMap<K, V, S, HH, BH>
where
    S: PrimInt,
    HH: HashHelper<K, BH>,
    BH: BuildHasher,
{
    helper: HH,
    slots: Box<[HashTableSlot<S>]>,
    entries: Box<[(K, V)]>,
    _0: PhantomData<BH>,
}

struct HashTableSlot<S: PrimInt> {
    entry_index: S,
    num_entries: S,
}

struct PrepItem<K, V> {
    slot_index: usize,
    entry: (K, V),
}

pub fn new_common_map<K, V, S, BH>(
    payload: Vec<(K, V)>,
    num_hash_slots: usize,
    bh: BH,
) -> HashMap<K, V, S, CommonHashHelper<BH>, BH>
where
    K: Eq + Hash,
    S: PrimInt,
    BH: BuildHasher,
{
    HashMap::new(payload, num_hash_slots, CommonHashHelper { bh })
}

pub fn new_left_slice_map<K, V, S, BH>(
    payload: Vec<(K, V)>,
    num_hash_slots: usize,
    bh: BH,
    slice_index: usize,
    slice_len: usize,
) -> HashMap<K, V, S, LeftHandSliceHashHelper<BH>, BH>
where
    K: Eq + SliceHash + Len,
    S: PrimInt,
    BH: BuildHasher,
{
    HashMap::new(
        payload,
        num_hash_slots,
        LeftHandSliceHashHelper {
            slice_index,
            slice_len,
            bh,
        },
    )
}

pub fn new_right_slice_map<K, V, S, BH>(
    payload: Vec<(K, V)>,
    num_hash_slots: usize,
    bh: BH,
    slice_index: usize,
    slice_len: usize,
) -> HashMap<K, V, S, RightHandSliceHashHelper<BH>, BH>
where
    K: Eq + SliceHash + Len,
    S: PrimInt,
    BH: BuildHasher,
{
    HashMap::new(
        payload,
        num_hash_slots,
        RightHandSliceHashHelper {
            slice_index,
            slice_len,
            bh,
        },
    )
}

pub fn new_length_map<K, V, S, BH>(
    payload: Vec<(K, V)>,
    num_hash_slots: usize,
    bh: BH,
) -> HashMap<K, V, S, LengthHashHelper<BH>, BH>
where
    K: Eq + Len,
    S: PrimInt,
    BH: BuildHasher,
{
    HashMap::new(payload, num_hash_slots, LengthHashHelper { bh })
}

pub fn new_integer_map<K, V, S, BH>(
    payload: Vec<(K, V)>,
    num_hash_slots: usize,
    bh: BH,
) -> HashMap<K, V, S, IntegerHashHelper<BH>, BH>
where
    K: Eq + PrimInt,
    S: PrimInt,
    BH: BuildHasher,
{
    HashMap::new(payload, num_hash_slots, IntegerHashHelper { bh })
}

impl<K, V, S, HH, BH> HashMap<K, V, S, HH, BH>
where
    S: PrimInt,
    HH: HashHelper<K, BH>,
    BH: BuildHasher,
{
    fn new(payload: Vec<(K, V)>, num_hash_slots: usize, hash_helper: HH) -> Self {
        let mut entries = Vec::with_capacity(payload.len());

        let mut hash_table = Vec::with_capacity(num_hash_slots);
        hash_table.resize_with(num_hash_slots, || HashTableSlot {
            entry_index: S::zero(),
            num_entries: S::zero(),
        });

        let mut prep_items = Vec::new();
        for entry in payload {
            let hash_code = hash_helper.hash(&entry.0);
            let hash_slot_index = (hash_code % num_hash_slots.to_u64().unwrap())
                .to_usize()
                .unwrap();

            prep_items.push(PrepItem {
                slot_index: hash_slot_index,
                entry,
            });
        }

        // sort items so hash collisions are contiguous
        prep_items.sort_unstable_by(|x, y| x.slot_index.cmp(&y.slot_index));

        let mut entry_index = 0;
        while let Some(mut item) = prep_items.pop() {
            let hash_slot_index = item.slot_index;
            let mut num_entries = 0;

            loop {
                entries.push(item.entry);
                num_entries += 1;

                if prep_items.is_empty() || prep_items.last().unwrap().slot_index != hash_slot_index
                {
                    break;
                }

                item = prep_items.pop().unwrap();
            }

            hash_table[hash_slot_index] = HashTableSlot {
                entry_index: S::from(entry_index).unwrap(),
                num_entries: S::from(num_entries).unwrap(),
            };

            entry_index += num_entries;
        }

        Self {
            helper: hash_helper,
            slots: hash_table.into_boxed_slice(),
            entries: entries.into_boxed_slice(),
            _0: PhantomData,
        }
    }

    #[inline]
    fn get_hash_info(&self, key: &K) -> (usize, usize) {
        let hash_code = self.helper.hash(key);
        let hash_slot_index = (hash_code % self.slots.len().to_u64().unwrap())
            .to_usize()
            .unwrap();
        let hash_slot = &self.slots[hash_slot_index];

        (
            hash_slot.entry_index.to_usize().unwrap(),
            hash_slot.num_entries.to_usize().unwrap(),
        )
    }

    pub fn get(&self, key: &K) -> Option<&V>
    where
        K: Eq,
    {
        let (entry_index, num_entries) = self.get_hash_info(key);
        for index in entry_index..(entry_index + num_entries) {
            if key.eq(&self.entries[index].0) {
                return Some(&self.entries[index].1);
            }
        }

        None
    }

    pub fn get_kv(&self, key: &K) -> Option<(&K, &V)>
    where
        K: Eq,
    {
        let (entry_index, num_entries) = self.get_hash_info(key);
        for index in entry_index..(entry_index + num_entries) {
            if key.eq(&self.entries[index].0) {
                return Some((&self.entries[index].0, &self.entries[index].1));
            }
        }

        None
    }

    pub fn get_mut(&mut self, key: &K) -> Option<&mut V>
    where
        K: Eq,
    {
        let (entry_index, num_entries) = self.get_hash_info(key);
        for index in entry_index..(entry_index + num_entries) {
            if key.eq(&self.entries[index].0) {
                return Some(&mut self.entries[index].1);
            }
        }

        None
    }

    pub fn get_by_index(&self, index: usize) -> Option<(&K, &V)> {
        if index < self.len() {
            Some((&self.entries[index].0, &self.entries[index].1))
        } else {
            None
        }
    }

    pub fn len(&self) -> usize {
        self.entries.len()
    }

    pub fn hasher(&self) -> &BH {
        self.helper.hasher()
    }
}

impl<K, V, S, HH, BH> Debug for HashMap<K, V, S, HH, BH>
where
    K: Debug,
    V: Debug,
    S: PrimInt,
    HH: HashHelper<K, BH>,
    BH: BuildHasher,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        let pairs = self.entries.iter().map(|x| (&x.0, &x.1));
        f.debug_map().entries(pairs).finish()
    }
}

pub struct CommonHashHelper<BH: BuildHasher> {
    bh: BH,
}

impl<K, BH> HashHelper<K, BH> for CommonHashHelper<BH>
where
    K: Hash,
    BH: BuildHasher,
{
    #[inline]
    fn hash(&self, key: &K) -> u64 {
        self.bh.hash_one(key)
    }

    fn hasher(&self) -> &BH {
        &self.bh
    }
}

pub struct IntegerHashHelper<BH: BuildHasher> {
    bh: BH,
}

impl<K, BH> HashHelper<K, BH> for IntegerHashHelper<BH>
where
    K: PrimInt,
    BH: BuildHasher,
{
    #[inline]
    fn hash(&self, key: &K) -> u64 {
        if K::lt(key, &K::zero()) {
            return key.to_i64().unwrap().as_u64();
        }

        key.to_u64().unwrap()
    }

    fn hasher(&self) -> &BH {
        &self.bh
    }
}

pub struct LengthHashHelper<BH: BuildHasher> {
    bh: BH,
}

impl<K, BH> HashHelper<K, BH> for LengthHashHelper<BH>
where
    K: Eq + Len,
    BH: BuildHasher,
{
    #[inline]
    fn hash(&self, key: &K) -> u64 {
        key.len().to_u64().unwrap()
    }

    fn hasher(&self) -> &BH {
        &self.bh
    }
}

pub struct LeftHandSliceHashHelper<BH: BuildHasher> {
    slice_index: usize,
    slice_len: usize,
    bh: BH,
}

impl<K, BH> HashHelper<K, BH> for LeftHandSliceHashHelper<BH>
where
    K: Eq + SliceHash + Len,
    BH: BuildHasher,
{
    #[inline]
    fn hash(&self, key: &K) -> u64 {
        if key.len() >= self.slice_len {
            key.hash(
                &self.bh,
                self.slice_index,
                self.slice_index + self.slice_len,
            )
        } else {
            0
        }
    }

    fn hasher(&self) -> &BH {
        &self.bh
    }
}

pub struct RightHandSliceHashHelper<BH: BuildHasher> {
    slice_index: usize,
    slice_len: usize,
    bh: BH,
}

impl<K, BH> HashHelper<K, BH> for RightHandSliceHashHelper<BH>
where
    K: SliceHash + Len + Eq,
    BH: BuildHasher,
{
    #[inline]
    fn hash(&self, key: &K) -> u64 {
        if key.len() >= self.slice_len {
            let start = key.len() - self.slice_index - 1;

            key.hash(&self.bh, start, start + self.slice_len - 1)
        } else {
            0
        }
    }

    fn hasher(&self) -> &BH {
        &self.bh
    }
}

pub trait SliceHash {
    fn hash<BH: BuildHasher>(&self, bh: &BH, slice_min: usize, slice_max: usize) -> u64;
}

impl SliceHash for String {
    fn hash<BH: BuildHasher>(&self, bh: &BH, slice_min: usize, slice_max: usize) -> u64 {
        bh.hash_one(&self.as_bytes()[slice_min..slice_max])
    }
}

#[cfg(test)]
mod left_slice_map_tests {
    use std::hash::RandomState;

    use super::*;

    #[test]
    pub fn string_left_slice_map_test() {
        let payload = vec![
            ("ABC".to_string(), 123),
            ("DEF".to_string(), 456),
            ("GHI".to_string(), 768),
        ];
        let mut m = new_left_slice_map::<String, i32, u8, RandomState>(
            payload,
            20,
            RandomState::new(),
            0,
            2,
        );

        assert_eq!(3, m.len());
        assert!(m.get_mut(&"ABC".to_string()).is_some());
        assert!(m.get_mut(&"DEF".to_string()).is_some());
        assert!(m.get_mut(&"GHI".to_string()).is_some());
        assert!(m.get_mut(&"XYZ".to_string()).is_none());
    }

    #[test]
    fn new_creates_slice_map_with_given_payload() {
        let payload = vec![
            ("ABC".to_string(), 123),
            ("DEF".to_string(), 456),
            ("GHI".to_string(), 768),
        ];
        let map = new_left_slice_map::<String, i32, u8, RandomState>(
            payload.clone(),
            20,
            RandomState::new(),
            0,
            2,
        );
        assert_eq!(payload.len(), map.len());
    }

    #[test]
    fn get_returns_some_for_existing_keys() {
        let payload = vec![
            ("ABC".to_string(), 123),
            ("DEF".to_string(), 456),
            ("GHI".to_string(), 768),
        ];
        let map = new_left_slice_map::<String, i32, u8, RandomState>(
            payload,
            20,
            RandomState::new(),
            0,
            2,
        );
        assert_eq!(&123, map.get(&"ABC".to_string()).unwrap());
        assert_eq!(&456, map.get(&"DEF".to_string()).unwrap());
        assert_eq!(&768, map.get(&"GHI".to_string()).unwrap());
    }

    #[test]
    fn get_returns_none_for_non_existing_keys() {
        let payload = vec![
            ("ABC".to_string(), 123),
            ("DEF".to_string(), 456),
            ("GHI".to_string(), 768),
        ];
        let map = new_left_slice_map::<String, i32, u8, RandomState>(
            payload,
            20,
            RandomState::new(),
            0,
            2,
        );
        assert_eq!(None, map.get(&"XYZ".to_string()));
    }

    #[test]
    fn get_mut_returns_some_for_existing_keys() {
        let payload = vec![
            ("ABC".to_string(), 123),
            ("DEF".to_string(), 456),
            ("GHI".to_string(), 768),
        ];
        let mut map = new_left_slice_map::<String, i32, u8, RandomState>(
            payload,
            20,
            RandomState::new(),
            0,
            2,
        );
        assert_eq!(&123, map.get_mut(&"ABC".to_string()).unwrap());
        assert_eq!(&456, map.get_mut(&"DEF".to_string()).unwrap());
        assert_eq!(&768, map.get_mut(&"GHI".to_string()).unwrap());
    }

    #[test]
    fn get_mut_returns_none_for_non_existing_keys() {
        let payload = vec![
            ("ABC".to_string(), 123),
            ("DEF".to_string(), 456),
            ("GHI".to_string(), 768),
        ];
        let mut map = new_left_slice_map::<String, i32, u8, RandomState>(
            payload,
            20,
            RandomState::new(),
            0,
            2,
        );
        assert_eq!(None, map.get_mut(&"XYZ".to_string()));
    }

    #[test]
    fn get_key_value_returns_some_for_existing_keys() {
        let payload = vec![
            ("ABC".to_string(), 123),
            ("DEF".to_string(), 456),
            ("GHI".to_string(), 768),
        ];
        let map = new_left_slice_map::<String, i32, u8, RandomState>(
            payload,
            20,
            RandomState::new(),
            0,
            2,
        );
        assert_eq!(
            Some((&"ABC".to_string(), &123)),
            map.get_kv(&"ABC".to_string())
        );
        assert_eq!(
            Some((&"DEF".to_string(), &456)),
            map.get_kv(&"DEF".to_string())
        );
        assert_eq!(
            Some((&"GHI".to_string(), &768)),
            map.get_kv(&"GHI".to_string())
        );
    }

    #[test]
    fn get_key_value_returns_none_for_non_existing_keys() {
        let payload = vec![
            ("ABC".to_string(), 123),
            ("DEF".to_string(), 456),
            ("GHI".to_string(), 768),
        ];
        let map = new_left_slice_map::<String, i32, u8, RandomState>(
            payload,
            20,
            RandomState::new(),
            0,
            2,
        );
        assert_eq!(None, map.get_kv(&"XYZ".to_string()));
    }

    #[test]
    fn debug_format_is_correct() {
        let payload = vec![("10".to_string(), 20)];
        let map = new_left_slice_map::<String, i32, u8, RandomState>(
            payload,
            20,
            RandomState::new(),
            0,
            1,
        );
        assert_eq!("{\"10\": 20}", format!("{map:?}"));
    }
}

#[cfg(test)]
mod right_slice_map_tests {
    use std::hash::RandomState;

    use super::*;

    #[test]
    pub fn string_right_slice_map_test() {
        let payload = vec![
            ("ABC".to_string(), 123),
            ("DEF".to_string(), 456),
            ("GHI".to_string(), 768),
        ];
        let mut m = new_right_slice_map::<String, i32, u8, RandomState>(
            payload,
            20,
            RandomState::new(),
            2,
            3,
        );

        assert_eq!(3, m.len());
        assert!(m.get_mut(&"ABC".to_string()).is_some());
        assert!(m.get_mut(&"DEF".to_string()).is_some());
        assert!(m.get_mut(&"GHI".to_string()).is_some());
        assert!(m.get_mut(&"XYZ".to_string()).is_none());
        assert!(m.get_mut(&"XZ".to_string()).is_none());
        assert!(m.get_mut(&"XYZA".to_string()).is_none());

        assert!(m.get(&"ABC".to_string()).is_some());
        assert!(m.get(&"DEF".to_string()).is_some());
        assert!(m.get(&"GHI".to_string()).is_some());
        assert!(m.get(&"XYZ".to_string()).is_none());
        assert!(m.get(&"XZ".to_string()).is_none());
        assert!(m.get(&"XYZA".to_string()).is_none());
    }

    #[test]
    fn new_creates_slice_map_with_given_payload() {
        let payload = vec![
            ("ABC".to_string(), 123),
            ("DEF".to_string(), 456),
            ("GHI".to_string(), 768),
        ];
        let map = new_right_slice_map::<String, i32, u8, RandomState>(
            payload.clone(),
            20,
            RandomState::new(),
            2,
            3,
        );
        assert_eq!(payload.len(), map.len());
    }

    #[test]
    fn get_returns_some_for_existing_keys() {
        let payload = vec![
            ("ABC".to_string(), 123),
            ("DEF".to_string(), 456),
            ("GHI".to_string(), 768),
        ];
        let map = new_right_slice_map::<String, i32, u8, RandomState>(
            payload,
            20,
            RandomState::new(),
            2,
            3,
        );
        assert_eq!(&123, map.get(&"ABC".to_string()).unwrap());
        assert_eq!(&456, map.get(&"DEF".to_string()).unwrap());
        assert_eq!(&768, map.get(&"GHI".to_string()).unwrap());
    }

    #[test]
    fn get_returns_none_for_non_existing_keys() {
        let payload = vec![
            ("ABC".to_string(), 123),
            ("DEF".to_string(), 456),
            ("GHI".to_string(), 768),
        ];
        let map = new_right_slice_map::<String, i32, u8, RandomState>(
            payload,
            20,
            RandomState::new(),
            2,
            3,
        );
        assert_eq!(None, map.get(&"XYZ".to_string()));
        assert_eq!(None, map.get(&"YZ".to_string()));
        assert_eq!(None, map.get(&"XYZA".to_string()));
    }

    #[test]
    fn get_mut_returns_some_for_existing_keys() {
        let payload = vec![
            ("ABC".to_string(), 123),
            ("DEF".to_string(), 456),
            ("GHI".to_string(), 768),
        ];
        let mut map = new_right_slice_map::<String, i32, u8, RandomState>(
            payload,
            20,
            RandomState::new(),
            2,
            3,
        );

        assert_eq!(&123, map.get_mut(&"ABC".to_string()).unwrap());
        assert_eq!(&456, map.get_mut(&"DEF".to_string()).unwrap());
        assert_eq!(&768, map.get_mut(&"GHI".to_string()).unwrap());
    }

    #[test]
    fn get_mut_returns_none_for_non_existing_keys() {
        let payload = vec![
            ("ABC".to_string(), 123),
            ("DEF".to_string(), 456),
            ("GHI".to_string(), 768),
        ];
        let mut map = new_right_slice_map::<String, i32, u8, RandomState>(
            payload,
            20,
            RandomState::new(),
            2,
            3,
        );
        assert_eq!(None, map.get_mut(&"XYZ".to_string()));
        assert_eq!(None, map.get_mut(&"YZ".to_string()));
        assert_eq!(None, map.get_mut(&"XYZA".to_string()));
    }

    #[test]
    fn get_key_value_returns_some_for_existing_keys() {
        let payload = vec![
            ("ABC".to_string(), 123),
            ("DEF".to_string(), 456),
            ("GHI".to_string(), 768),
        ];
        let map = new_right_slice_map::<String, i32, u8, RandomState>(
            payload,
            20,
            RandomState::new(),
            2,
            3,
        );
        assert_eq!(
            Some((&"ABC".to_string(), &123)),
            map.get_kv(&"ABC".to_string())
        );
        assert_eq!(
            Some((&"DEF".to_string(), &456)),
            map.get_kv(&"DEF".to_string())
        );
        assert_eq!(
            Some((&"GHI".to_string(), &768)),
            map.get_kv(&"GHI".to_string())
        );
    }

    #[test]
    fn get_key_value_returns_none_for_non_existing_keys() {
        let payload = vec![
            ("ABC".to_string(), 123),
            ("DEF".to_string(), 456),
            ("GHI".to_string(), 768),
        ];
        let map = new_right_slice_map::<String, i32, u8, RandomState>(
            payload,
            20,
            RandomState::new(),
            2,
            3,
        );
        assert_eq!(None, map.get_kv(&"XYZ".to_string()));
        assert_eq!(None, map.get_kv(&"YZ".to_string()));
        assert_eq!(None, map.get_kv(&"XYZA".to_string()));
    }

    #[test]
    fn debug_format_is_correct() {
        let payload = vec![("10".to_string(), 20)];
        let map = new_right_slice_map::<String, i32, u8, RandomState>(
            payload,
            20,
            RandomState::new(),
            0,
            1,
        );
        assert_eq!("{\"10\": 20}", format!("{map:?}"));
    }
}

#[cfg(test)]
mod integer_map_tests {
    use core::fmt::Debug;
    use std::collections::HashMap;
    use std::hash::{Hash, RandomState};

    use num_traits::PrimInt;

    use super::*;

    #[test]
    pub fn integer_map_test() {
        tests::<i32>(&[-11, -10, -9, 0, 1]);
        tests::<i8>(&[-11, -10, -9, 0, 1, 117]);
        tests::<u32>(&[1, 245, 246]);
        tests::<u8>(&[1, 245, 245]);
    }

    fn tests<T>(base: &[i32])
    where
        T: PrimInt + Debug + Hash,
    {
        for min in base {
            let mut payload = Vec::<(T, T)>::new();

            let max = *min + 10;
            for (i, key) in (*min..max).enumerate() {
                payload.push((T::from(key).unwrap(), T::from(i).unwrap()));
            }

            let mut m = new_integer_map::<T, T, u8, RandomState>(payload, 10, RandomState::new());

            assert_eq!(10, m.len());
            for i in 0..9 {
                let index = &T::from(min + i).unwrap();
                assert_eq!(i, m.get_mut(index).unwrap().to_i32().unwrap());

                let (k, v) = m.get_kv(index).unwrap();
                assert_eq!((index, T::from(i).unwrap()), (k, *v));
            }

            let below = &T::from(min - 1).unwrap();
            assert_eq!(None, m.get_mut(below));
            assert_eq!(None, m.get_kv(below));

            let above = &T::from(min + 10).unwrap();
            assert_eq!(None, m.get_mut(above));
            assert_eq!(None, m.get_kv(above));

            let s = format!("{m:?}").to_string();
            assert!(s.starts_with('{') && s.ends_with('}'));

            let mut result = HashMap::<T, T>::new();

            let sub = &s[1..(s.len() - 1)];
            for pair in sub.split(',') {
                let numbers: Vec<&str> = pair.trim().split(": ").collect();
                let key = numbers[0].parse::<i32>().unwrap();
                let value = numbers[1].parse::<i32>().unwrap();

                result.insert(T::from(key).unwrap(), T::from(value).unwrap());
            }

            assert_eq!(m.len(), result.len());
            for kv in &result {
                assert_eq!(m.get(kv.0), result.get(kv.0));
            }
        }
    }

    #[test]
    fn get_by_index_returns_some_for_existing_indices() {
        let payload = vec![(10, 123), (11, 456), (12, 768)];
        let map = new_integer_map::<i32, i32, u16, RandomState>(payload, 20, RandomState::new());
        let mut hm = HashMap::<i32, i32, RandomState>::new();

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
        let payload = vec![(10, 123), (11, 456), (12, 768)];
        let map = new_integer_map::<i32, i32, u16, RandomState>(payload, 20, RandomState::new());
        assert_eq!(None, map.get_by_index(3));
    }
}

#[cfg(test)]
mod length_map_tests {
    use std::collections::HashMap;
    use std::hash::RandomState;

    use super::*;

    #[test]
    fn new_creates_length_map_with_given_payload() {
        let payload = vec![
            ("ABC".to_string(), 123),
            ("DEFG".to_string(), 456),
            ("HIJKL".to_string(), 768),
        ];
        let map =
            new_length_map::<String, i32, u8, RandomState>(payload.clone(), 20, RandomState::new());
        assert_eq!(payload.len(), map.len());
    }

    #[test]
    fn get_returns_some_for_existing_keys() {
        let payload = vec![
            ("ABC".to_string(), 123),
            ("DEFG".to_string(), 456),
            ("HIJKL".to_string(), 768),
        ];
        let map = new_length_map::<String, i32, u8, RandomState>(payload, 20, RandomState::new());
        assert_eq!(&123, map.get(&"ABC".to_string()).unwrap());
        assert_eq!(&456, map.get(&"DEFG".to_string()).unwrap());
        assert_eq!(&768, map.get(&"HIJKL".to_string()).unwrap());
    }

    #[test]
    fn get_returns_none_for_non_existing_keys() {
        let payload = vec![
            ("ABC".to_string(), 123),
            ("DEFG".to_string(), 456),
            ("HIJKL".to_string(), 768),
        ];
        let map = new_length_map::<String, i32, u8, RandomState>(payload, 20, RandomState::new());
        assert!(map.get(&"XYZ".to_string()).is_none());
    }

    #[test]
    fn get_mut_returns_some_for_existing_keys() {
        let payload = vec![
            ("ABC".to_string(), 123),
            ("DEFG".to_string(), 456),
            ("HIJKL".to_string(), 768),
        ];
        let mut map =
            new_length_map::<String, i32, u8, RandomState>(payload, 20, RandomState::new());
        assert_eq!(&123, map.get_mut(&"ABC".to_string()).unwrap());
        assert_eq!(&456, map.get_mut(&"DEFG".to_string()).unwrap());
        assert_eq!(&768, map.get_mut(&"HIJKL".to_string()).unwrap());
    }

    #[test]
    fn get_mut_returns_none_for_non_existing_keys() {
        let payload = vec![
            ("ABC".to_string(), 123),
            ("DEFG".to_string(), 456),
            ("HIJKL".to_string(), 768),
        ];
        let mut map =
            new_length_map::<String, i32, u8, RandomState>(payload, 20, RandomState::new());
        assert!(map.get_mut(&"XYZ".to_string()).is_none());
    }

    #[test]
    fn get_key_value_returns_some_for_existing_keys() {
        let payload = vec![
            ("ABC".to_string(), 123),
            ("DEFG".to_string(), 456),
            ("HIJKL".to_string(), 768),
        ];
        let map = new_length_map::<String, i32, u8, RandomState>(payload, 20, RandomState::new());
        assert_eq!(
            Some((&"ABC".to_string(), &123)),
            map.get_kv(&"ABC".to_string())
        );
        assert_eq!(
            Some((&"DEFG".to_string(), &456)),
            map.get_kv(&"DEFG".to_string())
        );
        assert_eq!(
            Some((&"HIJKL".to_string(), &768)),
            map.get_kv(&"HIJKL".to_string())
        );
    }

    #[test]
    fn get_key_value_returns_none_for_non_existing_keys() {
        let payload = vec![
            ("ABC".to_string(), 123),
            ("DEFG".to_string(), 456),
            ("HIJKL".to_string(), 768),
        ];
        let map = new_length_map::<String, i32, u8, RandomState>(payload, 20, RandomState::new());
        assert_eq!(None, map.get_kv(&"XYZ".to_string()));
    }

    #[test]
    fn get_by_index_returns_some_for_existing_indices() {
        let payload = vec![
            ("ABC".to_string(), 123),
            ("DEFG".to_string(), 456),
            ("HIJKL".to_string(), 768),
        ];
        let map = new_length_map::<String, i32, u8, RandomState>(payload, 20, RandomState::new());
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
        let map = new_length_map::<String, i32, u8, RandomState>(payload, 20, RandomState::new());
        assert_eq!(None, map.get_by_index(3));
    }

    #[test]
    fn debug_format_is_correct() {
        let payload = vec![("10".to_string(), 20)];
        let map = new_length_map::<String, i32, u8, RandomState>(payload, 20, RandomState::new());
        assert_eq!("{\"10\": 20}", format!("{map:?}"));
    }
}

#[cfg(test)]
mod common_map_tests {
    use std::hash::RandomState;

    use super::*;

    #[test]
    pub fn common_map_test() {
        let mut map = new_common_map::<i32, i32, usize, RandomState>(
            vec![(10, 20), (30, 40), (50, 60)],
            20,
            RandomState::new(),
        );

        assert_eq!(3, map.len());
        assert_eq!(None, map.get_mut(&0));
        assert_eq!(None, map.get_kv(&0));

        assert_eq!(&20, map.get_mut(&10).unwrap());
        assert_eq!((&10, &20), map.get_kv(&10).unwrap());

        let map =
            new_common_map::<i32, i32, usize, RandomState>(vec![(10, 20)], 20, RandomState::new());
        assert_eq!("{10: 20}", format!("{map:?}"));
    }
}
