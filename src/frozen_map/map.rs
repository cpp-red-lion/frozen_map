use core::any::type_name;
use core::fmt::{Debug, Formatter, Result};
use core::hash::{BuildHasher, BuildHasherDefault, Hash};
use core::mem::MaybeUninit;
use core::mem::transmute;
use core::ops::Index;
use std::hash::DefaultHasher;

use num_traits::ToPrimitive;

use crate::analysis::hash_code_analyzer::analyze_hash_codes;
use crate::analysis::slice_key_analyzer::{analyze_slice_keys, SliceKeyAnalysisResult};
pub use crate::frozen_map::iterators::*;
use crate::maps::empty_map::EmptyMap;
use crate::maps::hash_map::*;
use crate::maps::integer_range_map::IntegerRangeMap;
use crate::maps::scanning_map::ScanningMap;
use crate::maps::singleton_map::SingletonMap;

/// The different implementations available for use, depending on the type and content of the payload.
enum MapTypes<K, V, BH>
where
    K: Eq + Hash,
    BH: BuildHasher,
{
    Empty(EmptyMap<K, V, BH>),

    Singleton(SingletonMap<K, V, BH>),

    Scanning2(ScanningMap<K, V, 2, BH>),
    Scanning3(ScanningMap<K, V, 3, BH>),

    CommonSmall(HashMap<K, V, u8, CommonHashHelper<BH>, BH>),
    CommonMedium(HashMap<K, V, u16, CommonHashHelper<BH>, BH>),
    CommonLarge(HashMap<K, V, usize, CommonHashHelper<BH>, BH>),

    U32Small(HashMap<u32, V, u8, IntegerHashHelper<BH>, BH>),
    U32Medium(HashMap<u32, V, u16, IntegerHashHelper<BH>, BH>),
    U32Large(HashMap<u32, V, usize, IntegerHashHelper<BH>, BH>),

    U32Range(IntegerRangeMap<u32, V, BH>),

    LeftStringSliceSmall(HashMap<String, V, u8, LeftHandSliceHashHelper<BH>, BH>),
    LeftStringSliceMedium(HashMap<String, V, u16, LeftHandSliceHashHelper<BH>, BH>),
    LeftStringSliceLarge(HashMap<String, V, usize, LeftHandSliceHashHelper<BH>, BH>),

    RightStringSliceSmall(HashMap<String, V, u8, RightHandSliceHashHelper<BH>, BH>),
    RightStringSliceMedium(HashMap<String, V, u16, RightHandSliceHashHelper<BH>, BH>),
    RightStringSliceLarge(HashMap<String, V, usize, RightHandSliceHashHelper<BH>, BH>),

    StringLengthSmall(HashMap<String, V, u8, LengthHashHelper<BH>, BH>),
}

/// A map optimized for fast read access.
///
/// A frozen map differs from the traditional [`std::collections::HashMap`] type in three key ways. First, creating
/// a mew frozen map can take a relatively long time, especially for very large maps. Second,
/// once created, the keys in frozen maps are immutable. And third, probing a frozen map is
/// typically considerably faster.
///
/// The reason creating a frozen map can take some time is due to the extensive analysis that is
/// performed on the map's keys in order to determine the best map implementation to use, and
/// the best data layout to use. This analysis is what enables frozen maps to be faster later when
/// reading from the map.
///
/// Frozen maps are intended for long-lived maps, where the cost of creating the map is made up
/// over time by the faster probing performance.
///
/// A `FrozenMap` requires that the elements
/// implement the [`Eq`] and [`Hash`] traits. This can frequently be achieved by
/// using `#[derive(PartialEq, Eq, Hash)]`. If you implement these yourself,
/// it is important that the following property holds:
///
/// ```text
/// k1 == k2 -> hash(k1) == hash(k2)
/// ```
///
/// In other words, if two keys are equal, their hashes must be equal.
/// Violating this property is a logic error.
///
/// It is also a logic error for a key to be modified in such a way that the key's
/// hash, as determined by the [`Hash`] trait, or its equality, as determined by
/// the [`Eq`] trait, changes while it is in the map. This is normally only
/// possible through [`Cell`], [`RefCell`], global state, I/O, or unsafe code.
///
/// The behavior resulting from either logic error is not specified, but will
/// be encapsulated to the `FrozenMap` that observed the logic error and not
/// result in undefined behavior. This could include panics, incorrect results,
/// aborts, memory leaks, and non-termination.
///
/// # Examples
///
/// ```
/// use frozen_collections::FrozenMap;
///
/// // Type inference lets us omit an explicit type signature (which
/// // would be `FrozenMap<String, String>` in this example).
/// let book_reviews = FrozenMap::from([
///     ("Adventures of Huckleberry Finn".to_string(), "My favorite book.".to_string()),
///     ("Grimms' Fairy Tales".to_string(), "Masterpiece.".to_string()),
///     ("Pride and Prejudice".to_string(), "Very enjoyable.".to_string()),
///     ("The Adventures of Sherlock Holmes".to_string(), "Eye lyked it alot.".to_string()),
/// ]);
///
/// // Check for a specific one.
/// if !book_reviews.contains_key(&"Les Misérables".to_string()) {
///     println!("We've got {} reviews, but Les Misérables ain't one.",
///              book_reviews.len());
/// }
///
/// // Look up the values associated with some keys.
/// let to_find = ["Pride and Prejudice", "Alice's Adventure in Wonderland"];
/// for &book in &to_find {
///     match book_reviews.get(&book.to_string()) {
///         Some(review) => println!("{book}: {review}"),
///         None => println!("{book} is unreviewed.")
///     }
/// }
///
/// // Look up the value for a key (will panic if the key is not found).
/// println!("Review for Jane: {}", book_reviews["Pride and Prejudice".to_string()]);
///
/// // Iterate over everything.
/// for (book, review) in &book_reviews {
///     println!("{book}: \"{review}\"");
/// }
/// ```
///
/// The easiest way to use `FrozenMap` with a custom key type is to derive [`Eq`] and [`Hash`].
/// We must also derive [`PartialEq`].
///
/// [`RefCell`]: std::cell::RefCell
/// [`Cell`]: std::cell::Cell
/// [`default`]: Default::default
/// [`with_hasher`]: Self::with_hasher
///
/// ```
/// use frozen_collections::FrozenMap;
///
/// #[derive(Hash, Eq, PartialEq, Debug)]
/// struct Viking {
///     name: String,
///     country: String,
/// }
///
/// impl Viking {
///     /// Creates a new Viking.
///     fn new(name: &str, country: &str) -> Viking {
///         Viking { name: name.to_string(), country: country.to_string() }
///     }
/// }
///
/// // Use a FrozenMap to store the vikings' health points.
/// let vikings = FrozenMap::from([
///     (Viking::new("Einar", "Norway"), 25),
///     (Viking::new("Olaf", "Denmark"), 24),
///     (Viking::new("Harald", "Iceland"), 12),
/// ]);
///
/// // Use derived implementation to print the status of the vikings.
/// for (viking, health) in &vikings {
///     println!("{viking:?} has {health} hp");
/// }
/// ```
#[allow(clippy::module_name_repetitions)]
pub struct FrozenMap<K, V, BH = BuildHasherDefault<DefaultHasher>>
where
    K: Eq + Hash,
    BH: BuildHasher,
{
    map_impl: MapTypes<K, V, BH>,
}

impl<K, V> FrozenMap<K, V, BuildHasherDefault<DefaultHasher>>
where
    K: Eq + Hash,
{
    /// Creates a frozen map which will use the given hash builder to hash
    /// keys.
    ///
    /// # Examples
    ///
    /// ```
    /// use frozen_collections::FrozenMap;
    /// use std::hash::RandomState;
    ///
    /// let map = FrozenMap::with_hasher([(1, 2)], RandomState::new());
    /// ```
    #[must_use]
    pub fn from_vec(payload: Vec<(K, V)>) -> Self {
        Self::from_vec_with_hasher(payload, BuildHasherDefault::default())
    }
}

impl<K, V, BH> FrozenMap<K, V, BH>
where
    K: Eq + Hash,
    BH: BuildHasher,
{
    /// Creates a frozen map which will use the given hash builder to hash
    /// keys.
    ///
    /// # Examples
    ///
    /// ```
    /// use frozen_collections::FrozenMap;
    /// use std::hash::RandomState;    ///
    ///
    /// let v = vec!((1, 2), (3, 4));
    /// let map = FrozenMap::from_vec_with_hasher(v, RandomState::new());
    /// ```
    #[must_use]
    pub fn from_vec_with_hasher(payload: Vec<(K, V)>, bh: BH) -> Self {
        Self {
            map_impl: Self::new_impl(payload, bh),
        }
    }

    /// Creates a frozen map which will use the given hash builder to hash
    /// keys.
    ///
    /// # Examples
    ///
    /// ```
    /// use frozen_collections::FrozenMap;
    /// use std::hash::RandomState;    ///
    ///
    /// let v = vec!((1, 2), (3, 4));
    /// let map = FrozenMap::from_iter_with_hasher(v, RandomState::new());
    /// ```
    #[must_use]
    pub fn from_iter_with_hasher<T: IntoIterator<Item = (K, V)>>(iter: T, bh: BH) -> Self {
        Self::from_vec_with_hasher(Vec::from_iter(iter), bh)
    }

    /// Creates a frozen map which will use the given hash builder to hash
    /// keys.
    ///
    /// # Examples
    ///
    /// ```
    /// use frozen_collections::FrozenMap;
    /// use std::hash::RandomState;    ///
    ///
    /// let map = FrozenMap::with_hasher([(0, 1), (2, 3)], RandomState::new());
    /// ```
    #[must_use]
    pub fn with_hasher<const N: usize>(payload: [(K, V); N], bh: BH) -> Self {
        Self::from_vec_with_hasher(Vec::from_iter(payload), bh)
    }

    fn new_impl(payload: Vec<(K, V)>, bh: BH) -> MapTypes<K, V, BH> {
        if payload.is_empty() {
            MapTypes::Empty(EmptyMap::new(bh))
        } else if payload.len() == 1 {
            let entry = payload.into_iter().last().unwrap();
            MapTypes::Singleton(SingletonMap::new(entry.0, entry.1, bh))
        } else if payload.len() == 2 {
            MapTypes::Scanning2(ScanningMap::new(payload, bh))
        } else if payload.len() == 3 {
            MapTypes::Scanning3(ScanningMap::new(payload, bh))
        } else if type_name::<K>() == type_name::<u32>() {
            Self::new_u32_map(payload, bh)
        } else if type_name::<K>() == type_name::<String>() {
            Self::new_string_map(payload, bh)
        } else {
            Self::new_fallback_map(payload, bh)
        }
    }

    #[allow(clippy::transmute_undefined_repr)]
    fn new_u32_map(payload: Vec<(K, V)>, bh: BH) -> MapTypes<K, V, BH> {
        let mut payload: Vec<(u32, V)> = unsafe { transmute(payload) };

        payload.sort_by_key(|x| x.0);
        let min = payload[0].0;
        let max = payload[payload.len() - 1].0;

        if (max - min) as usize == payload.len() - 1 {
            MapTypes::U32Range(IntegerRangeMap::new(
                min,
                payload.into_iter().map(|x| x.1),
                bh,
            ))
        } else {
            let codes: Vec<u64> = payload.iter().map(|x| x.0.to_u64().unwrap()).collect();
            let code_analysis = analyze_hash_codes(codes.as_slice());

            if payload.len() <= u8::MAX.to_usize().unwrap() {
                MapTypes::U32Small(new_integer_map(payload, code_analysis.num_hash_slots, bh))
            } else if payload.len() <= u16::MAX.to_usize().unwrap() {
                MapTypes::U32Medium(new_integer_map(payload, code_analysis.num_hash_slots, bh))
            } else {
                MapTypes::U32Large(new_integer_map(payload, code_analysis.num_hash_slots, bh))
            }
        }
    }

    #[allow(clippy::transmute_undefined_repr)]
    fn new_string_map(payload: Vec<(K, V)>, bh: BH) -> MapTypes<K, V, BH> {
        let payload: Vec<(String, V)> = unsafe { transmute(payload) };

        let keys: Vec<&[u8]> = payload.iter().map(|x| x.0.as_bytes()).collect();
        let key_analysis = analyze_slice_keys(keys.as_slice(), &bh);

        let codes: Vec<u64> = match key_analysis {
            SliceKeyAnalysisResult::Normal => payload.iter().map(|x| bh.hash_one(&x.0)).collect(),

            SliceKeyAnalysisResult::LeftHandSubslice {
                subslice_index,
                subslice_len,
            } => payload
                .iter()
                .map(|x| {
                    let s = &x.0.as_bytes()[subslice_index..(subslice_index + subslice_len)];
                    bh.hash_one(s)
                })
                .collect(),

            SliceKeyAnalysisResult::RightHandSubslice {
                subslice_index,
                subslice_len,
            } => payload
                .iter()
                .map(|x| {
                    let key = &x.0.as_bytes();
                    let start = key.len() - subslice_index - 1;
                    let s = &key[start..(start + subslice_len)];
                    bh.hash_one(s)
                })
                .collect(),

            SliceKeyAnalysisResult::Length => payload
                .iter()
                .map(|x| x.0.len().to_u64().unwrap())
                .collect(),
        };

        let code_analysis = analyze_hash_codes(codes.as_slice());

        if payload.len() <= u8::MAX.to_usize().unwrap() {
            match key_analysis {
                SliceKeyAnalysisResult::Normal => MapTypes::CommonSmall(new_common_map(
                    unsafe { transmute(payload) },
                    code_analysis.num_hash_slots,
                    bh,
                )),

                SliceKeyAnalysisResult::LeftHandSubslice {
                    subslice_index,
                    subslice_len,
                } => MapTypes::LeftStringSliceSmall(new_left_slice_map(
                    payload,
                    code_analysis.num_hash_slots,
                    bh,
                    subslice_index,
                    subslice_len,
                )),

                SliceKeyAnalysisResult::RightHandSubslice {
                    subslice_index,
                    subslice_len,
                } => MapTypes::RightStringSliceSmall(new_right_slice_map(
                    payload,
                    code_analysis.num_hash_slots,
                    bh,
                    subslice_index,
                    subslice_len,
                )),

                SliceKeyAnalysisResult::Length => MapTypes::StringLengthSmall(new_length_map(
                    payload,
                    code_analysis.num_hash_slots,
                    bh,
                )),
            }
        } else if payload.len() <= u16::MAX.to_usize().unwrap() {
            match key_analysis {
                SliceKeyAnalysisResult::Length | SliceKeyAnalysisResult::Normal => {
                    MapTypes::CommonMedium(new_common_map(
                        unsafe { transmute(payload) },
                        code_analysis.num_hash_slots,
                        bh,
                    ))
                }

                SliceKeyAnalysisResult::LeftHandSubslice {
                    subslice_index,
                    subslice_len,
                } => MapTypes::LeftStringSliceMedium(new_left_slice_map(
                    payload,
                    code_analysis.num_hash_slots,
                    bh,
                    subslice_index,
                    subslice_len,
                )),

                SliceKeyAnalysisResult::RightHandSubslice {
                    subslice_index,
                    subslice_len,
                } => MapTypes::RightStringSliceMedium(new_right_slice_map(
                    payload,
                    code_analysis.num_hash_slots,
                    bh,
                    subslice_index,
                    subslice_len,
                )),
            }
        } else {
            match key_analysis {
                SliceKeyAnalysisResult::Length | SliceKeyAnalysisResult::Normal => {
                    MapTypes::CommonLarge(new_common_map(
                        unsafe { transmute(payload) },
                        code_analysis.num_hash_slots,
                        bh,
                    ))
                }

                SliceKeyAnalysisResult::LeftHandSubslice {
                    subslice_index,
                    subslice_len,
                } => MapTypes::LeftStringSliceLarge(new_left_slice_map(
                    payload,
                    code_analysis.num_hash_slots,
                    bh,
                    subslice_index,
                    subslice_len,
                )),

                SliceKeyAnalysisResult::RightHandSubslice {
                    subslice_index,
                    subslice_len,
                } => MapTypes::RightStringSliceLarge(new_right_slice_map(
                    payload,
                    code_analysis.num_hash_slots,
                    bh,
                    subslice_index,
                    subslice_len,
                )),
            }
        }
    }

    fn new_fallback_map(payload: Vec<(K, V)>, bh: BH) -> MapTypes<K, V, BH> {
        let codes: Vec<u64> = payload.iter().map(|x| bh.hash_one(&x.0)).collect();

        let code_analysis = analyze_hash_codes(codes.as_slice());

        if payload.len() <= u8::MAX.to_usize().unwrap() {
            MapTypes::CommonSmall(new_common_map(payload, code_analysis.num_hash_slots, bh))
        } else if payload.len() <= u16::MAX.to_usize().unwrap() {
            MapTypes::CommonMedium(new_common_map(payload, code_analysis.num_hash_slots, bh))
        } else {
            MapTypes::CommonLarge(new_common_map(payload, code_analysis.num_hash_slots, bh))
        }
    }

    /// Returns a reference to the value corresponding to the key.
    ///
    /// # Examples
    ///
    /// ```
    /// use frozen_collections::FrozenMap;
    ///
    /// let map = FrozenMap::from([(1, "a".to_string())]);
    /// assert_eq!(map.get(&1), Some(&"a".to_string()));
    /// assert_eq!(map.get(&2), None);
    /// ```
    pub fn get(&self, key: &K) -> Option<&V> {
        match &self.map_impl {
            MapTypes::Empty(m) => m.get(key),
            MapTypes::Singleton(m) => m.get(key),
            MapTypes::Scanning2(m) => m.get(key),
            MapTypes::Scanning3(m) => m.get(key),
            MapTypes::CommonSmall(m) => m.get(key),
            MapTypes::CommonMedium(m) => m.get(key),
            MapTypes::CommonLarge(m) => m.get(key),
            MapTypes::U32Small(m) => m.get(unsafe { transmute(key) }),
            MapTypes::U32Medium(m) => m.get(unsafe { transmute(key) }),
            MapTypes::U32Large(m) => m.get(unsafe { transmute(key) }),
            MapTypes::U32Range(m) => m.get(unsafe { transmute(key) }),
            MapTypes::LeftStringSliceSmall(m) => m.get(unsafe { transmute(key) }),
            MapTypes::LeftStringSliceMedium(m) => m.get(unsafe { transmute(key) }),
            MapTypes::LeftStringSliceLarge(m) => m.get(unsafe { transmute(key) }),
            MapTypes::RightStringSliceSmall(m) => m.get(unsafe { transmute(key) }),
            MapTypes::RightStringSliceMedium(m) => m.get(unsafe { transmute(key) }),
            MapTypes::RightStringSliceLarge(m) => m.get(unsafe { transmute(key) }),
            MapTypes::StringLengthSmall(m) => m.get(unsafe { transmute(key) }),
        }
    }

    /// Returns the key-value pair corresponding to the supplied key.
    ///
    /// # Examples
    ///
    /// ```
    /// use frozen_collections::FrozenMap;
    ///
    /// let map = FrozenMap::from([(1, "a".to_string())]);
    /// assert_eq!(map.get_key_value(&1), Some((&1, &"a".to_string())));
    /// assert_eq!(map.get_key_value(&2), None);
    /// ```
    pub fn get_key_value(&self, key: &K) -> Option<(&K, &V)> {
        match &self.map_impl {
            MapTypes::Empty(m) => m.get_kv(key),
            MapTypes::Singleton(m) => m.get_kv(key),
            MapTypes::Scanning2(m) => m.get_kv(key),
            MapTypes::Scanning3(m) => m.get_kv(key),
            MapTypes::CommonSmall(m) => m.get_kv(key),
            MapTypes::CommonMedium(m) => m.get_kv(key),
            MapTypes::CommonLarge(m) => m.get_kv(key),
            MapTypes::U32Small(m) => unsafe { transmute(m.get_kv(transmute(key))) },
            MapTypes::U32Medium(m) => unsafe { transmute(m.get_kv(transmute(key))) },
            MapTypes::U32Large(m) => unsafe { transmute(m.get_kv(transmute(key))) },
            MapTypes::U32Range(m) => unsafe { transmute(m.get_key_value(transmute(key))) },
            MapTypes::LeftStringSliceSmall(m) => unsafe { transmute(m.get_kv(transmute(key))) },
            MapTypes::LeftStringSliceMedium(m) => unsafe { transmute(m.get_kv(transmute(key))) },
            MapTypes::LeftStringSliceLarge(m) => unsafe { transmute(m.get_kv(transmute(key))) },
            MapTypes::RightStringSliceSmall(m) => unsafe { transmute(m.get_kv(transmute(key))) },
            MapTypes::RightStringSliceMedium(m) => unsafe { transmute(m.get_kv(transmute(key))) },
            MapTypes::RightStringSliceLarge(m) => unsafe { transmute(m.get_kv(transmute(key))) },
            MapTypes::StringLengthSmall(m) => unsafe { transmute(m.get_kv(transmute(key))) },
        }
    }

    pub fn get_mut(&mut self, key: &K) -> Option<&mut V> {
        match &mut self.map_impl {
            MapTypes::Empty(m) => m.get_mut(key),
            MapTypes::Singleton(m) => m.get_mut(key),
            MapTypes::Scanning2(m) => m.get_mut(key),
            MapTypes::Scanning3(m) => m.get_mut(key),
            MapTypes::CommonSmall(m) => m.get_mut(key),
            MapTypes::CommonMedium(m) => m.get_mut(key),
            MapTypes::CommonLarge(m) => m.get_mut(key),
            MapTypes::U32Small(m) => m.get_mut(unsafe { transmute(key) }),
            MapTypes::U32Medium(m) => m.get_mut(unsafe { transmute(key) }),
            MapTypes::U32Large(m) => m.get_mut(unsafe { transmute(key) }),
            MapTypes::U32Range(m) => m.get_mut(unsafe { transmute(key) }),
            MapTypes::LeftStringSliceSmall(m) => m.get_mut(unsafe { transmute(key) }),
            MapTypes::LeftStringSliceMedium(m) => m.get_mut(unsafe { transmute(key) }),
            MapTypes::LeftStringSliceLarge(m) => m.get_mut(unsafe { transmute(key) }),
            MapTypes::RightStringSliceSmall(m) => m.get_mut(unsafe { transmute(key) }),
            MapTypes::RightStringSliceMedium(m) => m.get_mut(unsafe { transmute(key) }),
            MapTypes::RightStringSliceLarge(m) => m.get_mut(unsafe { transmute(key) }),
            MapTypes::StringLengthSmall(m) => m.get_mut(unsafe { transmute(key) }),
        }
    }

    /// Attempts to get mutable references to `N` values in the map at once.
    ///
    /// Returns an array of length `N` with the results of each query. For soundness, at most one
    /// mutable reference will be returned to any value. `None` will be returned if any of the
    /// keys are duplicates or missing.
    ///
    /// # Examples
    ///
    /// ```
    /// use frozen_collections::FrozenMap;
    ///
    /// let mut libraries = FrozenMap::from([
    ///     ("Bodleian Library".to_string(), 1602),
    ///     ("Athenæum".to_string(), 1807),
    ///     ("Herzogin-Anna-Amalia-Bibliothek".to_string(), 1691),
    ///     ("Library of Congress".to_string(), 1800)
    /// ]);
    ///
    /// let got = libraries.get_many_mut([
    ///     &"Athenæum".to_string(),
    ///     &"Library of Congress".to_string(),
    /// ]);
    /// assert_eq!(
    ///     got,
    ///     Some([
    ///         &mut 1807,
    ///         &mut 1800,
    ///     ]),
    /// );
    ///
    /// // Missing keys result in None
    /// let got = libraries.get_many_mut([
    ///     &"Athenæum".to_string(),
    ///     &"New York Public Library".to_string(),
    /// ]);
    /// assert_eq!(got, None);
    ///
    /// // Duplicate keys result in None
    /// let got = libraries.get_many_mut([
    ///     &"Athenæum".to_string(),
    ///     &"Athenæum".to_string(),
    /// ]);
    /// assert_eq!(got, None);
    /// ```
    #[allow(mutable_transmutes)]
    pub fn get_many_mut<const N: usize>(&mut self, keys: [&K; N]) -> Option<[&mut V; N]> {
        // ensure key uniqueness (assumes "keys" is a relatively small array)
        for i in 0..keys.len() {
            for j in 0..i {
                if keys[j].eq(keys[i]) {
                    return None;
                }
            }
        }

        unsafe {
            let mut result: MaybeUninit<[&mut V; N]> = MaybeUninit::uninit();
            let p = result.as_mut_ptr();

            for (i, key) in keys.iter().enumerate() {
                *(*p).get_unchecked_mut(i) = transmute(self.get(key)?);
            }

            Some(result.assume_init())
        }
    }

    pub(crate) fn get_by_index(&self, index: usize) -> Option<(&K, &V)> {
        match &self.map_impl {
            MapTypes::Empty(m) => m.get_by_index(index),
            MapTypes::Singleton(m) => m.get_by_index(index),
            MapTypes::Scanning2(m) => m.get_by_index(index),
            MapTypes::Scanning3(m) => m.get_by_index(index),
            MapTypes::CommonSmall(m) => m.get_by_index(index),
            MapTypes::CommonMedium(m) => m.get_by_index(index),
            MapTypes::CommonLarge(m) => m.get_by_index(index),
            MapTypes::U32Small(m) => unsafe { transmute(m.get_by_index(index)) },
            MapTypes::U32Medium(m) => unsafe { transmute(m.get_by_index(index)) },
            MapTypes::U32Large(m) => unsafe { transmute(m.get_by_index(index)) },
            MapTypes::U32Range(m) => unsafe { transmute(m.get_by_index(index)) },
            MapTypes::LeftStringSliceSmall(m) => unsafe { transmute(m.get_by_index(index)) },
            MapTypes::LeftStringSliceMedium(m) => unsafe { transmute(m.get_by_index(index)) },
            MapTypes::LeftStringSliceLarge(m) => unsafe { transmute(m.get_by_index(index)) },
            MapTypes::RightStringSliceSmall(m) => unsafe { transmute(m.get_by_index(index)) },
            MapTypes::RightStringSliceMedium(m) => unsafe { transmute(m.get_by_index(index)) },
            MapTypes::RightStringSliceLarge(m) => unsafe { transmute(m.get_by_index(index)) },
            MapTypes::StringLengthSmall(m) => unsafe { transmute(m.get_by_index(index)) },
        }
    }

    /// Returns `true` if the map contains a value for the specified key.
    ///
    /// # Examples
    ///
    /// ```
    /// use frozen_collections::FrozenMap;
    ///
    /// let map = FrozenMap::from([(1, "a".to_string())]);
    ///
    /// assert_eq!(map.contains_key(&1), true);
    /// assert_eq!(map.contains_key(&2), false);
    /// ```
    pub fn contains_key(&self, key: &K) -> bool {
        self.get(key).is_some()
    }

    /// Returns the number of elements in the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use frozen_collections::FrozenMap;
    ///
    /// let a = FrozenMap::from([(1, 2)]);
    /// assert_eq!(a.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        match &self.map_impl {
            MapTypes::Empty(m) => m.len(),
            MapTypes::Singleton(m) => m.len(),
            MapTypes::Scanning2(m) => m.len(),
            MapTypes::Scanning3(m) => m.len(),
            MapTypes::CommonSmall(m) => m.len(),
            MapTypes::CommonMedium(m) => m.len(),
            MapTypes::CommonLarge(m) => m.len(),
            MapTypes::U32Small(m) => m.len(),
            MapTypes::U32Medium(m) => m.len(),
            MapTypes::U32Large(m) => m.len(),
            MapTypes::U32Range(m) => m.len(),
            MapTypes::LeftStringSliceSmall(m) => m.len(),
            MapTypes::LeftStringSliceMedium(m) => m.len(),
            MapTypes::LeftStringSliceLarge(m) => m.len(),
            MapTypes::RightStringSliceSmall(m) => m.len(),
            MapTypes::RightStringSliceMedium(m) => m.len(),
            MapTypes::RightStringSliceLarge(m) => m.len(),
            MapTypes::StringLengthSmall(m) => m.len(),
        }
    }

    /// Returns a reference to the map's [`BuildHasher`].
    ///
    /// # Examples
    ///
    /// ```
    /// use frozen_collections::FrozenMap;
    /// use std::hash::RandomState;
    ///
    /// let map = FrozenMap::with_hasher([(0, 1), (2, 3)], RandomState::new());
    /// let hasher: &RandomState = map.hasher();
    /// ```
    pub fn hasher(&self) -> &BH {
        match &self.map_impl {
            MapTypes::Empty(m) => m.hasher(),
            MapTypes::Singleton(m) => m.hasher(),
            MapTypes::Scanning2(m) => m.hasher(),
            MapTypes::Scanning3(m) => m.hasher(),
            MapTypes::CommonSmall(m) => m.hasher(),
            MapTypes::CommonMedium(m) => m.hasher(),
            MapTypes::CommonLarge(m) => m.hasher(),
            MapTypes::U32Small(m) => m.hasher(),
            MapTypes::U32Medium(m) => m.hasher(),
            MapTypes::U32Large(m) => m.hasher(),
            MapTypes::U32Range(m) => m.hasher(),
            MapTypes::LeftStringSliceSmall(m) => m.hasher(),
            MapTypes::LeftStringSliceMedium(m) => m.hasher(),
            MapTypes::LeftStringSliceLarge(m) => m.hasher(),
            MapTypes::RightStringSliceSmall(m) => m.hasher(),
            MapTypes::RightStringSliceMedium(m) => m.hasher(),
            MapTypes::RightStringSliceLarge(m) => m.hasher(),
            MapTypes::StringLengthSmall(m) => m.hasher(),
        }
    }

    /// Returns `true` if the map contains no elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use frozen_collections::FrozenMap;
    ///
    /// let a = FrozenMap::from([(0, 1)]);
    /// assert!(!a.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// An iterator visiting all key-value pairs in arbitrary order.
    /// The iterator element type is `(&'a K, &'a V)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use frozen_collections::FrozenMap;
    ///
    /// let map = FrozenMap::from([
    ///     ("a", 1),
    ///     ("b", 2),
    ///     ("c", 3),
    /// ]);
    ///
    /// for (key, val) in map.iter() {
    ///     println!("key: {key} val: {val}");
    /// }
    /// ```
    pub const fn iter(&self) -> Iter<K, V, BH> {
        Iter::new(self)
    }

    /// An iterator visiting all keys in arbitrary order.
    /// The iterator element type is `&'a K`.
    ///
    /// # Examples
    ///
    /// ```
    /// use frozen_collections::FrozenMap;
    ///
    /// let map = FrozenMap::from([
    ///     ("a", 1),
    ///     ("b", 2),
    ///     ("c", 3),
    /// ]);
    ///
    /// for key in map.keys() {
    ///     println!("{key}");
    /// }
    /// ```
    pub const fn keys(&self) -> Keys<K, V, BH> {
        Keys::new(self)
    }

    /// An iterator visiting all values in arbitrary order.
    /// The iterator element type is `&'a V`.
    ///
    /// # Examples
    ///
    /// ```
    /// use frozen_collections::FrozenMap;
    ///
    /// let map = FrozenMap::from([
    ///     ("a", 1),
    ///     ("b", 2),
    ///     ("c", 3),
    /// ]);
    ///
    /// for val in map.values() {
    ///     println!("{val}");
    /// }
    /// ```
    pub const fn values(&self) -> Values<K, V, BH> {
        Values::new(self)
    }
}

impl<K, V, const N: usize> From<[(K, V); N]> for FrozenMap<K, V, BuildHasherDefault<DefaultHasher>>
where
    K: Eq + Hash,
{
    fn from(payload: [(K, V); N]) -> Self {
        Self::from_vec(Vec::from_iter(payload))
    }
}

impl<K, V> FromIterator<(K, V)> for FrozenMap<K, V, BuildHasherDefault<DefaultHasher>>
where
    K: Eq + Hash,
{
    fn from_iter<T: IntoIterator<Item = (K, V)>>(iter: T) -> Self {
        Self::from_vec(Vec::from_iter(iter))
    }
}

impl<K, V, BH> Index<K> for FrozenMap<K, V, BH>
where
    K: Eq + Hash,
    BH: BuildHasher,
{
    type Output = V;

    fn index(&self, index: K) -> &Self::Output {
        self.get(&index).unwrap()
    }
}

impl<K, V, BH> Default for FrozenMap<K, V, BH>
where
    K: Eq + Hash,
    BH: BuildHasher + Default,
{
    fn default() -> Self {
        Self {
            map_impl: MapTypes::Empty(EmptyMap::<K, V, BH>::new(Default::default())),
        }
    }
}

impl<K, V, BH> Debug for FrozenMap<K, V, BH>
where
    K: Eq + Hash + Debug,
    V: Debug,
    BH: BuildHasher,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match &self.map_impl {
            MapTypes::Empty(m) => m.fmt(f),
            MapTypes::Singleton(m) => m.fmt(f),
            MapTypes::Scanning2(m) => m.fmt(f),
            MapTypes::Scanning3(m) => m.fmt(f),
            MapTypes::CommonSmall(m) => m.fmt(f),
            MapTypes::CommonMedium(m) => m.fmt(f),
            MapTypes::CommonLarge(m) => m.fmt(f),
            MapTypes::U32Small(m) => m.fmt(f),
            MapTypes::U32Medium(m) => m.fmt(f),
            MapTypes::U32Large(m) => m.fmt(f),
            MapTypes::U32Range(m) => m.fmt(f),
            MapTypes::LeftStringSliceSmall(m) => m.fmt(f),
            MapTypes::LeftStringSliceMedium(m) => m.fmt(f),
            MapTypes::LeftStringSliceLarge(m) => m.fmt(f),
            MapTypes::RightStringSliceSmall(m) => m.fmt(f),
            MapTypes::RightStringSliceMedium(m) => m.fmt(f),
            MapTypes::RightStringSliceLarge(m) => m.fmt(f),
            MapTypes::StringLengthSmall(m) => m.fmt(f),
        }
    }
}

impl<K, V, BH> PartialEq<Self> for FrozenMap<K, V, BH>
where
    K: Eq + Hash,
    V: PartialEq,
    BH: BuildHasher,
{
    fn eq(&self, other: &Self) -> bool {
        if self.len() != other.len() {
            return false;
        }

        self.iter()
            .all(|(key, value)| other.get(key).map_or(false, |v| *value == *v))
    }
}

impl<K, V, BH> Eq for FrozenMap<K, V, BH>
where
    K: Eq + Hash,
    V: PartialEq,
    BH: BuildHasher,
{
}

impl<K, V, BH> Clone for FrozenMap<K, V, BH>
where
    K: Eq + Hash + Clone,
    V: Clone,
    BH: BuildHasher + Clone,
{
    fn clone(&self) -> Self {
        Self::from_iter_with_hasher(
            self.iter().map(|x| (x.0.clone(), x.1.clone())),
            self.hasher().clone(),
        )
    }
}

impl<'a, K, V, BH> IntoIterator for &'a FrozenMap<K, V, BH>
where
    K: Eq + Hash,
    BH: BuildHasher,
{
    type Item = (&'a K, &'a V);
    type IntoIter = Iter<'a, K, V, BH>;

    fn into_iter(self) -> Iter<'a, K, V, BH> {
        self.iter()
    }
}
