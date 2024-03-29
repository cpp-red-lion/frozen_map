use core::fmt::{Debug, Formatter, Result};
use core::hash::{BuildHasher, BuildHasherDefault, Hash};
use core::ops::{BitAnd, BitOr, BitXor, Sub};
use std::collections::HashSet;
use std::hash::DefaultHasher;

pub use crate::frozen_set::iterators::*;
use crate::FrozenMap;

/// A set optimized for fast read access.
///
/// A frozen set differs from the traditional [`HashSet`] type in three key ways. First, creating
/// a mew frozen set can take a relatively long time, especially for very large sets. Second,
/// once created, instances of frozen sets are immutable. And third, probing a frozen set is
/// typically considerably faster.
///
/// The reason creating a frozen set can take some time is due to the extensive analysis that is
/// performed on the set's values in order to determine the best set implementation to use, and
/// the best data layout to use. This analysis is what enables frozen sets to be faster later when
/// probing the set.
///
/// Frozen sets are intended for long-lived sets, where the cost of creating the set is made up
/// over time by the faster probing performance.
///
/// A `FrozenSet` requires that the elements
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
/// the [`Eq`] trait, changes while it is in the set. This is normally only
/// possible through [`Cell`], [`RefCell`], global state, I/O, or unsafe code.
///
/// The behavior resulting from either logic error is not specified, but will
/// be encapsulated to the `FrozenSet` that observed the logic error and not
/// result in undefined behavior. This could include panics, incorrect results,
/// aborts, memory leaks, and non-termination.
///
/// # Examples
///
/// ```
/// use std::hash::RandomState;
/// use frozen_collections::FrozenSet;
///
/// let books = FrozenSet::from_vec(vec!(
///     "A Dance With Dragons".to_string(),
///     "To Kill a Mockingbird".to_string(),
///     "The Odyssey".to_string(),
///     "The Great Gatsby".to_string()));
///
/// // Check for a specific one.
/// if !books.contains(&"The Winds of Winter".to_string()) {
///     println!("We have {} books, but The Winds of Winter ain't one.",
///              books.len());
/// }
///
/// // Iterate over everything.
/// for book in &books {
///     println!("{book}");
/// }
/// ```
///
/// The easiest way to use `FrozenSet` with a custom type is to derive
/// [`Eq`] and [`Hash`]. We must also derive [`PartialEq`],
/// which is required if [`Eq`] is derived.
///
/// ```
/// use frozen_collections::FrozenSet;
///
/// #[derive(Hash, Eq, PartialEq, Debug)]
/// struct Viking {
///     name: String,
///     power: usize,
/// }
///
/// let vikings = FrozenSet::from([
///     Viking {name: "Einar".to_string(), power: 9 },
///     Viking { name: "Olaf".to_string(), power: 4 },
///     Viking { name: "Harald".to_string(), power: 8 }]);
///
/// // Use derived implementation to print the vikings.
/// for x in &vikings {
///     println!("{x:?}");
/// }
/// ```
///
/// [`HashSet`]: HashSet
/// [`HashMap`]: std::collections::HashMap
/// [`RefCell`]: std::cell::RefCell
/// [`Cell`]: std::cell::Cell
#[allow(clippy::module_name_repetitions)]
pub struct FrozenSet<T, BH = BuildHasherDefault<DefaultHasher>>
where
    T: Eq + Hash,
    BH: BuildHasher,
{
    map: FrozenMap<T, Nothing, BH>,
}

type Nothing = ();

impl<T> FrozenSet<T, BuildHasherDefault<DefaultHasher>>
where
    T: Eq + Hash,
{
    /// Creates a new frozen set using the default hasher to hash values.
    ///
    /// # Examples
    ///
    /// ```
    /// use frozen_collections::FrozenSet;
    /// use std::hash::RandomState;
    ///
    /// let set = FrozenSet::from_vec(vec!(1, 2, 3));
    /// ```
    #[must_use]
    pub fn from_vec(payload: Vec<T>) -> Self {
        Self::from_vec_with_hasher(payload, BuildHasherDefault::default())
    }
}

impl<T, BH> FrozenSet<T, BH>
where
    T: Eq + Hash,
    BH: BuildHasher,
{
    /// Creates a new frozen set which will use the given hasher to hash values.
    ///
    /// # Examples
    ///
    /// ```
    /// use frozen_collections::FrozenSet;
    /// use std::hash::RandomState;
    ///
    /// let set = FrozenSet::from_vec_with_hasher(vec!(1, 2, 3), RandomState::new());
    /// ```
    #[must_use]
    pub fn from_vec_with_hasher(payload: Vec<T>, bh: BH) -> Self {
        Self::new(payload.into_iter().map(|x| (x, ())).collect(), bh)
    }

    /// Creates a new frozen set which will use the given hasher to hash
    /// keys.
    ///
    /// # Examples
    ///
    /// ```
    /// use frozen_collections::FrozenSet;
    /// use std::hash::RandomState;
    ///
    /// let vec = vec!(1, 2, 3);
    /// let set = FrozenSet::from_iter_with_hasher(vec.iter(), RandomState::new());
    /// ```
    #[must_use]
    pub fn from_iter_with_hasher<U: IntoIterator<Item = T>>(iter: U, bh: BH) -> Self {
        Self::new(iter.into_iter().map(|x| (x, ())).collect::<Vec<_>>(), bh)
    }

    /// Creates a new frozen set which will use the given hasher to hash
    /// keys.
    ///
    /// # Examples
    ///
    /// ```
    /// use frozen_collections::FrozenSet;
    /// use std::hash::RandomState;
    ///
    /// let set = FrozenSet::with_hasher([1, 2, 3, 4], RandomState::new());
    /// ```
    #[must_use]
    pub fn with_hasher<const N: usize>(payload: [T; N], bh: BH) -> Self {
        Self::new(Vec::from_iter(payload.map(|x| (x, ()))), bh)
    }

    fn new(payload: Vec<(T, Nothing)>, bh: BH) -> Self {
        Self {
            map: FrozenMap::from_vec_with_hasher(payload, bh),
        }
    }

    /// Returns `true` if the set contains a value.
    ///
    /// # Examples
    ///
    /// ```
    /// use frozen_collections::FrozenSet;
    ///
    /// let set = FrozenSet::from([1, 2, 3]);
    /// assert!(set.contains(&1));
    /// assert!(!set.contains(&4));
    /// ```
    pub fn contains(&self, value: &T) -> bool {
        self.map.contains_key(value)
    }

    /// Returns a reference to the set's [`BuildHasher`].
    ///
    /// # Examples
    ///
    /// ```
    /// use frozen_collections::FrozenSet;
    /// use std::hash::RandomState;
    ///
    /// let hasher = RandomState::new();
    /// let set = FrozenSet::with_hasher([1, 2, 3], hasher);
    /// let hasher: &RandomState = set.hasher();
    /// ```
    pub fn hasher(&self) -> &BH {
        self.map.hasher()
    }

    /// Returns `true` if the set contains no elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use frozen_collections::FrozenSet;
    ///
    /// let x = FrozenSet::from([1, 2, 3]);
    /// assert!(!x.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns the number of elements in the set.
    ///
    /// # Examples
    ///
    /// ```
    /// use frozen_collections::FrozenSet;
    ///
    /// let x = FrozenSet::from([1, 2, 3]);
    /// assert_eq!(x.len(), 3);
    /// ```
    pub fn len(&self) -> usize {
        self.map.len()
    }

    /// An iterator visiting all elements in arbitrary order.
    /// The iterator element type is `&'a T`.
    ///
    /// # Examples
    ///
    /// ```
    /// use frozen_collections::FrozenSet;
    ///
    /// let set = FrozenSet::from(["a".to_string(), "b".to_string()]);
    ///
    /// // Will print in an arbitrary order.
    /// for x in set.iter() {
    ///     println!("{x}");
    /// }
    /// ```
    pub const fn iter(&self) -> Iter<T, BH> {
        Iter::new(self)
    }

    /// Returns a reference to the value in the set, if any, that is equal to the given value.
    ///
    /// # Examples
    ///
    /// ```
    /// use frozen_collections::FrozenSet;
    ///
    /// let set = FrozenSet::from([1, 2, 3]);
    /// assert_eq!(set.get(&2), Some(&2));
    /// assert_eq!(set.get(&4), None);
    /// ```
    pub fn get(&self, value: &T) -> Option<&T> {
        Some(self.map.get_key_value(value)?.0)
    }

    pub(crate) fn get_by_index(&self, index: usize) -> Option<&T> {
        Some(self.map.get_by_index(index)?.0)
    }

    /// Visits the values representing the difference,
    /// i.e., the values that are in `self` but not in `other`.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::HashSet;
    /// use std::hash::RandomState;
    /// use frozen_collections::FrozenSet;
    ///
    /// let a = FrozenSet::with_hasher([1, 2, 3], RandomState::new());
    /// let b = HashSet::from([4, 2, 3, 4]);
    ///
    /// // Can be seen as `a - b`.
    /// for x in a.difference(&b) {
    ///     println!("{x}"); // Print 1
    /// }
    ///
    /// let diff: HashSet<_> = a.difference(&b).collect();
    /// assert_eq!(diff, [1].iter().collect());
    /// ```
    pub const fn difference<'a>(&'a self, other: &'a HashSet<T, BH>) -> Difference<'a, T, BH> {
        Difference::new(self, other)
    }

    /// Visits the values representing the symmetric difference,
    /// i.e., the values that are in `self` or in `other` but not in both.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::HashSet;
    /// use std::hash::RandomState;
    /// use frozen_collections::FrozenSet;
    ///
    /// let a = FrozenSet::with_hasher([1, 2, 3], RandomState::new());
    /// let b = HashSet::from([4, 2, 3, 4]);
    ///
    /// // Print 1, 4 in arbitrary order.
    /// for x in a.symmetric_difference(&b) {
    ///     println!("{x}");
    /// }
    /// ```
    pub fn symmetric_difference<'a>(
        &'a self,
        other: &'a HashSet<T, BH>,
    ) -> SymmetricDifference<'a, T, BH> {
        SymmetricDifference::new(self, other)
    }

    /// Visits the values representing the union,
    /// i.e., all the values in `self` or `other`, without duplicates.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::HashSet;
    /// use std::hash::RandomState;
    /// use frozen_collections::FrozenSet;
    ///
    /// let a = FrozenSet::with_hasher([1, 2, 3], RandomState::new());
    /// let b = HashSet::from([4, 2, 3, 4]);
    ///
    /// // Print 1, 2, 3, 4 in arbitrary order.
    /// for x in a.union(&b) {
    ///     println!("{x}");
    /// }
    ///
    /// let union: HashSet<_> = a.union(&b).collect();
    /// assert_eq!(union, [1, 2, 3, 4].iter().collect());
    /// ```
    pub fn union<'a>(&'a self, other: &'a HashSet<T, BH>) -> Union<'a, T, BH> {
        Union::new(self, other)
    }

    /// Visits the values representing the intersection,
    /// i.e., the values that are both in `self` and `other`.
    ///
    /// When an equal element is present in `self` and `other`
    /// then the resulting `Intersection` may yield references to
    /// one or the other. This can be relevant if `T` contains fields which
    /// are not compared by its `Eq` implementation, and may hold different
    /// value between the two equal copies of `T` in the two sets.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::HashSet;
    /// use std::hash::RandomState;
    /// use frozen_collections::FrozenSet;
    ///
    /// let a = FrozenSet::with_hasher([1, 2, 3], RandomState::new());
    /// let b = HashSet::from([4, 2, 3, 4]);
    ///
    /// // Print 2, 3 in arbitrary order.
    /// for x in a.intersection(&b) {
    ///     println!("{x}");
    /// }
    ///
    /// let intersection: HashSet<_> = a.intersection(&b).collect();
    /// assert_eq!(intersection, [2, 3].iter().collect());
    /// ```
    pub const fn intersection<'a>(&'a self, other: &'a HashSet<T, BH>) -> Intersection<'a, T, BH> {
        Intersection::new(self, other)
    }

    /// Returns `true` if `self` has no elements in common with `other`.
    /// This is equivalent to checking for an empty intersection.
    pub fn is_disjoint<'a>(&'a self, other: &'a HashSet<T, BH>) -> bool {
        if self.len() <= other.len() {
            self.iter().all(|v| !other.contains(v))
        } else {
            other.iter().all(|v| !self.contains(v))
        }
    }

    /// Returns `true` if the set is a subset of another,
    /// i.e., `other` contains at least all the values in `self`.
    pub fn is_subset<'a>(&'a self, other: &'a HashSet<T, BH>) -> bool {
        if self.len() <= other.len() {
            self.iter().all(|v| other.contains(v))
        } else {
            false
        }
    }

    /// Returns `true` if the set is a superset of another,
    /// i.e., `self` contains at least all the values in `other`.
    pub fn is_superset<'a>(&'a self, other: &'a HashSet<T, BH>) -> bool {
        if other.len() <= self.len() {
            other.iter().all(|v| self.contains(v))
        } else {
            false
        }
    }
}

impl<T, const N: usize> From<[T; N]> for FrozenSet<T, BuildHasherDefault<DefaultHasher>>
where
    T: Eq + Hash,
{
    fn from(payload: [T; N]) -> Self {
        Self::from_vec(Vec::from_iter(payload))
    }
}

impl<T> FromIterator<T> for FrozenSet<T, BuildHasherDefault<DefaultHasher>>
where
    T: Eq + Hash,
{
    fn from_iter<U: IntoIterator<Item = T>>(iter: U) -> Self {
        Self::from_vec(Vec::from_iter(iter))
    }
}

impl<T, BH> Default for FrozenSet<T, BH>
where
    T: Eq + Hash,
    BH: BuildHasher + Default,
{
    fn default() -> Self {
        Self {
            map: FrozenMap::default(),
        }
    }
}

impl<T, BH> Debug for FrozenSet<T, BH>
where
    T: Eq + Hash + Debug,
    BH: BuildHasher,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        self.map.fmt(f)
    }
}

impl<T, BH> PartialEq<Self> for FrozenSet<T, BH>
where
    T: Eq + Hash,
    BH: BuildHasher,
{
    fn eq(&self, other: &Self) -> bool {
        self.map.eq(&other.map)
    }
}

impl<T, BH> Eq for FrozenSet<T, BH>
where
    T: Eq + Hash,
    BH: BuildHasher,
{
}

impl<T, BH> Clone for FrozenSet<T, BH>
where
    T: Eq + Hash + Clone,
    BH: BuildHasher + Clone,
{
    fn clone(&self) -> Self {
        Self {
            map: self.map.clone(),
        }
    }
}

impl<T, BH> BitOr<&HashSet<T, BH>> for &FrozenSet<T, BH>
where
    T: Eq + Hash + Clone,
    BH: BuildHasher + Default,
{
    type Output = HashSet<T, BH>;

    fn bitor(self, rhs: &HashSet<T, BH>) -> HashSet<T, BH> {
        self.union(rhs).cloned().collect()
    }
}

impl<T, BH> BitAnd<&HashSet<T, BH>> for &FrozenSet<T, BH>
where
    T: Eq + Hash + Clone,
    BH: BuildHasher + Default,
{
    type Output = HashSet<T, BH>;

    fn bitand(self, rhs: &HashSet<T, BH>) -> HashSet<T, BH> {
        self.intersection(rhs).cloned().collect()
    }
}

impl<T, BH> BitXor<&HashSet<T, BH>> for &FrozenSet<T, BH>
where
    T: Eq + Hash + Clone,
    BH: BuildHasher + Default,
{
    type Output = HashSet<T, BH>;

    fn bitxor(self, rhs: &HashSet<T, BH>) -> HashSet<T, BH> {
        self.symmetric_difference(rhs).cloned().collect()
    }
}

impl<T, BH> Sub<&HashSet<T, BH>> for &FrozenSet<T, BH>
where
    T: Eq + Hash + Clone,
    BH: BuildHasher + Default,
{
    type Output = HashSet<T, BH>;

    fn sub(self, rhs: &HashSet<T, BH>) -> HashSet<T, BH> {
        self.difference(rhs).cloned().collect()
    }
}

impl<'a, T, BH> IntoIterator for &'a FrozenSet<T, BH>
where
    T: Eq + Hash,
    BH: BuildHasher,
{
    type Item = &'a T;
    type IntoIter = Iter<'a, T, BH>;

    fn into_iter(self) -> Iter<'a, T, BH> {
        self.iter()
    }
}
