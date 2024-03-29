use core::fmt::{Debug, Formatter, Result};
use core::hash::{BuildHasher, Hash};
use core::iter::Chain;
use core::iter::FusedIterator;
use std::collections::HashSet;

use crate::FrozenSet;

/// An iterator over the items of a frozen set.
///
/// This `struct` is created by the [`iter`] method on [`FrozenSet`].
/// See its documentation for more.
///
/// [`iter`]: FrozenSet::iter
pub struct Iter<'a, T, BH>
where
    T: Hash + Eq,
    BH: BuildHasher,
{
    set: &'a FrozenSet<T, BH>,
    index: usize,
}

impl<'a, T, BH> Iter<'a, T, BH>
where
    T: Hash + Eq,
    BH: BuildHasher,
{
    pub const fn new(set: &'a FrozenSet<T, BH>) -> Self {
        Self { set, index: 0 }
    }
}

impl<'a, T, BH> Clone for Iter<'a, T, BH>
where
    T: Hash + Eq,
    BH: BuildHasher,
{
    fn clone(&self) -> Self {
        Self {
            set: self.set,
            index: self.index,
        }
    }
}

impl<'a, T, BH> Iterator for Iter<'a, T, BH>
where
    T: Hash + Eq,
    BH: BuildHasher,
{
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        let result = self.set.get_by_index(self.index);

        if result.is_some() {
            self.index += 1;
        }

        result
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, Some(self.set.len()))
    }

    fn count(self) -> usize
    where
        Self: Sized,
    {
        self.len()
    }
}

impl<'a, T, BH> ExactSizeIterator for Iter<'a, T, BH>
where
    T: Hash + Eq,
    BH: BuildHasher,
{
    fn len(&self) -> usize {
        self.set.len() - self.index
    }
}

impl<'a, T, BH> FusedIterator for Iter<'a, T, BH>
where
    T: Hash + Eq,
    BH: BuildHasher,
{
}

impl<'a, T, BH> Debug for Iter<'a, T, BH>
where
    T: Hash + Eq + Debug,
    BH: BuildHasher,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

/// A lazy iterator producing elements in the union of sets.
///
/// This `struct` is created by the [`union`] method on [`FrozenSet`].
/// See its documentation for more.
///
/// [`union`]: FrozenSet::union
pub struct Union<'a, T, BH>
where
    T: Hash + Eq,
    BH: BuildHasher,
{
    iter: Chain<Iter<'a, T, BH>, HashSetDifference<'a, T, BH>>,
}

impl<'a, T, BH> Union<'a, T, BH>
where
    T: Hash + Eq,
    BH: BuildHasher,
{
    pub fn new(this: &'a FrozenSet<T, BH>, other: &'a HashSet<T, BH>) -> Self {
        Self {
            iter: this.iter().chain(HashSetDifference::new(other, this)),
        }
    }
}

impl<'a, T, BH> Clone for Union<'a, T, BH>
where
    T: Hash + Eq,
    BH: BuildHasher,
{
    fn clone(&self) -> Self {
        Self {
            iter: self.iter.clone(),
        }
    }
}

impl<'a, T, BH> Iterator for Union<'a, T, BH>
where
    T: Hash + Eq,
    BH: BuildHasher,
{
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        self.iter.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }

    fn count(self) -> usize {
        self.iter.count()
    }

    fn fold<B, F>(self, init: B, f: F) -> B
    where
        Self: Sized,
        F: FnMut(B, Self::Item) -> B,
    {
        self.iter.fold(init, f)
    }
}

impl<'a, T, BH> FusedIterator for Union<'a, T, BH>
where
    T: Hash + Eq,
    BH: BuildHasher,
{
}

impl<'a, T, BH> Debug for Union<'a, T, BH>
where
    T: Hash + Eq + Debug,
    BH: BuildHasher,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

/// A lazy iterator producing elements in the symmetric difference of sets.
///
/// This `struct` is created by the [`symmetric_difference`] method on
/// [`FrozenSet`]. See its documentation for more.
///
/// [`symmetric_difference`]: FrozenSet::symmetric_difference
pub struct SymmetricDifference<'a, T, BH>
where
    T: Hash + Eq,
    BH: BuildHasher,
{
    iter: Chain<Difference<'a, T, BH>, HashSetDifference<'a, T, BH>>,
}

impl<'a, T, BH> SymmetricDifference<'a, T, BH>
where
    T: Hash + Eq,
    BH: BuildHasher,
{
    pub fn new(this: &'a FrozenSet<T, BH>, other: &'a HashSet<T, BH>) -> Self {
        Self {
            iter: this
                .difference(other)
                .chain(HashSetDifference::new(other, this)),
        }
    }
}

impl<'a, T, BH> Clone for SymmetricDifference<'a, T, BH>
where
    T: Hash + Eq,
    BH: BuildHasher,
{
    fn clone(&self) -> Self {
        Self {
            iter: self.iter.clone(),
        }
    }
}

impl<'a, T, BH> Iterator for SymmetricDifference<'a, T, BH>
where
    T: Hash + Eq,
    BH: BuildHasher,
{
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        self.iter.next()
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
    fn fold<B, F>(self, init: B, f: F) -> B
    where
        Self: Sized,
        F: FnMut(B, Self::Item) -> B,
    {
        self.iter.fold(init, f)
    }
}

impl<'a, T, BH> FusedIterator for SymmetricDifference<'a, T, BH>
where
    T: Hash + Eq,
    BH: BuildHasher,
{
}

impl<'a, T, BH> Debug for SymmetricDifference<'a, T, BH>
where
    T: Hash + Eq + Debug,
    BH: BuildHasher,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

/// A lazy iterator producing elements in the difference of sets.
///
/// This `struct` is created by the [`difference`] method on [`FrozenSet`].
/// See its documentation for more.
///
/// [`difference`]: FrozenSet::difference
pub struct Difference<'a, T, BH>
where
    T: Hash + Eq,
    BH: BuildHasher,
{
    // iterator of the first set
    iter: Iter<'a, T, BH>,

    // the second set
    other: &'a HashSet<T, BH>,
}

impl<'a, T, BH> Difference<'a, T, BH>
where
    T: Hash + Eq,
    BH: BuildHasher,
{
    pub const fn new(this: &'a FrozenSet<T, BH>, other: &'a HashSet<T, BH>) -> Self {
        Self {
            iter: this.iter(),
            other,
        }
    }
}

impl<'a, T, BH> Clone for Difference<'a, T, BH>
where
    T: Hash + Eq,
    BH: BuildHasher,
{
    fn clone(&self) -> Self {
        Self {
            iter: self.iter.clone(),
            ..*self
        }
    }
}

impl<'a, T, BH> Iterator for Difference<'a, T, BH>
where
    T: Hash + Eq,
    BH: BuildHasher,
{
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let elt = self.iter.next()?;
            if !self.other.contains(elt) {
                return Some(elt);
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let (_, upper) = self.iter.size_hint();
        (0, upper)
    }

    fn fold<B, F>(self, init: B, mut f: F) -> B
    where
        Self: Sized,
        F: FnMut(B, Self::Item) -> B,
    {
        self.iter.fold(init, |acc, elt| {
            if self.other.contains(elt) {
                acc
            } else {
                f(acc, elt)
            }
        })
    }
}

impl<'a, T, BH> FusedIterator for Difference<'a, T, BH>
where
    T: Hash + Eq,
    BH: BuildHasher,
{
}

impl<'a, T, BH> Debug for Difference<'a, T, BH>
where
    T: Hash + Eq + Debug,
    BH: BuildHasher,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

/// A lazy iterator producing elements in the intersection of sets.
///
/// This `struct` is created by the [`intersection`] method on [`FrozenSet`].
/// See its documentation for more.
///
/// [`intersection`]: FrozenSet::intersection
pub struct Intersection<'a, T, BH>
where
    T: Hash + Eq,
    BH: BuildHasher,
{
    // iterator of the first set
    iter: Iter<'a, T, BH>,

    // the second set
    other: &'a HashSet<T, BH>,
}

impl<'a, T, BH> Intersection<'a, T, BH>
where
    T: Hash + Eq,
    BH: BuildHasher,
{
    pub const fn new(this: &'a FrozenSet<T, BH>, other: &'a HashSet<T, BH>) -> Self {
        Self {
            iter: this.iter(),
            other,
        }
    }
}

impl<'a, T, BH> Clone for Intersection<'a, T, BH>
where
    T: Hash + Eq,
    BH: BuildHasher,
{
    fn clone(&self) -> Self {
        Self {
            iter: self.iter.clone(),
            ..*self
        }
    }
}

impl<'a, T, BH> Iterator for Intersection<'a, T, BH>
where
    T: Hash + Eq,
    BH: BuildHasher,
{
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let elt = self.iter.next()?;
            if self.other.contains(elt) {
                return Some(elt);
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let (_, upper) = self.iter.size_hint();
        (0, upper)
    }

    fn fold<B, F>(self, init: B, mut f: F) -> B
    where
        Self: Sized,
        F: FnMut(B, Self::Item) -> B,
    {
        self.iter.fold(init, |acc, elt| {
            if self.other.contains(elt) {
                f(acc, elt)
            } else {
                acc
            }
        })
    }
}

impl<'a, T, BH> FusedIterator for Intersection<'a, T, BH>
where
    T: Hash + Eq,
    BH: BuildHasher,
{
}

impl<'a, T, BH> Debug for Intersection<'a, T, BH>
where
    T: Hash + Eq + Debug,
    BH: BuildHasher,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

struct HashSetDifference<'a, T, BH>
where
    T: Hash + Eq,
    BH: BuildHasher,
{
    // iterator of the first set
    iter: std::collections::hash_set::Iter<'a, T>,

    // the second set
    other: &'a FrozenSet<T, BH>,
}

impl<'a, T, BH> HashSetDifference<'a, T, BH>
where
    T: Hash + Eq,
    BH: BuildHasher,
{
    pub fn new(this: &'a HashSet<T, BH>, other: &'a FrozenSet<T, BH>) -> Self {
        Self {
            iter: this.iter(),
            other,
        }
    }
}

impl<'a, T, BH> Clone for HashSetDifference<'a, T, BH>
where
    T: Hash + Eq,
    BH: BuildHasher,
{
    fn clone(&self) -> Self {
        Self {
            iter: self.iter.clone(),
            ..*self
        }
    }
}

impl<'a, T, BH> Iterator for HashSetDifference<'a, T, BH>
where
    T: Hash + Eq,
    BH: BuildHasher,
{
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let elt = self.iter.next()?;
            if !self.other.contains(elt) {
                return Some(elt);
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let (_, upper) = self.iter.size_hint();
        (0, upper)
    }

    fn fold<B, F>(self, init: B, mut f: F) -> B
    where
        Self: Sized,
        F: FnMut(B, Self::Item) -> B,
    {
        self.iter.fold(init, |acc, elt| {
            if self.other.contains(elt) {
                acc
            } else {
                f(acc, elt)
            }
        })
    }
}

impl<'a, T, BH> FusedIterator for HashSetDifference<'a, T, BH>
where
    T: Hash + Eq,
    BH: BuildHasher,
{
}
