use core::fmt::{Debug, Formatter, Result};
use core::hash::{BuildHasher, Hash};
use core::iter::FusedIterator;

use crate::FrozenMap;

/// An iterator over the entries of a `FrozenMap`.
///
/// This `struct` is created by the [`iter`] method on [`FrozenMap`]. See its
/// documentation for more.
///
/// [`iter`]: FrozenMap::iter
pub struct Iter<'a, K, V, BH>
where
    K: Hash + Eq,
    BH: BuildHasher,
{
    map: &'a FrozenMap<K, V, BH>,
    index: usize,
}

impl<'a, K, V, BH> Iter<'a, K, V, BH>
where
    K: Hash + Eq,
    BH: BuildHasher,
{
    pub const fn new(map: &'a FrozenMap<K, V, BH>) -> Self {
        Self { map, index: 0 }
    }
}

impl<'a, K, V, BH> Clone for Iter<'a, K, V, BH>
where
    K: Hash + Eq,
    BH: BuildHasher,
{
    fn clone(&self) -> Self {
        Self {
            map: self.map,
            index: self.index,
        }
    }
}

impl<'a, K, V, BH> Iterator for Iter<'a, K, V, BH>
where
    K: Hash + Eq,
    BH: BuildHasher,
{
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        let result = self.map.get_by_index(self.index);

        if result.is_some() {
            self.index += 1;
        }

        result
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, Some(self.map.len()))
    }

    fn count(self) -> usize
    where
        Self: Sized,
    {
        self.len()
    }
}

impl<'a, K, V, BH> ExactSizeIterator for Iter<'a, K, V, BH>
where
    K: Hash + Eq,
    BH: BuildHasher,
{
    fn len(&self) -> usize {
        self.map.len() - self.index
    }
}

impl<'a, K, V, BH> FusedIterator for Iter<'a, K, V, BH>
where
    K: Hash + Eq,
    BH: BuildHasher,
{
}

impl<'a, K, V, BH> Debug for Iter<'a, K, V, BH>
where
    K: Hash + Eq + Debug,
    V: Debug,
    BH: BuildHasher,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

/// An iterator over the keys of a `FrozenMap`.
///
/// This `struct` is created by the [`keys`] method on [`FrozenMap`]. See its
/// documentation for more.
///
/// [`keys`]: FrozenMap::keys
pub struct Keys<'a, K, V, BH>
where
    K: Hash + Eq,
    BH: BuildHasher,
{
    inner: Iter<'a, K, V, BH>,
}

impl<'a, K, V, BH> Keys<'a, K, V, BH>
where
    K: Hash + Eq,
    BH: BuildHasher,
{
    pub const fn new(map: &'a FrozenMap<K, V, BH>) -> Self {
        Self {
            inner: Iter::new(map),
        }
    }
}

impl<'a, K, V, BH> Clone for Keys<'a, K, V, BH>
where
    K: Hash + Eq,
    BH: BuildHasher,
{
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
        }
    }
}

impl<'a, K, V, BH> Iterator for Keys<'a, K, V, BH>
where
    K: Hash + Eq,
    BH: BuildHasher,
{
    type Item = &'a K;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|x| x.0)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }

    fn count(self) -> usize {
        self.inner.count()
    }

    fn fold<B, F>(self, init: B, mut f: F) -> B
    where
        Self: Sized,
        F: FnMut(B, Self::Item) -> B,
    {
        self.inner.fold(init, |acc, (k, _)| f(acc, k))
    }
}

impl<'a, K, V, BH> ExactSizeIterator for Keys<'a, K, V, BH>
where
    K: Hash + Eq,
    BH: BuildHasher,
{
    fn len(&self) -> usize {
        self.inner.len()
    }
}

impl<'a, K, V, BH> FusedIterator for Keys<'a, K, V, BH>
where
    K: Hash + Eq,
    BH: BuildHasher,
{
}

impl<'a, K, V, BH> Debug for Keys<'a, K, V, BH>
where
    K: Hash + Eq + Debug,
    V: Debug,
    BH: BuildHasher,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

/// An iterator over the values of a `FrozenMap`.
///
/// This `struct` is created by the [`values`] method on [`FrozenMap`]. See its
/// documentation for more.
///
/// [`values`]: FrozenMap::values
pub struct Values<'a, K, V, BH>
where
    K: Hash + Eq,
    BH: BuildHasher,
{
    inner: Iter<'a, K, V, BH>,
}

impl<'a, K, V, BH> Values<'a, K, V, BH>
where
    K: Hash + Eq,
    BH: BuildHasher,
{
    pub const fn new(map: &'a FrozenMap<K, V, BH>) -> Self {
        Self {
            inner: Iter::new(map),
        }
    }
}

impl<'a, K, V, BH> Clone for Values<'a, K, V, BH>
where
    K: Hash + Eq,
    BH: BuildHasher,
{
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
        }
    }
}

impl<'a, K, V, BH> Iterator for Values<'a, K, V, BH>
where
    K: Hash + Eq,
    BH: BuildHasher,
{
    type Item = &'a V;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|x| x.1)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }

    fn count(self) -> usize {
        self.inner.count()
    }

    fn fold<B, F>(self, init: B, mut f: F) -> B
    where
        Self: Sized,
        F: FnMut(B, Self::Item) -> B,
    {
        self.inner.fold(init, |acc, (_, v)| f(acc, v))
    }
}

impl<'a, K, V, BH> ExactSizeIterator for Values<'a, K, V, BH>
where
    K: Hash + Eq,
    BH: BuildHasher,
{
    fn len(&self) -> usize {
        self.inner.len()
    }
}

impl<'a, K, V, BH> FusedIterator for Values<'a, K, V, BH>
where
    K: Hash + Eq,
    BH: BuildHasher,
{
}

impl<'a, K, V, BH> Debug for Values<'a, K, V, BH>
where
    K: Hash + Eq + Debug,
    V: Debug,
    BH: BuildHasher,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        f.debug_list().entries(self.clone()).finish()
    }
}
