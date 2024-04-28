//! Iterators for the listpack.

use redis_custom_allocator::CustomAllocator;

use crate::{Listpack, ListpackEntryRef, ListpackEntryRemoved};

/// An iterator over the elements of a listpack.
///
/// # Example
///
/// ```
/// use listpack_redis::Listpack;
///
/// let mut listpack: Listpack = Listpack::default();
/// listpack.push("Hello");
/// listpack.push("World");
/// let mut iter = listpack.iter();
/// assert_eq!(iter.next().unwrap().to_string(), "Hello");
/// assert_eq!(iter.next().unwrap().to_string(), "World");
/// assert!(iter.next().is_none());
/// ```
#[derive(Debug)]
pub struct ListpackIter<'a, Allocator>
where
    Allocator: CustomAllocator,
{
    pub(crate) listpack: &'a Listpack<Allocator>,
    pub(crate) index: usize,
}

impl<'a, Allocator> Iterator for ListpackIter<'a, Allocator>
where
    Allocator: CustomAllocator,
{
    type Item = &'a ListpackEntryRef;

    fn next(&mut self) -> Option<Self::Item> {
        if self.index >= self.listpack.len() {
            return None;
        }

        let element = self.listpack.get(self.index)?;

        self.index += 1;

        Some(element)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.index, Some(self.listpack.len()))
    }
}

impl<Allocator> DoubleEndedIterator for ListpackIter<'_, Allocator>
where
    Allocator: CustomAllocator,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.index >= self.listpack.len() {
            return None;
        }

        let index = self.listpack.len() - self.index - 1;
        let element = self.listpack.get(index)?;

        self.index += 1;

        Some(element)
    }
}

/// An iterator over the elements of a listpack, which returns the
/// elements as [`ListpackEntryRemoved`]. This iterator owns the
/// listpack.
#[derive(Debug)]
pub struct ListpackIntoIter<Allocator>
where
    Allocator: CustomAllocator,
{
    pub(crate) listpack: Listpack<Allocator>,
    pub(crate) index: usize,
}

impl<Allocator> Iterator for ListpackIntoIter<Allocator>
where
    Allocator: CustomAllocator,
{
    type Item = ListpackEntryRemoved;

    fn next(&mut self) -> Option<Self::Item> {
        if self.index >= self.listpack.len() {
            return None;
        }

        let element = self.listpack.get(self.index)?;

        self.index += 1;

        Some(element.into())
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.index, Some(self.listpack.len()))
    }
}

impl<Allocator> DoubleEndedIterator for ListpackIntoIter<Allocator>
where
    Allocator: CustomAllocator,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.index >= self.listpack.len() {
            return None;
        }

        let index = self.listpack.len() - self.index - 1;
        let element = self.listpack.get(index)?;

        self.index += 1;

        Some(element.into())
    }
}

/// An iterator over the elements of a listpack, which returns
/// contiguous windows of elements.
///
/// # Example
///
/// ```
/// use listpack_redis::Listpack;
///
/// let mut listpack: Listpack = Listpack::default();
/// listpack.push("Hello");
/// listpack.push("World");
/// listpack.push("!");
/// let mut iter = listpack.windows(2);
/// assert_eq!(iter.next().unwrap().len(), 2);
/// assert_eq!(iter.next().unwrap().len(), 2);
/// assert!(iter.next().is_none());
/// ```
///
/// Or with values:
///
/// ```
/// use listpack_redis::Listpack;
///
/// let mut listpack: Listpack = Listpack::default();
/// listpack.push("Hello");
/// listpack.push("World");
/// listpack.push("!");
///
/// let mut iter = listpack.windows(2);
///
/// let value = iter.next().unwrap();
///
/// assert_eq!(value[0].to_string(), "Hello");
/// assert_eq!(value[1].to_string(), "World");
/// assert_eq!(value.len(), 2);
///
/// let value = iter.next().unwrap();
///
/// assert_eq!(value[0].to_string(), "World");
/// assert_eq!(value[1].to_string(), "!");
/// assert_eq!(value.len(), 2);
///
/// assert!(iter.next().is_none());
/// ```
#[derive(Debug)]
pub struct ListpackWindows<'a, Allocator>
where
    Allocator: CustomAllocator,
{
    pub(crate) listpack: &'a Listpack<Allocator>,
    pub(crate) size: usize,
    pub(crate) index: usize,
}

impl<'a, Allocator> Iterator for ListpackWindows<'a, Allocator>
where
    Allocator: CustomAllocator,
{
    type Item = Vec<&'a ListpackEntryRef>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.index + self.size > self.listpack.len() {
            return None;
        }

        let mut window = Vec::with_capacity(self.size);
        for i in self.index..self.index + self.size {
            window.push(self.listpack.get(i).unwrap());
        }

        self.index += 1;

        Some(window)
    }
}

impl<Allocator> DoubleEndedIterator for ListpackWindows<'_, Allocator>
where
    Allocator: CustomAllocator,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        let length = self.listpack.len();

        if self.index + self.size > length {
            return None;
        }

        let mut window = Vec::with_capacity(self.size);
        for i in length - self.index - self.size..length - self.index + self.size {
            window.push(self.listpack.get(i).unwrap());
        }

        self.index += 1;

        Some(window)
    }
}

/// An iterator over the elements of a listpack, which returns chunks
/// of elements.
///
/// # Example
///
/// ```
/// use listpack_redis::Listpack;
///
/// let mut listpack: Listpack = Listpack::default();
/// listpack.push("Hello");
/// listpack.push("World");
/// listpack.push("!");
/// let mut iter = listpack.chunks(2);
/// assert_eq!(iter.next().unwrap().len(), 2);
/// assert_eq!(iter.next().unwrap().len(), 1);
/// assert!(iter.next().is_none());
/// ```
///
/// Or with values:
///
/// ```
/// use listpack_redis::Listpack;
///
/// let mut listpack: Listpack = Listpack::default();
/// listpack.push("Hello");
/// listpack.push("World");
/// listpack.push("!");
///
/// let mut iter = listpack.chunks(2);
///
/// let value = iter.next().unwrap();
///
/// assert_eq!(value[0].to_string(), "Hello");
/// assert_eq!(value[1].to_string(), "World");
/// assert_eq!(value.len(), 2);
///
/// let value = iter.next().unwrap();
///
/// assert_eq!(value[0].to_string(), "!");
/// assert_eq!(value.len(), 1);
///
/// assert!(iter.next().is_none());
/// ```
#[derive(Debug)]

pub struct ListpackChunks<'a, Allocator>
where
    Allocator: CustomAllocator,
{
    pub(crate) listpack: &'a Listpack<Allocator>,
    pub(crate) size: usize,
    pub(crate) index: usize,
}

impl<'a, Allocator> Iterator for ListpackChunks<'a, Allocator>
where
    Allocator: CustomAllocator,
{
    type Item = Vec<&'a ListpackEntryRef>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.index >= self.listpack.len() {
            return None;
        }

        let remaining = (self.listpack.len() - self.index).min(self.size);
        let mut chunk = Vec::with_capacity(remaining);
        for i in self.index..self.index + remaining {
            chunk.push(self.listpack.get(i).unwrap());
        }

        self.index += remaining;

        Some(chunk)
    }
}

/// Removes the specified range from the listpack in bulk, returning all
/// removed elements as an iterator. If the iterator is dropped before
/// being fully consumed, it drops the remaining removed elements.
///
/// The returned iterator keeps a mutable borrow on the vector to
/// optimize its implementation.
///
/// # Example
///
/// ```
/// use listpack_redis::Listpack;
///
/// let mut listpack: Listpack = Listpack::default();
/// listpack.push("Hello");
/// listpack.push("World");
/// listpack.push("!");
/// let removed = listpack.drain(..).collect::<Vec<_>>();
/// assert!(listpack.is_empty());
/// assert_eq!(removed.len(), 3);

#[derive(Debug)]
pub struct ListpackDrain<'a, Allocator>
where
    Allocator: CustomAllocator,
{
    pub(crate) listpack: &'a mut Listpack<Allocator>,
    pub(crate) offset: usize,
    pub(crate) start: usize,
    pub(crate) end: usize,
}

impl<'a, Allocator> Iterator for ListpackDrain<'a, Allocator>
where
    Allocator: CustomAllocator,
{
    type Item = ListpackEntryRemoved;

    fn next(&mut self) -> Option<Self::Item> {
        if self.offset >= self.end - self.start || self.offset + self.start >= self.listpack.len() {
            return None;
        }

        let element = self.listpack.get(self.start + self.offset).unwrap().into();

        self.offset += 1;

        Some(element)
    }
}

impl<'a, Allocator> DoubleEndedIterator for ListpackDrain<'a, Allocator>
where
    Allocator: CustomAllocator,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.offset >= self.end - self.start || self.offset + self.start >= self.listpack.len() {
            return None;
        }

        let element = self
            .listpack
            .get(self.end - self.offset - 1)
            .unwrap()
            .into();
        self.offset += 1;

        Some(element)
    }
}

impl<Allocator> Drop for ListpackDrain<'_, Allocator>
where
    Allocator: CustomAllocator,
{
    fn drop(&mut self) {
        self.listpack
            .remove_range(self.start, self.end - self.start);
    }
}
//
// /// A mutable iterator over the elements of a listpack.
// ///
// /// # Example
// ///
// /// ```
// /// use listpack_redis::Listpack;
// ///
// /// let mut listpack = Listpack::default();
// /// listpack.push("Hello");
// /// listpack.push("World");
// /// let mut iter = listpack.iter_mut();
// /// assert_eq!(iter.next().unwrap().to_string(), "Hello");
// /// assert_eq!(iter.next().unwrap().to_string(), "World");
// /// assert!(iter.next().is_none());
// /// ```
// #[derive(Debug)]
// pub struct ListpackIterMut<'a> {
//     listpack: &'a mut Listpack,
//     index: usize,
// }

// impl<'a> Iterator for ListpackIterMut<'a> {
//     type Item = ListpackEntryMutable<'a>;

//     fn next(&mut self) -> Option<Self::Item> {
//         if self.index >= self.listpack.len() {
//             return None;
//         }

//         let element = self.listpack.get_mut(self.index).unwrap();

//         self.index += 1;

//         Some(element)
//     }

//     fn size_hint(&self) -> (usize, Option<usize>) {
//         (self.index, Some(self.listpack.len()))
//     }
// }

// impl<'a> DoubleEndedIterator for ListpackIterMut<'a> {
//     fn next_back(&mut self) -> Option<Self::Item> {
//         if self.index >= self.listpack.len() {
//             return None;
//         }

//         let index = self.listpack.len() - self.index - 1;
//         let element = self.listpack.get(self.index).unwrap();
//         let entry = ListpackEntryMutable {
//             listpack: self.listpack,
//             entry: element,
//             index: self.index - 1,
//         };

//         self.index += 1;

//         Some(entry)
//     }
// }
