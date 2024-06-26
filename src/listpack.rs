//! The listpack interface and main implementation.
//!
//! The listpack data structure is a memory-efficient and compact
//! representation of a list of elements. It is used in Redis to store
//! lists of strings and numbers. The listpack data structure is
//! implemented in the C programming language, and this crate
//! reimplements the listpack data structure in Rust, also extending its
//! functionality and the data types it can store.

use std::{
    alloc::Layout,
    fmt::{Debug, Write},
    hash::Hash,
    ops::{Deref, DerefMut, Index, RangeBounds},
    ptr::NonNull,
};

use redis_custom_allocator::{CustomAllocator, MemoryConsumption};

use crate::{
    allocator::ListpackAllocator,
    compression::{AbstractPointerTag, AllocationPointerTag, Taggable, TryEncode},
    entry::{ListpackEntryInsert, ListpackEntryRef, ListpackEntryRemoved},
    error::{AllocationError, Result},
    iter::{ListpackChunks, ListpackIntoIter, ListpackIter, ListpackWindows},
    ListpackEntryEncodingType, ListpackEntryMutable,
};

/// The last byte of the allocator for the listpack should always be
/// this value. It is used to detect overflows in the listpack.
const END_MARKER: u8 = 0xFF;

/// A location where an element should be inserted.
#[derive(Debug, Copy, Clone)]
pub enum InsertionPlacement {
    /// Before the element specified by the index.
    Before(usize),
    /// After the element specified by the index.
    After(usize),
    /// Replace the referred element with the new one, accessible by
    /// the provided index.
    Replace(usize),
}

impl InsertionPlacement {
    /// Returns the index of the element where the new element should be
    /// inserted.
    pub fn index(&self) -> usize {
        match self {
            Self::Before(index) | Self::After(index) | Self::Replace(index) => *index,
        }
    }

    /// Returns the index of the element to replace, if the placement is
    /// to replace an element.
    pub fn to_replace(&self) -> Option<usize> {
        match self {
            Self::Replace(index) => Some(*index),
            _ => None,
        }
    }
}

/// The fitting requirement for the listpack, after a test for an entry
/// to be inserted. See [`Listpack::can_fit_entry`].
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum FittingRequirement {
    /// The listpack must be extended by the given amount of bytes.
    Grow(usize),
    /// The listpack must be shrinked by the given amount of bytes.
    Shrink(usize),
    /// The listpack does not need to be changed.
    NoChange,
}

impl FittingRequirement {
    /// Returns the number of bytes regardless of the requirement.
    #[allow(unused)]
    fn get_size(&self) -> usize {
        match self {
            Self::Grow(size) => *size,
            Self::Shrink(size) => *size,
            Self::NoChange => 0,
        }
    }

    fn from_difference(needed: usize, available: usize) -> Self {
        match needed.cmp(&available) {
            std::cmp::Ordering::Greater => Self::Grow(needed - available),
            std::cmp::Ordering::Less => Self::Shrink(available - needed),
            std::cmp::Ordering::Equal => Self::NoChange,
        }
    }
}

impl From<isize> for FittingRequirement {
    fn from(size: isize) -> Self {
        match size.cmp(&0) {
            std::cmp::Ordering::Greater => Self::Grow(size as usize),
            std::cmp::Ordering::Less => Self::Shrink(size.unsigned_abs()),
            std::cmp::Ordering::Equal => Self::NoChange,
        }
    }
}

impl From<usize> for FittingRequirement {
    fn from(size: usize) -> Self {
        match size.cmp(&0) {
            std::cmp::Ordering::Greater => Self::Grow(size),
            std::cmp::Ordering::Equal => Self::NoChange,
            _ => unreachable!("The size cannot be negative."),
        }
    }
}

/// The header of the listpack data structure. Can only be obtained
/// from an existing listpack using the [`Listpack::header_ref`] method.
#[repr(C, packed(1))]
#[derive(Debug, Copy, Clone, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub struct ListpackHeader {
    /// An unsigned integer holding the total amount of bytes
    /// representing the listpack. Including the header itself and the
    /// terminator. This basically is the total size of the allocation
    /// needed to hold the listpack and allows to jump at the end in
    /// order to scan the listpack in reverse order, from the last to
    /// the first element, when needed.
    total_bytes: u32,
    /// An unsigned integer holding the total number of elements the
    /// listpack holds. However if this field is set to 65535, which is
    /// the greatest unsigned integer representable in 16 bit, it means
    /// that the number of listpack elements is not known, so a
    /// LIST-LENGTH operation will require to fully scan the listpack.
    /// This happens when, at some point, the listpack has a number of
    /// elements equal or greater than 65535. The num-elements field
    /// will be set again to a lower number the first time a
    /// LIST-LENGTH operation detects the elements count returned in the
    /// representable range.
    num_elements: u16,
}

impl ListpackHeader {
    // TODO: This is better and more correct, future-proof, but the
    // size_of_val function is not yet stable.
    //
    // /// The maximum number of bytes the listpack header may hold.
    // const MAXIMUM_TOTAL_BYTES: usize = std::mem::size_of_val(&Self::total_bytes) * 8;
    // /// The maximum number of bytes allowed to be used by the elements.
    // const MAXIMUM_ELEMENT_BYTES: usize = Self::MAXIMUM_TOTAL_BYTES
    //     + std::mem::size_of_val(&END_MARKER)
    //     - std::mem::size_of::<Self>();

    /// The maximum number of bytes the listpack header may hold.
    const MAXIMUM_TOTAL_BYTES: usize = std::u32::MAX as usize;
    /// The maximum number of bytes allowed to be used by the elements.
    const MAXIMUM_ELEMENT_BYTES: usize =
        Self::MAXIMUM_TOTAL_BYTES + std::mem::size_of::<u8>() - std::mem::size_of::<Self>();

    /// Returns the header from the given pointer.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the pointer is valid.
    pub unsafe fn from_ptr<'a>(ptr: *const u8) -> &'a Self {
        unsafe { ptr.cast::<Self>().as_ref().unwrap() }
    }

    /// Returns the total amount of bytes representing the listpack.
    ///
    /// # Example
    ///
    /// ```
    /// use listpack_redis::Listpack;
    ///
    /// let listpack: Listpack = Listpack::default();
    /// let header = unsafe { listpack.get_header_ref() };
    /// // The header is 6 bytes long, one more byte is the terminator.
    /// assert_eq!(header.total_bytes(), 7);
    pub fn total_bytes(&self) -> usize {
        self.total_bytes as usize
    }

    /// Returns the total number of elements the listpack holds.
    ///
    /// # Example
    ///
    /// ```
    /// use listpack_redis::Listpack;
    ///
    /// let listpack: Listpack = Listpack::default();
    /// let header = unsafe { listpack.get_header_ref() };
    /// assert_eq!(header.num_elements(), 0);
    ///
    /// let listpack: Listpack = Listpack::from(&[1, 2, 3]);
    /// let header = unsafe { listpack.get_header_ref() };
    /// assert_eq!(header.num_elements(), 3);
    pub fn num_elements(&self) -> usize {
        self.num_elements as usize
    }

    /// Returns the amount of bytes available for the listpack to store
    /// new elements. This is the maximum size of the allocation minus
    /// the size of the header and the end marker and the existing
    /// elements.
    pub fn available_bytes(&self) -> usize {
        Self::MAXIMUM_TOTAL_BYTES - self.total_bytes()
    }

    /// Returns the number of bytes the elements occupy in the listpack,
    /// that is available right after the header. This is the number of
    /// bytes in the allocation without the header and the end marker.
    pub fn element_bytes(&self) -> usize {
        self.total_bytes()
            - std::mem::size_of::<ListpackHeader>()
            - std::mem::size_of_val(&END_MARKER)
    }

    /// Sets the new total amount of bytes representing the listpack.
    pub fn set_total_bytes(&mut self, total_bytes: u32) {
        self.total_bytes = total_bytes;
    }

    /// Sets the new total number of elements the listpack holds.
    pub fn set_num_elements(&mut self, num_elements: u16) {
        self.num_elements = num_elements;
    }
}

/// A reference to the header of the listpack data structure.
///
/// The header reference is a special kind of object (header) that is
/// located at the beginning of the listpack and is used to access the
/// listpack in a safe way. That means, it is basically a listpack
/// itself.
///
/// A listpack reference is always a reference to a valid listpack
/// header. It can be obtained using [`Listpack::header_ref`] method.
///
/// The header reference is a transparent wrapper around the header
/// object ([`ListpackHeader`]).
#[repr(transparent)]
#[derive(Debug, Copy, Clone)]
pub struct ListpackHeaderRef<'a>(&'a ListpackHeader);

impl AsRef<ListpackHeader> for ListpackHeaderRef<'_> {
    fn as_ref(&self) -> &ListpackHeader {
        self.0
    }
}

impl ListpackHeaderRef<'_> {
    /// Returns the total amount of bytes representing the listpack.
    ///
    /// See [`ListpackHeader::total_bytes`].
    pub fn total_bytes(&self) -> usize {
        self.0.total_bytes as usize
    }

    /// Returns the number of bytes the elements occupy in the listpack,
    /// that is available right after the header.
    pub fn element_bytes(&self) -> usize {
        self.total_bytes()
            - std::mem::size_of::<ListpackHeader>()
            - std::mem::size_of_val(&END_MARKER)
    }

    /// Returns the total number of elements the listpack holds.
    ///
    /// See [`ListpackHeader::num_elements`].
    pub fn num_elements(&self) -> usize {
        self.0.num_elements as usize
    }

    /// Returns the amount of bytes available for the listpack to store
    /// new elements.
    ///
    /// See [`ListpackHeader::available_bytes`].
    pub fn available_bytes(&self) -> usize {
        self.0.available_bytes()
    }
}

/// A pointer to the allocation of the listpack. It will contain the
/// header, the data block (including the elements), and the end marker.
///
/// This is simply a container of a pointer to the listpack data, and
/// the pointer will never be automatically deallocated by
/// the [`ListpackAllocationPointer`] itself, it is the responsibility
/// of the user who allocated the memory to deallocate it.
#[repr(transparent)]
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
struct ListpackAllocationPointer(NonNull<u8>);

impl ListpackAllocationPointer {
    /// Finds out the layout of the listpack by looking for the end
    /// marker.
    fn from_owned_ptr(ptr: NonNull<[u8]>) -> Result<Self> {
        if unsafe { ptr.as_ref() }.last() != Some(&END_MARKER) {
            return Err(crate::error::Error::MissingEndMarker);
        }

        Ok(Self(ptr.cast()))
    }

    /// Creates a listpack allocation pointer from a raw pointer. The
    /// function will return an error if the pointer does not contain a
    /// valid listpack.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the pointer is valid.
    unsafe fn from_owned_raw_ptr(ptr: NonNull<u8>) -> Result<Self> {
        Self::from_owned_ptr(Self::ptr_as_slice(ptr))
    }

    /// Creates a listpack allocation pointer from a borrowed pointer.
    /// The pointer is tagged as borrowed.
    pub fn from_borrowed_ptr(ptr: NonNull<[u8]>) -> Result<Self> {
        if unsafe { ptr.as_ref() }.last() != Some(&END_MARKER) {
            return Err(crate::error::Error::MissingEndMarker);
        }

        let ptr: NonNull<u8> = ptr.cast();

        Ok(Self(ptr.tag(AllocationPointerTag::Borrowed)))
    }

    /// Creates a lsitpack allocation pointer from a raw borrowed
    /// pointer. The function will return an error if the pointer does
    /// not contain a valid listpack.
    ///
    /// # Safety
    ///
    /// 1. The user must ensure that the pointer is valid throughout the
    /// lifetime of the returned object.
    /// 2. The user must deallocate the provided pointer manually, as
    /// the returned object does not own the memory and will not
    /// deallocate the memory referred to by the provided pointer.
    unsafe fn from_borrowed_raw_ptr(ptr: NonNull<u8>) -> Result<Self> {
        Self::from_borrowed_ptr(Self::ptr_as_slice(ptr))
    }

    /// Converts a pointer to a slice pointer.
    fn ptr_as_slice(ptr: NonNull<u8>) -> NonNull<[u8]> {
        let header = unsafe { ListpackHeader::from_ptr(ptr.as_ptr().cast()) };
        let total_bytes = header.total_bytes as usize;

        unsafe {
            NonNull::new_unchecked(std::ptr::slice_from_raw_parts_mut(
                ptr.as_ptr(),
                total_bytes,
            ))
        }
    }

    /// Returns [`true`] if the pointer is tagged as borrowed, meaning
    /// the data allocated and referred to by the pointer is not owned
    /// by the pointer itself.
    pub fn is_borrowed(&self) -> bool {
        self.0.get_tag() == Some(AllocationPointerTag::Borrowed)
    }

    /// Returns [`true`] if the pointer is tagged as owned, meaning the
    /// data allocated and referred to by the pointer is owned by the
    /// pointer itself.
    pub fn is_owned(&self) -> bool {
        !self.is_borrowed()
    }

    /// Returns the pointer to the beginning of the data.
    fn ptr(&self) -> NonNull<u8> {
        // if self.is_owned() {
        //     self.0.cast()
        // } else {
        //     <NonNull<u8> as Taggable<AllocationPointerTag>>::remove_tag(&self.0).cast()
        // }
        <NonNull<u8> as Taggable<AllocationPointerTag>>::remove_tag(&self.0).cast()
    }

    /// Returns the length of the listpack accessible by the pointer.
    fn get_length(&self) -> usize {
        unsafe { ListpackHeader::from_ptr(self.ptr().as_ptr().cast_const()) }.total_bytes()
    }

    fn layout(&self) -> Layout {
        Layout::from_size_align(self.get_length(), 1).expect("Could not create layout")
    }

    /// Returns a pointer to a slice of bytes.
    pub fn as_slice_raw_ptr(&self) -> *mut [u8] {
        let ptr = self.ptr().as_ptr();
        let length = self.get_length();

        std::ptr::slice_from_raw_parts_mut(ptr, length)
    }

    /// Returns a pointer to a slice of bytes as a NonNull pointer.
    pub fn as_slice_ptr(&self) -> NonNull<[u8]> {
        unsafe { NonNull::new_unchecked(self.as_slice_raw_ptr()) }
    }

    /// Returns a slice of bytes.
    pub fn as_slice(&self) -> &[u8] {
        unsafe { &*self.as_slice_raw_ptr() }
    }

    /// Returns a pointer to the beginning of the data.
    fn data_start_ptr(&self) -> *const u8 {
        unsafe {
            self.ptr()
                .as_ptr()
                .add(std::mem::size_of::<ListpackHeader>())
        }
    }

    fn data_start_slice(&self) -> &[u8] {
        &self.as_slice()[std::mem::size_of::<ListpackHeader>()..]
    }

    /// Returns a pointer pointing to the end marker.
    fn data_end_ptr(&self) -> *const u8 {
        unsafe { self.ptr().as_ptr().add(self.total_bytes() - 1) }
    }

    /// Sets the last byte of the listpack to the end marker.
    fn set_end_marker(&mut self) {
        unsafe {
            *self.data_end_ptr().cast_mut() = END_MARKER;
        }
    }

    fn get_header(&self) -> &ListpackHeader {
        unsafe {
            self.ptr()
                .as_ptr()
                .cast::<ListpackHeader>()
                .as_ref()
                .unwrap()
        }
    }

    fn get_header_mut(&mut self) -> &mut ListpackHeader {
        unsafe {
            self.ptr()
                .as_ptr()
                .cast::<ListpackHeader>()
                .as_mut()
                .unwrap()
        }
    }

    /// Sets a new size.
    ///
    /// # Safety
    ///
    /// The user of this function must ensure that the new size is
    /// correct.
    unsafe fn set_new_size(&mut self, size: usize) {
        self.get_header_mut().set_total_bytes(size as u32);
        self.set_end_marker();
    }
}

impl Deref for ListpackAllocationPointer {
    type Target = ListpackHeader;

    fn deref(&self) -> &Self::Target {
        self.get_header()
    }
}

impl DerefMut for ListpackAllocationPointer {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.get_header_mut()
    }
}

/// Represents the capacity of the listpack. The capacity is the number
/// of bytes the listpack is allowed to use for storing elements,
/// excluding the extra memory costs related to the header and the end
/// marker, or any other data stored but unrelated to the elements.
#[derive(Debug, Copy, Clone, Eq, PartialEq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct ListpackCapacity(usize);

impl ListpackCapacity {
    /// The zero capacity of the listpack, which is the same as the
    /// minimum capacity, which includes the header and the end marker.
    const ZERO: Self = Self::MINIMUM_CAPACITY;
    /// The minimum capacity of the listpack, which is the size of the
    /// header and the end marker.
    const MINIMUM_CAPACITY: Self =
        Self(std::mem::size_of::<ListpackHeader>() + std::mem::size_of::<u8>());
}

impl TryFrom<usize> for ListpackCapacity {
    type Error = crate::error::Error;

    fn try_from(value: usize) -> Result<Self> {
        if value > ListpackHeader::MAXIMUM_ELEMENT_BYTES {
            return Err(AllocationError::ListpackIsTooBig {
                size: value,
                max_size: ListpackHeader::MAXIMUM_TOTAL_BYTES,
            }
            .into());
        }

        Ok(Self(value + Self::MINIMUM_CAPACITY.0))
    }
}

/// The listpack data structure.
pub struct Listpack<Allocator: CustomAllocator = crate::allocator::DefaultAllocator> {
    allocation: ListpackAllocationPointer,
    allocator: Allocator,
}

impl<Allocator> Default for Listpack<Allocator>
where
    Allocator: ListpackAllocator,
    <Allocator as CustomAllocator>::Error: Debug,
{
    fn default() -> Self {
        Self::with_capacity(0)
    }
}

impl<Allocator> Hash for Listpack<Allocator>
where
    Allocator: CustomAllocator,
{
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.allocation.hash(state);
    }
}

impl<Allocator> Debug for Listpack<Allocator>
where
    Allocator: CustomAllocator + Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Listpack")
            .field("allocation", &self.allocation)
            // TODO: optimise to not use collection to vector.
            .field("elements", &self.iter().collect::<Vec<_>>())
            .field("allocator", &self.allocator)
            .finish()
    }
}

impl<Allocator> std::fmt::Display for Listpack<Allocator>
where
    Allocator: CustomAllocator,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_char('[')?;

        for (i, element) in self.iter().enumerate() {
            f.write_str(&element.to_string())?;

            if i < self.len() - 1 {
                f.write_str(", ")?;
            }
        }

        f.write_char(']')
    }
}

impl<Allocator> Drop for Listpack<Allocator>
where
    Allocator: CustomAllocator,
{
    fn drop(&mut self) {
        // If the pointer this listpack object was created from is
        // owned by the allocator, deallocate the memory. If it is not
        // owned, the allocator should not deallocate the memory.

        if self.allocation.is_owned() {
            unsafe {
                self.allocator
                    .deallocate(self.allocation.ptr(), self.allocation.layout())
            }
        }
    }
}

impl<Allocator> Clone for Listpack<Allocator>
where
    Allocator: ListpackAllocator,
    <Allocator as CustomAllocator>::Error: Debug,
{
    fn clone(&self) -> Self {
        let mut cloned = Self::with_capacity_and_allocator(
            self.get_header_ref().element_bytes(),
            self.allocator.clone(),
        );

        unsafe {
            std::ptr::copy_nonoverlapping(
                self.as_ptr(),
                cloned.as_mut_ptr().cast(),
                self.allocation.layout().size(),
            );
        }

        cloned
    }
}

impl<Allocator> PartialEq for Listpack<Allocator>
where
    Allocator: CustomAllocator,
{
    fn eq(&self, other: &Self) -> bool {
        self.iter().eq(other.iter())
    }
}

impl<Allocator> Eq for Listpack<Allocator> where Allocator: CustomAllocator {}

/// Comparing a listpack against a slice of insertable entries.
///
/// # Example
///
/// ```
/// use listpack_redis::{Listpack, ListpackEntryInsert};
///
/// let array = ["Hello", "World"];
///
/// let listpack: Listpack = Listpack::from(&["Hello", "World"]);
/// assert_eq!(listpack, &array);
/// ```
impl<'a, T, Allocator> PartialEq<&'a [T]> for Listpack<Allocator>
where
    ListpackEntryInsert<'a>: std::convert::From<&'a T>,
    Allocator: CustomAllocator,
{
    fn eq(&self, other: &&'a [T]) -> bool {
        for (a, b) in self.iter().zip(other.iter()) {
            let b = ListpackEntryInsert::from(b);
            if a != b {
                return false;
            }
        }

        true
    }
}

/// Comparing a listpack against a slice of insertable entries, but
/// of static length.
///
/// # Example
///
/// ```
/// use listpack_redis::{Listpack, ListpackEntryInsert};
///
/// let listpack: Listpack = Listpack::from(&["Hello", "World"]);
/// assert_eq!(listpack, &["Hello", "World"]);
/// ```
impl<'a, T, const N: usize, Allocator> PartialEq<&'a [T; N]> for Listpack<Allocator>
where
    &'a T: Into<ListpackEntryInsert<'a>>,
    ListpackEntryInsert<'a>: std::convert::From<&'a T>,
    Allocator: CustomAllocator,
{
    fn eq(&self, other: &&'a [T; N]) -> bool {
        self.eq(&other.as_slice())
    }
}

impl<'a, T, Allocator> From<&'a [T]> for Listpack<Allocator>
where
    &'a T: Into<ListpackEntryInsert<'a>>,
    ListpackEntryInsert<'a>: std::convert::From<&'a T>,
    Allocator: ListpackAllocator,
    <Allocator as CustomAllocator>::Error: Debug,
{
    fn from(slice: &'a [T]) -> Self {
        let items = slice
            .iter()
            .map(ListpackEntryInsert::from)
            .collect::<Vec<_>>();
        let elements_size: usize = items
            .iter()
            .map(ListpackEntryInsert::full_encoded_size)
            .sum();
        let mut listpack = Listpack::with_capacity(elements_size);
        let ptr = listpack.allocation.data_start_ptr();

        let encoded: Vec<u8> = items
            .iter()
            .flat_map(|item| item.try_encode().expect("Encoded value"))
            .collect();

        unsafe {
            std::ptr::copy_nonoverlapping(encoded.as_ptr(), ptr.cast_mut(), encoded.len());
        }

        listpack.set_num_elements(slice.len() as u16);

        listpack
    }
}

impl<'a, T, const N: usize, Allocator> From<&'a [T; N]> for Listpack<Allocator>
where
    &'a T: Into<ListpackEntryInsert<'a>>,
    ListpackEntryInsert<'a>: std::convert::From<&'a T>,
    Allocator: ListpackAllocator,
    <Allocator as CustomAllocator>::Error: Debug,
{
    fn from(slice: &'a [T; N]) -> Self {
        let items = slice
            .iter()
            .map(ListpackEntryInsert::from)
            .collect::<Vec<_>>();

        let elements_size: usize = items
            .iter()
            .map(ListpackEntryInsert::full_encoded_size)
            .sum();

        let mut listpack = Listpack::with_capacity(elements_size);
        let ptr = listpack.allocation.data_start_ptr();

        let encoded: Vec<u8> = items
            .iter()
            .flat_map(|item| item.try_encode().expect("Encoded value"))
            .collect();

        unsafe {
            std::ptr::copy_nonoverlapping(encoded.as_ptr(), ptr.cast_mut(), encoded.len());
        }

        listpack.set_num_elements(N as u16);
        listpack
    }
}

/// Allows to create a listpack from an iterator of insertable entries.
///
/// # Example
///
/// ```
/// use listpack_redis::Listpack;
///
/// let listpack: Listpack = vec!["Hello", "World"].into_iter().collect();
/// assert_eq!(listpack, &["Hello", "World"]);
///
/// let listpack: Listpack = (0..10).collect();
/// assert_eq!(listpack.len(), 10);
/// assert_eq!(listpack, &[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]);
/// ```
impl<'a, T, Allocator> FromIterator<T> for Listpack<Allocator>
where
    ListpackEntryInsert<'a>: From<T>,
    Allocator: ListpackAllocator,
    <Allocator as CustomAllocator>::Error: Debug,
{
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let items = iter
            .into_iter()
            .map(ListpackEntryInsert::from)
            .collect::<Vec<_>>();
        let elements_size: usize = items
            .iter()
            .map(ListpackEntryInsert::full_encoded_size)
            .sum();
        let items_len = items.len();

        let mut listpack = Listpack::with_capacity(elements_size);
        let ptr = listpack.allocation.data_start_ptr();

        let encoded: Vec<u8> = items
            .iter()
            .flat_map(|item| item.try_encode().expect("Encoded value"))
            .collect();

        unsafe {
            std::ptr::copy_nonoverlapping(encoded.as_ptr(), ptr.cast_mut(), encoded.len());
        }

        listpack.set_num_elements(items_len as u16);
        listpack
    }
}

impl<Allocator> MemoryConsumption for Listpack<Allocator>
where
    Allocator: CustomAllocator,
{
    fn memory_consumption(&self) -> usize {
        self.allocation.layout().size() + std::mem::size_of::<Self>()
    }
}

/// The methods which do not require any additional constraints on the
/// allocator.
impl<Allocator> Listpack<Allocator>
where
    Allocator: CustomAllocator,
{
    /// Returns `true` if the listpack is homogeneous, that is, all the
    /// elements have the same type. The type is meant to be the
    /// encoding type of the elements. That said, there is a difference
    /// between the small strings, large strings, and integers, and the
    /// other types, as the [`ListpackEntryEncodingType::SmallString`]
    /// and [`ListpackEntryEncodingType::LargeString`] are considered
    /// to be of different types, while the actual data they store is
    /// the same (still a string).
    ///
    /// In case the listpack is empty, it is considered homogeneous.
    ///
    /// # Example
    ///
    /// ```
    /// use listpack_redis::Listpack;
    ///
    /// let mut listpack: Listpack = Listpack::default();
    /// assert!(listpack.is_homogeneous());
    ///
    /// listpack.push("Hello");
    /// listpack.push("World");
    /// assert!(listpack.is_homogeneous());
    ///
    /// listpack.push(1);
    /// assert!(!listpack.is_homogeneous());
    /// ```
    ///
    /// To know the types of the elements, use the
    /// [`Listpack::get_element_types`] method.
    pub fn is_homogeneous(&self) -> bool {
        if self.is_empty() {
            return true;
        }

        let mut iter = self.iter();
        let first = iter.next().map(|e| e.encoding_type().unwrap()).unwrap();

        iter.all(|e| e.encoding_type().unwrap() == first)
    }

    /// Returns a reference to the listpack located at the beginning of
    /// the provided pointer. The pointer must point exactly to the
    /// listpack's data: the header, the elements, and the end marker.
    ///
    /// The allocator must be provided to the listpack, as it is used
    /// to deallocate the listpack when it is dropped.
    ///
    /// Creating a Listpack object from this function is cheap: there
    /// are no allocations made except for the pointer and the
    /// allocator: the pointer to the listpack provided as an argument
    /// to this method will **NOT** be owned by the returned
    /// [`Listpack`] object, but will be used for reading. So the user
    /// is responsible for deallocating the memory pointed to by the
    /// provided pointer. Once the returned [`Listpack`] object needs to
    /// allocate more memory, it will use the allocator provided to the
    /// function to allocate another memory block, which **will be**
    /// owned by the returning object. When the listpack is dropped, the
    /// allocator will deallocate the memory.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the pointer is valid.
    pub unsafe fn from_ptr(ptr: *const u8, allocator: Allocator) -> Self {
        let allocation = ListpackAllocationPointer::from_borrowed_raw_ptr(NonNull::new_unchecked(
            ptr.cast_mut(),
        ))
        .expect("The listpack is valid.");

        Self {
            allocation,
            allocator,
        }
    }

    /// Returns the encoding types of the elements of the listpack.
    ///
    /// # Example
    ///
    /// ```
    /// use listpack_redis::{Listpack, ListpackEntryEncodingType};
    ///
    /// let mut listpack: Listpack = Listpack::default();
    /// listpack.push("Hello");
    /// listpack.push(1);
    ///
    /// let types = listpack.get_element_types();
    /// assert_eq!(types, vec![ListpackEntryEncodingType::SmallString, ListpackEntryEncodingType::SmallUnsignedInteger]);
    /// ```
    pub fn get_element_types(&self) -> Vec<ListpackEntryEncodingType> {
        self.iter().map(|e| e.encoding_type().unwrap()).collect()
    }

    /// Returns a vector of elements of the listpack. The elements are
    /// converted to the type `T` using the [`From`] trait.
    /// If the listpack is not homogeneous, returns [`None`].
    ///
    /// # Example
    ///
    /// ```
    /// use listpack_redis::Listpack;
    ///
    /// let mut listpack: Listpack = Listpack::default();
    /// listpack.push("Hello");
    /// listpack.push("World");
    ///
    /// let vec: Vec<String> = listpack.get_homogenous_vec().unwrap();
    /// assert_eq!(vec, vec!["Hello", "World"]);
    ///
    /// listpack.push(1);
    /// assert!(listpack.get_homogenous_vec::<String>().is_err());
    /// ```
    pub fn get_homogenous_vec<'a, T>(&'a self) -> Result<Vec<T>, T::Error>
    where
        T: TryFrom<&'a ListpackEntryRef>,
    {
        self.iter().map(T::try_from).collect::<Result<_, _>>()
    }

    /// Returns the allocator of the listpack.
    pub fn get_allocator(&self) -> &Allocator {
        &self.allocator
    }

    /// Returns a mutable reference to the allocator of the listpack.
    pub fn get_allocator_mut(&mut self) -> &mut Allocator {
        &mut self.allocator
    }

    /// Returns a raw pointer to the listpack data (starting from the
    /// header). The returned pointer is never null.
    ///
    /// # Example
    ///
    /// ```
    /// use listpack_redis::Listpack;
    ///
    /// let listpack: Listpack = Listpack::default();
    /// let ptr = listpack.as_ptr();
    /// assert!(!ptr.is_null());
    /// ```
    pub fn as_ptr(&self) -> *const u8 {
        self.allocation.ptr().as_ptr().cast()
    }

    /// Returns a mutable raw pointer to the listpack. The returned
    /// pointer is never null.
    ///
    /// # Example
    ///
    /// ```
    /// use listpack_redis::Listpack;
    ///
    /// let mut listpack: Listpack = Listpack::default();
    /// let ptr = listpack.as_mut_ptr();
    /// assert!(!ptr.is_null());
    /// ```
    pub fn as_mut_ptr(&mut self) -> *mut [u8] {
        self.allocation.as_slice_raw_ptr()
    }

    /// Returns a mutable reference to the listpack header.
    pub fn get_header_mut(&mut self) -> &mut ListpackHeader {
        unsafe {
            self.allocation
                .0
                .as_ptr()
                .cast::<ListpackHeader>()
                .as_mut()
                .unwrap()
        }
    }

    /// Returns the number of elements of this listpack.
    ///
    /// # Example
    ///
    /// ```
    /// use listpack_redis::Listpack;
    ///
    /// let mut listpack: Listpack = Listpack::default();
    /// listpack.push("Hello, world!");
    /// assert_eq!(listpack.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        self.get_header_ref().num_elements()
    }

    /// Returns the length of the listpack, describing how many elements
    /// are currently in this listpack.
    ///
    /// # Example
    ///
    /// ```
    /// use listpack_redis::Listpack;
    ///
    /// let mut listpack: Listpack = Listpack::default();
    /// listpack.push("Hello, world!");
    /// assert!(!listpack.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// An unsafe way to obtain an immutable reference to the listpack
    /// header.
    ///
    /// # Panics
    ///
    /// Panics if the header is not valid.
    ///
    /// # Example
    ///
    /// ```
    /// use listpack_redis::Listpack;
    ///
    /// let mut listpack: Listpack = Listpack::default();
    /// let header = unsafe { listpack.get_header_ref() };
    /// assert_eq!(header.num_elements(), 0);
    ///
    /// listpack.push(1);
    /// let header = unsafe { listpack.get_header_ref() };
    /// assert_eq!(header.num_elements(), 1);
    /// ```
    pub fn get_header_ref(&self) -> &ListpackHeader {
        // &*(self.ptr.as_ptr() as *const ListpackHeader)
        unsafe {
            (self.as_ptr() as *const ListpackHeader)
                .as_ref()
                .expect("Header is valid")
        }
    }

    /// Creates a new listpack from the given raw pointer.
    ///
    /// # Safety
    ///
    /// 1. The caller must ensure that the pointer is valid.
    /// 2. Since there is no way to track the pointer returned by the
    ///    [`Listpack::as_ptr`] method, the caller must ensure that the
    ///    pointer is not used after the listpack is dropped, and that
    ///    the listpack this pointer was taken from **is** dropped if
    ///    another listpack is created from the same pointer, using
    ///    [`Listpack::from_raw_parts`], as in the example.
    ///
    /// # Example
    ///
    /// ```
    /// use listpack_redis::Listpack;
    /// use std::ptr::NonNull;
    ///
    /// let mut old: Listpack = Listpack::default();
    /// old.push("Hello, world!");
    /// let ptr = unsafe { NonNull::new_unchecked(old.as_mut_ptr()) };
    /// let new: Listpack = unsafe { Listpack::from_raw_parts(ptr, old.get_allocator().clone()) };
    /// assert_eq!(old.get(0), new.get(0));
    ///
    /// // The old listpack is forgotten so that there is no
    /// // double-free.
    /// std::mem::forget(old);
    /// ```
    pub unsafe fn from_raw_parts(ptr: NonNull<[u8]>, allocator: Allocator) -> Self {
        let allocation =
            ListpackAllocationPointer::from_owned_ptr(ptr).expect("The listpack is valid.");

        Self {
            allocation,
            allocator,
        }
    }

    /// Checks that the passed element can be inserted into the
    /// listpack. In case it cannot, returns the corresponding error.
    ///
    /// Optionally it is possible to specify an index of an object which
    /// will be replaced by the new one. Without this parameter, the
    /// method will check if the listpack can fit the new element
    /// without replacing any of the existing ones.
    ///
    /// When it is possible to fit an entry passed, the amount of bytes
    /// required to store the entry is returned. By this amount of bytes
    /// the listpack must be extended prior to the insertion. Otherwise,
    /// if the element to be replaced is bigger than the new one, the
    /// listpack does not need to be extended and needs to be shrinked,
    /// by the amount of bytes returned (negative).
    ///
    /// # Example
    ///
    /// ```
    /// use listpack_redis::Listpack;
    ///
    /// let mut listpack: Listpack = Listpack::default();
    ///
    /// let entry = "Hello, world!".into();
    /// let check = listpack.can_fit_entry(&entry, None);
    /// assert!(check.is_ok());
    ///
    /// // The string is too long to be stored in the listpack.
    /// let string = "a".repeat(2usize.pow(32).into());
    /// let entry = (&string).into();
    /// let check = listpack.can_fit_entry(&entry, None);
    /// assert!(check.is_err());
    /// ```
    pub fn can_fit_entry(
        &self,
        entry: &ListpackEntryInsert,
        entry_to_replace: Option<&ListpackEntryRef>,
    ) -> Result<FittingRequirement> {
        let object_to_replace_size = entry_to_replace
            .map(|e| e.total_bytes())
            .unwrap_or_default();

        let available_listpack_length =
            self.get_header_ref().available_bytes() + object_to_replace_size;

        let encoded_size = entry.full_encoded_size();

        if encoded_size > available_listpack_length {
            return Err(crate::error::InsertionError::ListpackIsFull {
                current_length: encoded_size,
                available_listpack_length,
            }
            .into());
        }

        if let ListpackEntryInsert::String(s) = entry {
            if s.is_empty() {
                return Err(crate::error::InsertionError::StringIsEmpty.into());
            }
        }

        Ok(FittingRequirement::from_difference(
            encoded_size,
            object_to_replace_size,
        ))
    }

    /// Returns the first element of the listpack, or [`None`] if it is
    /// empty.
    pub fn first(&self) -> Option<&ListpackEntryRef> {
        self.get(0)
    }

    /// Returns the last element of the listpack, or [`None`] if it is
    /// empty.
    pub fn last(&self) -> Option<&ListpackEntryRef> {
        self.get(self.len() - 1)
    }

    /// Swaps two elements in the listpack.
    ///
    /// # Panics
    ///
    /// Panics if either `a` or `b` are out of bounds.
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
    ///
    /// listpack.swap(0, 2);
    ///
    /// assert_eq!(listpack.len(), 3);
    /// assert_eq!(listpack[0].to_string(), "!");
    /// assert_eq!(listpack[1].to_string(), "World");
    /// assert_eq!(listpack[2].to_string(), "Hello");
    /// ```
    pub fn swap(&mut self, a: usize, b: usize) {
        let range = 0..self.len();

        if !range.contains(&a) || !range.contains(&b) {
            panic!("The index is out of bounds.");
        }

        unsafe { self.swap_unchecked(a, b) }
    }

    /// Swaps two elements in the listpack without doing any bounds
    /// checking.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the indexes are not out of bounds.
    ///
    /// # Example
    ///
    /// ```
    /// use listpack_redis::Listpack;
    ///
    /// let mut listpack: Listpack = Listpack::default();
    ///
    /// listpack.push("Hello");
    /// listpack.push("World!");
    ///
    /// unsafe { listpack.swap_unchecked(0, 1) };
    ///
    /// assert_eq!(listpack.len(), 2);
    ///
    /// assert_eq!(listpack[0].to_string(), "World!");
    /// assert_eq!(listpack[1].to_string(), "Hello");
    /// ```
    pub unsafe fn swap_unchecked(&mut self, a: usize, b: usize) {
        if a == b {
            return;
        }

        // Instead of calling the replace method, we can directly
        // replace the elements in the listpack. This is more
        // efficient, because we do not need to check if the listpack
        // can fit the new element, since we are just swapping the
        // elements, and we don't need to reallocate twice.

        let a_entry = self.get(a).expect("Get an entry from listpack");
        let b_entry = self.get(b).expect("Get an entry from listpack");

        if a_entry.total_bytes() == b_entry.total_bytes() {
            a_entry
                .as_slice_mut()
                .swap_with_slice(b_entry.as_slice_mut());
        } else {
            let ((smaller, smaller_initial_offset), (bigger, bigger_initial_offset)) = {
                let a_encoded = a_entry.as_slice();
                let b_encoded = b_entry.as_slice();

                // Casting to usize is safe since the elements are always
                // father that the listpack start.
                let a_offset = a_entry
                    .as_ptr()
                    .offset_from(self.allocation.data_start_ptr())
                    as usize;

                let b_offset = b_entry
                    .as_ptr()
                    .offset_from(self.allocation.data_start_ptr())
                    as usize;

                if a_encoded.len() < b_encoded.len() {
                    (
                        (a_encoded.to_owned(), a_offset),
                        (b_encoded.to_owned(), b_offset),
                    )
                } else {
                    (
                        (b_encoded.to_owned(), b_offset),
                        (a_encoded.to_owned(), a_offset),
                    )
                }
            };

            let data_start_ptr = self.allocation.data_start_ptr();

            let length_difference = bigger.len() - smaller.len();

            // Shift the elements to the left or to the right by the
            // amount of the difference between the bigger and the
            // smaller element. This is based on the initial offset of the elements to swap.
            if smaller_initial_offset > bigger_initial_offset {
                // Move the smaller element to the bigger element's
                // place.
                std::ptr::copy_nonoverlapping(
                    smaller.as_ptr(),
                    data_start_ptr.add(bigger_initial_offset).cast_mut(),
                    smaller.len(),
                );

                // Here as the smallest element should be on the left,
                // (should be copied into the bigger one's place), so
                // we should move all the elements after it until the
                // element-to-swap-with inclusively, to the left, by
                // the difference between the lengths of those.
                let count_to_move =
                    smaller_initial_offset - bigger_initial_offset - length_difference;

                std::ptr::copy(
                    data_start_ptr.add(bigger_initial_offset + bigger.len()),
                    data_start_ptr
                        .add(bigger_initial_offset + smaller.len())
                        .cast_mut(),
                    count_to_move,
                );

                // Move the bigger element to the smaller element's place.
                std::ptr::copy_nonoverlapping(
                    bigger.as_ptr(),
                    // data_start_ptr.add(bigger_initial_offset - difference).cast_mut(),
                    data_start_ptr
                        .add(smaller_initial_offset - length_difference)
                        .cast_mut(),
                    bigger.len(),
                );
            } else {
                // Move the smaller element to the bigger element's place,
                // but not to the start of it, but to the end (backwards).
                std::ptr::copy_nonoverlapping(
                    smaller.as_ptr(),
                    data_start_ptr
                        .add(bigger_initial_offset + bigger.len() - smaller.len())
                        .cast_mut(),
                    smaller.len(),
                );

                // Move the in-between elements to the right.
                let count_to_move = bigger_initial_offset - smaller_initial_offset - smaller.len();

                for i in (0..count_to_move).rev() {
                    let source = data_start_ptr.add(smaller_initial_offset + smaller.len() + i);
                    let destination = data_start_ptr.add(smaller_initial_offset + bigger.len() + i);
                    std::ptr::copy_nonoverlapping(source, destination.cast_mut(), 1);
                }

                // Move the bigger element to the smaller element's place.
                std::ptr::copy_nonoverlapping(
                    bigger.as_ptr(),
                    // data_start_ptr.add(bigger_initial_offset - difference).cast_mut(),
                    data_start_ptr.add(smaller_initial_offset).cast_mut(),
                    bigger.len(),
                );
            }
        }
    }

    /// Returns an iterator over all contiguous windows of length
    /// `size`. The windows overlap. If the listpack is shorter than
    /// `size`, the iterator returns no values.
    ///
    /// # Panics
    ///
    /// Panics if the size is zero.
    ///
    /// See [`ListpackWindows`] for more information.
    pub fn windows(&self, size: usize) -> ListpackWindows<Allocator> {
        if size == 0 {
            panic!("The size must be greater than zero.");
        }

        ListpackWindows {
            listpack: self,
            size,
            index: 0,
        }
    }

    /// Returns an iterator over all contiguous windows of length
    /// `size`. The windows overlap. If the listpack is shorter than
    /// `size`, the iterator returns no values.
    ///
    /// # Panics
    ///
    /// Panics if the size is zero.
    ///
    /// See [`ListpackChunks`] for more information.
    pub fn chunks(&self, size: usize) -> ListpackChunks<Allocator> {
        if size == 0 {
            panic!("The size must be greater than zero.");
        }

        ListpackChunks {
            listpack: self,
            size,
            index: 0,
        }
    }

    /// Returns `true` if the listpack contains an element with the
    /// given value.
    ///
    /// # Example
    ///
    /// ```
    /// use listpack_redis::Listpack;
    ///
    /// let mut listpack: Listpack = Listpack::default();
    /// listpack.push("Hello");
    /// listpack.push("World");
    /// assert!(listpack.contains("Hello"));
    /// assert!(listpack.contains("World"));
    /// assert!(!listpack.contains("Hello, world!"));
    /// assert!(!listpack.contains(2));
    /// ```
    pub fn contains<'a, T: Into<ListpackEntryInsert<'a>>>(&self, object: T) -> bool {
        let object = object.into();

        self.iter().any(|entry| -> bool {
            if let Ok(data) = entry.data() {
                if let Some(string) = data.get_str() {
                    ListpackEntryInsert::String(string) == object
                } else if let Some(integer) = data.get_i64() {
                    ListpackEntryInsert::Integer(integer) == object
                } else {
                    false
                }
            } else {
                false
            }
        })
    }

    /// Returns `true` if the listpack begins with the elements of the
    /// given prefix.
    ///
    /// # Example
    ///
    /// ```
    /// use listpack_redis::Listpack;
    ///
    /// let mut listpack: Listpack = Listpack::default();
    /// listpack.push("Hello");
    /// listpack.push("World");
    /// assert!(listpack.starts_with(&["Hello"]));
    /// assert!(listpack.starts_with(&["Hello", "World"]));
    /// assert!(!listpack.starts_with(&["Hello", "World", "!"]));
    /// ```
    pub fn starts_with<'a, T>(&self, prefix: &'a [T]) -> bool
    where
        ListpackEntryInsert<'a>: std::convert::From<&'a T>,
    {
        if prefix.len() > self.len() {
            return false;
        }

        self.iter()
            .zip(
                prefix
                    .iter()
                    .map(ListpackEntryInsert::from)
                    .take(self.len()),
            )
            .filter_map(|(entry, prefix)| Some((entry.data().ok()?, prefix)))
            .all(|(data, object)| {
                if let Some(string) = data.get_str() {
                    ListpackEntryInsert::String(string) == object
                } else if let Some(integer) = data.get_i64() {
                    ListpackEntryInsert::Integer(integer) == object
                } else {
                    false
                }
            })
    }

    /// Returns `true` if the listpack ends with the elements of the
    /// given suffix.
    ///
    /// # Example
    ///
    /// ```
    /// use listpack_redis::Listpack;
    ///
    /// let mut listpack: Listpack = Listpack::default();
    /// listpack.push("Hello");
    /// listpack.push("World");
    /// assert!(listpack.ends_with(&["World"]));
    /// assert!(listpack.ends_with(&["Hello", "World"]));
    /// assert!(!listpack.ends_with(&["Hello", "World", "!"]));
    /// ```
    pub fn ends_with<'a, T>(&self, suffix: &'a [T]) -> bool
    where
        ListpackEntryInsert<'a>: std::convert::From<&'a T>,
    {
        if suffix.len() > self.len() {
            return false;
        }

        self.iter()
            .rev()
            .zip(
                suffix
                    .iter()
                    .map(ListpackEntryInsert::from)
                    .take(self.len())
                    .rev(),
            )
            .filter_map(|(entry, suffix)| Some((entry.data().ok()?, suffix)))
            .all(|(data, object)| {
                if let Some(string) = data.get_str() {
                    ListpackEntryInsert::String(string) == object
                } else if let Some(integer) = data.get_i64() {
                    ListpackEntryInsert::Integer(integer) == object
                } else {
                    false
                }
            })
    }

    /// Returns a sublist of objects with the prefix removed.
    /// [`None`] if the listpack doesn't start with the prefix.
    ///
    /// # Note
    ///
    /// As the listpack's elements cannot be of the same size, there is
    /// no way to produce a slice of the listpack, so the method
    /// returns a [`Vec`] of references to the elements.
    ///
    /// # Example
    ///
    /// ```
    /// use listpack_redis::Listpack;
    ///
    /// let mut listpack: Listpack = Listpack::default();
    /// listpack.push("Hello");
    /// listpack.push("World");
    /// assert_eq!(listpack.strip_prefix(&["Hello"]), vec!["World"]);
    /// ```
    pub fn strip_prefix<'a, 'b, T>(&'b self, prefix: &'a [T]) -> Vec<&'b ListpackEntryRef>
    where
        ListpackEntryInsert<'a>: std::convert::From<&'a T>,
    {
        if self.starts_with(prefix) {
            self.iter().skip(prefix.len()).collect()
        } else {
            Vec::default()
        }
    }

    /// Returns a sublist of objects with the suffix removed.
    /// [`None`] if the listpack doesn't start with the suffix.
    ///
    /// # Note
    ///
    /// As the listpack's elements cannot be of the same size, there is
    /// no way to produce a slice of the listpack, so the method
    /// returns a [`Vec`] of references to the elements.
    ///
    /// # Example
    ///
    /// ```
    /// use listpack_redis::Listpack;
    ///
    /// let mut listpack: Listpack = Listpack::default();
    /// listpack.push("Hello");
    /// listpack.push("World");
    /// assert_eq!(listpack.strip_suffix(&["World"]), vec!["Hello"]);
    /// ```
    pub fn strip_suffix<'a, 'b, T>(&'b mut self, suffix: &'a [T]) -> Vec<&'b ListpackEntryRef>
    where
        ListpackEntryInsert<'a>: std::convert::From<&'a T>,
    {
        if self.ends_with(suffix) {
            self.iter().take(self.len() - suffix.len()).collect()
        } else {
            Vec::default()
        }
    }

    /// Returns an iterator over the elements of the listpack.
    ///
    /// # Example
    ///
    /// ```
    /// use listpack_redis::Listpack;
    ///
    /// let mut listpack: Listpack = Listpack::default();
    ///
    /// listpack.push("Hello");
    /// listpack.push("World");
    ///
    /// let mut iter = listpack.iter();
    ///
    /// assert_eq!(iter.next().unwrap().to_string(), "Hello");
    /// assert_eq!(iter.next().unwrap().to_string(), "World");
    /// assert!(iter.next().is_none());
    /// ```
    pub fn iter(&self) -> ListpackIter<Allocator> {
        ListpackIter {
            listpack: self,
            index: 0,
        }
    }
}

/// The methods requiring the allocator to be a listpack allocator.
impl<Allocator> Listpack<Allocator>
where
    Allocator: ListpackAllocator,
    <Allocator as CustomAllocator>::Error: Debug,
{
    /// Splits the listpack into two at the given index. Returns a new
    /// listpack containing the elements from `at` to the end, and
    /// removes those elements from the original listpack.
    ///
    /// # Panics
    ///
    /// Panics if the index is out of bounds.
    ///
    /// # Example
    ///
    /// ```
    /// use listpack_redis::Listpack;
    ///
    /// let mut listpack: Listpack = Listpack::default();
    /// listpack.push("Hello, world!");
    /// listpack.push("Hello!");
    /// listpack.push("World!");
    ///
    /// let other = listpack.split_off(1);
    ///
    /// assert_eq!(listpack.len(), 1);
    /// assert_eq!(other.len(), 2);
    ///
    /// assert_eq!(listpack[0].to_string(), "Hello, world!");
    /// assert_eq!(other[0].to_string(), "Hello!");
    /// assert_eq!(other[1].to_string(), "World!");
    /// ```
    pub fn split_off(&mut self, at: usize) -> Self {
        let length = self.len();
        if at > length {
            panic!("The index is out of bounds.")
        }

        // TODO: use allocate with capacity and calculate the amount
        // of bytes needed, then memcpy instead of pushes.
        let mut other = Self::new(self.allocator.clone());

        self.drain(at..(at + length - 1))
            .for_each(|entry| other.push(ListpackEntryInsert::from(&entry)));

        other
    }
}

impl<Allocator> Listpack<Allocator>
where
    Allocator: ListpackAllocator,
    <Allocator as CustomAllocator>::Error: Debug,
{
    /// Creates a new listpack with the given capacity. A shorthand for
    /// `Listpack::with_capacity_and_allocator(capacity, Allocator::default())`.
    pub fn with_capacity<T>(capacity: T) -> Self
    where
        T: TryInto<ListpackCapacity>,
    {
        Self::with_capacity_and_allocator(capacity, Allocator::default())
    }
}

impl<Allocator, AllocatorError> Listpack<Allocator>
where
    Allocator: CustomAllocator<Error = AllocatorError>,
    AllocatorError: Debug,
{
    /// Returns a new listpack.
    ///
    /// # Example
    ///
    /// ```
    /// use listpack_redis::Listpack;
    /// use listpack_redis::allocator::DefaultAllocator;
    ///
    /// let allocator = DefaultAllocator;
    /// let listpack = Listpack::new(allocator);
    /// assert!(listpack.is_empty());
    /// ```
    pub fn new(allocator: Allocator) -> Self {
        Self::with_capacity_and_allocator(ListpackCapacity::ZERO, allocator)
    }

    fn allocate_header_for_capacity(
        allocator: &Allocator,
        capacity: ListpackCapacity,
    ) -> Result<ListpackAllocationPointer, AllocatorError> {
        let bytes_to_allocate = capacity.0;

        // This is an impossible situation, as the maximum size of the
        // is already checked in the `ListpackCapacity::try_from`.
        let total_bytes: u32 = capacity
            .0
            .try_into()
            .expect("The bytes to allocate fits into the header.");

        // Another impossible scenario, as we have fully satisfied the
        // requirements for this function to avoid returning an error.
        let layout = std::alloc::Layout::from_size_align(bytes_to_allocate, 1)
            .expect("Could not create layout");

        let ptr = allocator.allocate(layout)?;

        let header_ptr = ptr.cast().as_ptr();

        unsafe {
            *header_ptr = ListpackHeader {
                total_bytes,
                num_elements: 0,
            };
        }

        let mut pointer = ListpackAllocationPointer(ptr.cast());

        pointer.set_end_marker();

        Ok(pointer)
    }

    /// Creates a new listpack with the given capacity (the number of
    /// bytes). There is no notion of "capacity" in the listpack, as it
    /// is a single allocation and all the elements may vary in size,
    /// and the main purpose of the data structure is to be compressed.
    ///
    /// However, in certain use-cases it is useful to pre-allocate the
    /// memory for the listpack, so that the listpack doesn't have to
    /// reallocate the memory every time a new element is added.
    ///
    /// The allocated amount will be the given capacity plus the size
    /// of the listpack header and the end marker.
    ///
    /// # Panics
    ///
    /// Panics if the capacity is too big to be stored in the listpack.
    ///
    /// # Example
    ///
    /// ```
    /// use listpack_redis::Listpack;
    ///
    /// let listpack: Listpack = Listpack::with_capacity(10);
    /// assert!(listpack.is_empty());
    /// ```
    fn with_capacity_and_allocator<T>(capacity: T, allocator: Allocator) -> Self
    where
        T: TryInto<ListpackCapacity>,
    {
        let capacity = match capacity.try_into() {
            Ok(capacity) => capacity,
            Err(_) => panic!("Couldn't convert the provided capacity to listpack capacity"),
        };

        // TODO: provide the error back to the user.
        let allocation = Self::allocate_header_for_capacity(&allocator, capacity)
            .expect("Allocated header successfully.");

        Self {
            allocation,
            allocator,
        }
    }
}

impl<Allocator> Listpack<Allocator>
where
    Allocator: CustomAllocator,
{
    /// Reallocates the pointer to a new place in memory, growing the
    /// size of the data block.
    ///
    /// # Note
    ///
    /// After calling this function, the block contains two end markers:
    /// one at the end of the old block and one at the end of the new
    /// block (for the safety).
    fn grow(&mut self, new_layout: Layout) -> Result<(), <Allocator as CustomAllocator>::Error> {
        unsafe {
            self.allocation.0 = self
                .allocator
                .grow(self.allocation.ptr(), self.allocation.layout(), new_layout)?
                .cast();

            self.allocation.set_new_size(new_layout.size());
        }

        Ok(())
    }

    /// Grows the capacity of the listpack by `additional_bytes`.
    fn grow_by(
        &mut self,
        additional_bytes: usize,
    ) -> Result<(), <Allocator as CustomAllocator>::Error> {
        let new_layout =
            Layout::from_size_align(self.allocation.layout().size() + additional_bytes, 1)
                .expect("Created layout");
        self.grow(new_layout)
    }

    /// Shrinks the listpack by `bytes_to_shrink`.
    fn shrink_by(
        &mut self,
        bytes_to_shrink: usize,
    ) -> Result<(), <Allocator as CustomAllocator>::Error> {
        let new_layout =
            Layout::from_size_align(self.allocation.layout().size() - bytes_to_shrink, 1)
                .expect("Created layout");

        unsafe {
            self.allocation.0 = self
                .get_allocator()
                .shrink(self.allocation.ptr(), self.allocation.layout(), new_layout)?
                .cast();

            self.allocation.set_new_size(new_layout.size());
        }

        Ok(())
    }

    /// Truncates the listpack, keeping only the first `len` elements.
    ///
    /// # Example
    ///
    /// ```
    /// use listpack_redis::Listpack;
    ///
    /// let mut listpack: Listpack = Listpack::default();
    /// assert_eq!(listpack.len(), 0);
    /// listpack.push("Hello, world!");
    /// assert_eq!(listpack.len(), 1);
    /// listpack.push("Hello!");
    /// assert_eq!(listpack.len(), 2);
    /// listpack.truncate(1);
    /// assert_eq!(listpack.len(), 1);
    pub fn truncate(&mut self, len: usize) {
        if len > self.len() {
            return;
        }

        let start = len;
        let end = self.len();
        self.remove_range(start..end);
    }

    /// Clears the entire listpack. Same as calling [`Self::truncate()`]
    /// with `0` as an argument.
    ///
    /// # Example
    ///
    /// ```
    /// use listpack_redis::Listpack;
    /// let mut listpack: Listpack = Listpack::default();
    /// listpack.push("Hello, world!");
    /// assert_eq!(listpack.len(), 1);
    /// listpack.clear();
    /// assert_eq!(listpack.len(), 0);
    /// ```
    pub fn clear(&mut self) {
        self.truncate(0)
    }

    /// Appends an element to the back of the listpack.
    ///
    /// # Panics
    ///
    /// Panics if the string is too long to be stored in the listpack.
    ///
    /// # Example
    ///
    /// ```
    /// use listpack_redis::Listpack;
    ///
    /// let mut listpack: Listpack = Listpack::default();
    /// listpack.push("Hello, world!");
    /// assert_eq!(listpack.len(), 1);
    /// ```
    pub fn push<'a, T: Into<ListpackEntryInsert<'a>>>(&mut self, entry: T) {
        self.try_push(entry).expect("Pushed to listpack");
    }

    /// Inserts an element at the given index into the listpack.
    /// The insertion is done before the specified index, shifting
    /// all the elements past this index to the right.
    ///
    /// # Panics
    ///
    /// Panics if the string is too long to be stored in the listpack
    /// or if the index is out of bounds.
    ///
    /// The maximum length of a string stored within the listpack is
    /// (`std::u32::MAX - 1`) bytes.
    ///
    /// # Example
    ///
    /// ```
    /// use listpack_redis::Listpack;
    ///
    /// let mut listpack: Listpack = Listpack::default();
    /// listpack.push("Hello, world!");
    /// listpack.insert(0, "Hello!");
    /// assert_eq!(listpack.len(), 2);
    /// assert_eq!(listpack.get(0).unwrap().to_string(), "Hello!");
    /// assert_eq!(listpack.get(1).unwrap().to_string(), "Hello, world!");
    /// ```
    /// Or a more familiar example from [`std::vec::Vec`]:
    /// ```
    /// use listpack_redis::Listpack;
    /// let mut listpack: Listpack = Listpack::default();
    /// listpack.push(1);
    /// listpack.push(2);
    /// listpack.push(3);
    ///
    /// listpack.insert(1, 4);
    /// assert_eq!(listpack.len(), 4);
    /// assert_eq!(listpack.get(0).unwrap().to_string(), "1");
    /// assert_eq!(listpack.get(1).unwrap().to_string(), "4");
    /// assert_eq!(listpack.get(2).unwrap().to_string(), "2");
    /// assert_eq!(listpack.get(3).unwrap().to_string(), "3");
    /// ```
    pub fn insert<'a, T: Into<ListpackEntryInsert<'a>>>(&mut self, index: usize, entry: T) {
        self.insert_with_placement_internal(InsertionPlacement::Before(index), entry)
    }

    /// Inserts an element at the given index into the listpack.
    ///
    /// The safe version of [`Self::insert`].
    ///
    /// # Example
    ///
    /// ```
    /// use listpack_redis::Listpack;
    ///
    /// let mut listpack: Listpack = Listpack::default();
    ///
    /// // Index out of bounds:
    /// assert!(listpack.try_insert(0, "Hello, world!").is_err());
    /// listpack.push("Hello, world!");
    /// assert!(listpack.try_insert(0, "Hello!").is_ok());
    ///
    /// assert_eq!(listpack.len(), 2);
    /// assert_eq!(listpack.get(0).unwrap().to_string(), "Hello!");
    /// assert_eq!(listpack.get(1).unwrap().to_string(), "Hello, world!");
    /// ```
    pub fn try_insert<'a, T: Into<ListpackEntryInsert<'a>>>(
        &mut self,
        index: usize,
        entry: T,
    ) -> Result {
        self.try_insert_with_placement_internal(InsertionPlacement::Before(index), entry)
    }

    fn insert_with_placement_internal<'a, T: Into<ListpackEntryInsert<'a>>>(
        &mut self,
        placement: InsertionPlacement,
        entry: T,
    ) {
        self.try_insert_with_placement_internal(placement, entry)
            .expect("Insert an element into listpack");
    }

    // 1. First and foremost, check that the index is within the bounds.
    // 2. Check that the listpack can fit the new element: if it is a
    //    replacement of an existing element, consider its size,
    //    otherwise, just check that the listpack can fit the new
    //    element.
    // 3. Grow the listpack if necessary by the amount of bytes
    //    necessary.
    // 4. If it was a replacement, replace the element, otherwise
    //    insert the new element, either before or after the referred
    //    element, by shifting the memory of the listpack to the right.
    // 5. Safety check: if reallocating, don't forget to mark the end
    //    of the listpack.
    fn try_insert_with_placement_internal<'a, T: Into<ListpackEntryInsert<'a>>>(
        &mut self,
        placement: InsertionPlacement,
        entry: T,
    ) -> Result {
        let entry = entry.into();
        let index = placement.index();

        if index > self.len() {
            return Err(crate::error::InsertionError::IndexOutOfBounds {
                index,
                length: self.len(),
            }
            .into());
        }

        let encoded_value = entry.try_encode()?;

        let referred_element_ptr = self.get_internal_entry_ptr(index).ok_or(
            crate::error::InsertionError::IndexOutOfBounds {
                index,
                length: self.len(),
            },
        )?;

        let referred_element = ListpackEntryRef::ref_from_ptr(referred_element_ptr);

        let referred_element_offset_from_start = unsafe {
            referred_element_ptr
                .as_ptr()
                .offset_from(self.allocation.data_start_ptr()) as usize
        };
        let referred_element_length = referred_element.total_bytes();

        let element_to_replace = placement.to_replace().map(|_| referred_element);

        let length_to_relocate = {
            let referred_element_ptr = referred_element.as_ptr();
            let end_ptr = self.allocation.data_end_ptr();
            unsafe { end_ptr.offset_from(referred_element_ptr) as usize }
        };

        let fitting_requirement = self.can_fit_entry(&entry, element_to_replace)?;

        match fitting_requirement {
            FittingRequirement::NoChange => {}
            FittingRequirement::Grow(size) => {
                self.grow_by(size)
                    .map_err(|_| AllocationError::FailedToGrow { size })?;
            }
            FittingRequirement::Shrink(size) => {
                // The downsizing can only happen in the case of a
                // replace. That means the new element is smaller than
                // the one it replaces. The element to replace is the
                // referred element. We can reposition the elements to
                // the right of the referred element to the left by the
                // size of the new element, so that the shrinking can
                // happen.

                let next_after_referred_element_ptr = unsafe {
                    referred_element
                        .as_ptr()
                        .add(referred_element.total_bytes())
                };

                // Exclude the referred element from the length to
                // relocate.
                let length_to_relocate = length_to_relocate - referred_element.total_bytes();

                if length_to_relocate > 0 {
                    unsafe {
                        std::ptr::copy(
                            next_after_referred_element_ptr,
                            referred_element
                                .as_ptr()
                                .cast_mut()
                                .add(encoded_value.len()),
                            length_to_relocate,
                        );
                    }
                }

                self.shrink_by(size)
                    .map_err(|_| AllocationError::FailedToShrink { size })?;
            }
        }

        // Lets obtain a new reference to the element after the
        // reallocation. If the element was to be replaced, it might
        // be partially destroyed by the reallocation. So, we can't
        // work with it here, but we can work with its pointer.
        let referred_element_ptr = unsafe {
            NonNull::new_unchecked(
                self.allocation
                    .data_start_ptr()
                    .cast_mut()
                    .add(referred_element_offset_from_start),
            )
        }
        .as_ptr();

        match placement {
            InsertionPlacement::Before(_) => {
                // 1. Relocate all the memory to the right of the
                // referred element (including the referred element's
                // memory) by the size of the new element.
                // 2. Insert the new element at the location of the
                // referred element.

                unsafe {
                    // Shift the elements to the right.
                    std::ptr::copy(
                        referred_element_ptr,
                        referred_element_ptr.add(encoded_value.len()),
                        length_to_relocate,
                    );

                    std::ptr::copy_nonoverlapping(
                        encoded_value.as_ptr(),
                        referred_element_ptr,
                        encoded_value.len(),
                    );
                }

                self.increment_num_elements();
            }
            InsertionPlacement::After(_) => {
                // 1. Relocate all the memory to the right of the
                // referred element, excluding the referred element's
                // memory, by the size of the new element.
                // 2. Insert the new element at the location after that
                // of the referred element.

                // If this is the last element, it should point to
                // the end marker (the old one, before the
                // reallocation).

                // Skip the referred element.
                let next_after_referred_element_ptr =
                    unsafe { referred_element_ptr.add(referred_element_length) };

                unsafe {
                    // Shift the elements to the right.
                    std::ptr::copy_nonoverlapping(
                        next_after_referred_element_ptr,
                        next_after_referred_element_ptr.add(encoded_value.len()),
                        length_to_relocate - referred_element_length,
                    );

                    std::ptr::copy_nonoverlapping(
                        encoded_value.as_ptr(),
                        next_after_referred_element_ptr,
                        encoded_value.len(),
                    );
                }

                self.increment_num_elements();
            }
            InsertionPlacement::Replace(_) => unsafe {
                // Skip the referred element.
                let next_after_referred_element_ptr =
                    referred_element_ptr.add(referred_element_length);

                // Shift the elements to the right.
                std::ptr::copy_nonoverlapping(
                    next_after_referred_element_ptr,
                    referred_element_ptr.add(encoded_value.len()),
                    length_to_relocate - referred_element_length,
                );

                std::ptr::copy_nonoverlapping(
                    encoded_value.as_ptr(),
                    referred_element_ptr,
                    encoded_value.len(),
                );
            },
        }

        Ok(())
    }

    /// A safe version of [`Self::push`]. It is a little more useful,
    /// when the listpack grows large. As the listpack is a single
    /// allocation, and this allocation is limited in terms of length,
    /// by the listpack header's `total_bytes` field, it is only
    /// possible to occupy the four bytes (`2u32.pow(32) - 1`) bytes of
    /// memory. This method will return an [`crate::error::Error`] if
    /// the listpack is full and the element cannot be pushed.
    ///
    /// # Example
    ///
    /// ```
    /// use listpack_redis::Listpack;
    ///
    /// let mut listpack: Listpack = Listpack::default();
    /// assert!(listpack.try_push("Hello, world!").is_ok());
    /// assert_eq!(listpack.len(), 1);
    /// ```
    pub fn try_push<'a, T: Into<ListpackEntryInsert<'a>>>(&mut self, entry: T) -> Result {
        let entry = entry.into();
        let fitting_requirement = self.can_fit_entry(&entry, None)?;
        let old_end_offset = unsafe {
            self.allocation
                .data_end_ptr()
                .offset_from(self.allocation.ptr().as_ptr().cast()) as usize
        };

        match fitting_requirement {
            FittingRequirement::NoChange => {}
            FittingRequirement::Grow(size) => {
                self.grow_by(size)
                    .map_err(|_| AllocationError::FailedToGrow { size })?;
            }
            FittingRequirement::Shrink(_) => {
                unreachable!("The listpack is growing, not shrinking.");
            }
        }

        let encoded_value = entry.try_encode()?;

        unsafe {
            let ptr = self.allocation.ptr().as_ptr().add(old_end_offset);
            std::ptr::copy_nonoverlapping(encoded_value.as_ptr(), ptr, encoded_value.len());
        }

        self.increment_num_elements();

        Ok(())
    }

    /// Removes the element at the given index from the listpack and
    /// returns it.
    ///
    /// # Panics
    ///
    /// Panics if the index is out of bounds.
    ///
    /// # Example
    ///
    /// ```
    /// use listpack_redis::Listpack;
    ///
    /// let mut listpack: Listpack = Listpack::default();
    /// listpack.push("Hello, world!");
    /// let removed = listpack.remove(0);
    /// assert_eq!(listpack.len(), 0);
    /// assert_eq!(removed.to_string(), "Hello, world!");
    /// ```
    pub fn remove(&mut self, index: usize) -> ListpackEntryRemoved {
        let removed = self.get(index).unwrap().into();
        self.remove_range(index..(index + 1));
        removed
    }

    /// Retains only the elements specified by the predicate.
    ///
    /// In other words, removes all elements `e` such that `f(&e)`
    /// returns `false`. This method operates in place, visiting each
    /// element exactly once in the original order, and preserves the
    /// order of the retained elements.
    ///
    /// # Example
    ///
    /// ```
    /// use listpack_redis::Listpack;
    ///
    /// let mut listpack: Listpack = Listpack::default();
    /// listpack.push("Hello, world!");
    /// listpack.push("Hello!");
    /// listpack.push("World!");
    /// listpack.retain(|entry| entry.to_string().contains("Hello"));
    ///
    /// assert_eq!(listpack.len(), 2);
    /// assert_eq!(listpack[0].to_string(), "Hello, world!");
    /// assert_eq!(listpack[1].to_string(), "Hello!");
    /// ```
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&ListpackEntryRef) -> bool,
    {
        let mut index = 0;
        while index < self.len() {
            let entry = self.get(index).unwrap();
            if !f(entry) {
                let _ = self.remove(index);
            } else {
                index += 1;
            }
        }
    }

    /// Appends the elements of another listpack to the back of this
    /// listpack.
    ///
    /// # Panics
    ///
    /// Panics if the listpacks cannot be merged.
    ///
    /// # Example
    ///
    /// ```
    /// use listpack_redis::Listpack;
    ///
    /// let mut listpack1: Listpack = Listpack::default();
    /// listpack1.push("Hello, world!");
    /// listpack1.push("Hello!");
    ///
    /// let mut listpack2: Listpack = Listpack::default();
    /// listpack2.push("World!");
    ///
    /// listpack1.append(&mut listpack2);
    ///
    /// assert_eq!(listpack1.len(), 3);
    /// assert_eq!(listpack2.len(), 1);
    ///
    /// assert_eq!(listpack1[0].to_string(), "Hello, world!");
    /// assert_eq!(listpack1[1].to_string(), "Hello!");
    /// assert_eq!(listpack1[2].to_string(), "World!");
    /// ```
    pub fn append(&mut self, other: &mut Self) {
        other.iter().for_each(|entry| {
            let data = entry.data().expect("Extract an entry from listpack");
            let entry = ListpackEntryInsert::try_from(&data)
                .expect("Convert an entry to ListpackEntryInsert");
            self.push(entry);
        });
    }

    /// Removes the elements in the specified range from the listpack
    /// in bulk, returning all removed elements as an iterator.
    ///
    /// See [`crate::iter::ListpackDrain`].
    ///
    /// # Panics
    ///
    /// Panics if the starting point is greater than the end point
    /// or if the end point is greater than the length of the listpack.
    ///
    /// # Example
    ///
    /// ```
    /// use listpack_redis::Listpack;
    ///
    /// let mut listpack: Listpack = Listpack::default();
    /// listpack.push("Hello, world!");
    /// listpack.push("Hello!");
    /// listpack.push("World!");
    /// let removed = listpack.drain(1..3).collect::<Vec<_>>();
    /// assert_eq!(listpack.len(), 1);
    /// assert_eq!(removed.len(), 2);
    /// assert_eq!(removed[0].get_str().unwrap(), "Hello!");
    /// assert_eq!(removed[1].get_str().unwrap(), "World!");
    /// ```
    ///
    /// Use it the same way as [`Self::clear`], if you want to remove
    /// all elements from the listpack:
    ///
    /// ```
    /// use listpack_redis::Listpack;
    ///
    /// let mut listpack: Listpack = Listpack::default();
    /// listpack.push("Hello, world!");
    /// listpack.push("Hello!");
    /// listpack.push("World!");
    /// let removed = listpack.drain(..).collect::<Vec<_>>();
    /// assert!(listpack.is_empty());
    /// assert_eq!(removed.len(), 3);
    /// assert_eq!(removed[0].get_str().unwrap(), "Hello, world!");
    /// assert_eq!(removed[1].get_str().unwrap(), "Hello!");
    /// assert_eq!(removed[2].get_str().unwrap(), "World!");
    /// ```
    ///
    /// See [std::vec::Vec::drain] for more information.
    pub fn drain<R>(&mut self, range: R) -> impl std::iter::Iterator<Item = ListpackEntryRemoved>
    where
        R: RangeBounds<usize>,
    {
        use std::ops::Bound;

        let start = match range.start_bound() {
            Bound::Included(&start) => start,
            Bound::Excluded(&start) => start + 1,
            Bound::Unbounded => 0,
        };

        let end = match range.end_bound() {
            Bound::Included(&end) => end + 1,
            Bound::Excluded(&end) => end,
            Bound::Unbounded => self.len(),
        };

        if start > end {
            panic!("The start is greater than the end.")
        } else if end > self.len() {
            panic!("The end is greater than the length of the listpack.")
        }

        let length = end - start;
        let removed_elements = self
            .iter()
            .skip(start)
            .take(length)
            .map(ListpackEntryRemoved::from)
            .collect::<Vec<_>>();

        self.remove_range(start..end);

        removed_elements.into_iter()
    }

    /// Appends all the elements of a slice to the listpack.
    ///
    /// # Note
    ///
    /// The elements must be convertible to [`ListpackEntryInsert`].
    ///
    /// # Example
    ///
    /// ```
    /// use listpack_redis::Listpack;
    ///
    /// let mut listpack: Listpack = Listpack::default();
    /// listpack.extend_from_slice(&["Hello", "World", "!"]);
    /// assert_eq!(listpack.len(), 3);
    /// assert_eq!(listpack[0].to_string(), "Hello");
    /// assert_eq!(listpack[1].to_string(), "World");
    /// assert_eq!(listpack[2].to_string(), "!");
    /// ```
    pub fn extend_from_slice<'a, T>(&mut self, slice: &'a [T])
    where
        &'a T: Into<ListpackEntryInsert<'a>>,
        ListpackEntryInsert<'a>: std::convert::From<&'a T>,
    {
        // TODO: perform a one-time reallocation instead of many
        // due to `push()`.
        for item in slice {
            self.push(item.into());
        }
    }

    /// Copies elements from `src` range to the end of the listpack.
    ///
    /// # Panics
    ///
    /// Panics if the range is out of bounds.
    ///
    /// # Example
    ///
    /// ```
    /// use listpack_redis::Listpack;
    ///
    /// let mut listpack: Listpack = Listpack::default();
    ///
    /// listpack.push("Hello");
    /// listpack.push("World");
    /// listpack.push("!");
    ///
    /// // Copy the first two elements to the end of the listpack.
    /// listpack.extend_from_within(0..2);
    ///
    /// assert_eq!(listpack.len(), 5);
    /// assert_eq!(listpack[0].to_string(), "Hello");
    /// assert_eq!(listpack[1].to_string(), "World");
    /// assert_eq!(listpack[2].to_string(), "!");
    /// assert_eq!(listpack[3].to_string(), "Hello");
    /// assert_eq!(listpack[4].to_string(), "World");
    /// ```
    pub fn extend_from_within(&mut self, src: std::ops::Range<usize>) {
        if src.contains(&self.len()) {
            panic!("The range is out of bounds.");
        }

        for i in src {
            let entry = self.get(i).unwrap();
            let entry = ListpackEntryRemoved::from(entry);
            let entry = ListpackEntryInsert::from(&entry);

            self.push(entry);
        }
    }

    /// Removes consecutive repeated elements from the listpack.
    ///
    /// # Example
    ///
    /// ```
    /// use listpack_redis::Listpack;
    ///
    /// let mut listpack: Listpack = Listpack::default();
    /// listpack.push("Hello");
    /// listpack.push("Hello");
    /// listpack.push("World");
    /// listpack.push("World");
    /// listpack.push("World");
    /// listpack.push("!");
    /// listpack.dedup();
    /// assert_eq!(listpack.len(), 3);
    /// assert_eq!(listpack[0].to_string(), "Hello");
    /// assert_eq!(listpack[1].to_string(), "World");
    /// assert_eq!(listpack[2].to_string(), "!");
    /// ```
    pub fn dedup(&mut self) {
        let mut index = 0;
        let mut indexes_to_remove = Vec::new();

        while index < self.len() {
            let entry = self.get(index).unwrap();
            let mut next_index = index + 1;
            while next_index < self.len() {
                let next_entry = self.get(next_index).unwrap();
                if entry == next_entry {
                    indexes_to_remove.push(next_index);
                    next_index += 1;
                } else {
                    break;
                }
            }
            index = next_index;
        }

        for index in indexes_to_remove.into_iter().rev() {
            let _ = self.remove(index);
        }
    }

    /// Reverses the order of the elements in the listpack in place.
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
    ///
    /// listpack.reverse();
    ///
    /// assert_eq!(listpack.len(), 3);
    /// assert_eq!(listpack[0].to_string(), "!");
    /// assert_eq!(listpack[1].to_string(), "World");
    /// assert_eq!(listpack[2].to_string(), "Hello");
    /// ```
    pub fn reverse(&mut self) {
        let length = self.len();
        let mut indexes_to_swap = Vec::new();

        for i in 0..length / 2 {
            indexes_to_swap.push((i, length - i - 1));
        }

        for (a, b) in indexes_to_swap {
            self.swap(a, b);
        }
    }

    /// Removes the last element from the listpack and returns it, or
    /// [`None`] if it is empty. The returned [`ListpackEntry`] is not
    /// a part of the listpack anymore.
    ///
    /// # Example
    ///
    /// ```
    /// use listpack_redis::Listpack;
    ///
    /// let mut listpack: Listpack = Listpack::default();
    /// listpack.push("Hello, world!");
    /// assert_eq!(listpack.len(), 1);
    /// let removed = listpack.pop().unwrap();
    /// assert_eq!(listpack.len(), 0);
    /// assert_eq!(removed.get_str().unwrap(), "Hello, world!");
    /// ```
    pub fn pop(&mut self) -> Option<ListpackEntryRemoved> {
        if self.is_empty() {
            return None;
        }

        Some(self.remove(self.len() - 1))
    }

    // Commented out, as there is no such method in listpack C API as
    // of now.
    // /// Removes the element at the given index from the listpack and
    // /// returns it, swapping it with the last element.
    // ///
    // /// # Panics
    // ///
    // /// Panics if the index is out of bounds.
    // ///
    // /// # Example
    // ///
    // /// ```
    // /// use listpack_redis::Listpack;
    // ///
    // /// let mut listpack = Listpack::default();
    // /// listpack.push("Hello");
    // /// listpack.push("World");
    // /// listpack.push("!");
    // /// let removed = listpack.swap_remove(0);
    // /// assert_eq!(listpack.len(), 2);
    // /// assert_eq!(removed.as_str().unwrap(), "Hello");
    // /// assert_eq!(listpack.get(0).unwrap().data().unwrap().get_small_str().unwrap(), "!");
    // /// assert_eq!(listpack.get(1).unwrap().data().unwrap().get_small_str().unwrap(), "World");
    // /// ```
    // pub fn swap_remove(&mut self, index: usize) -> ListpackEntryRemoved {
    //     let ptr = NonNull::new(unsafe { bindings::lpSeek(self.ptr.as_ptr(), index as _) })
    //         .expect("Index out of bounds.");
    //     let cloned = ListpackEntryRemoved::from(ptr);
    //     let last = NonNull::new(unsafe { bindings::lpLast(self.ptr.as_ptr()) })
    //         .expect("The last element is accessible.");
    //     self.ptr = NonNull::new(unsafe {
    //         bindings::lpDelete(self.ptr.as_ptr(), ptr.as_ptr(), std::ptr::null_mut())
    //     })
    //     .expect("Deleted from listpack");
    //     cloned
    // }

    // TODO: implement
    // /// Returns an iterator over the elements of the listpack.
    // pub fn iter_mut(&mut self) -> ListpackIterMut {
    //     ListpackIterMut {
    //         listpack: self,
    //         index: 0,
    //     }
    // }
}

/// Slice methods.
///
/// Since the listpack objects aren't laid out in memory as a
/// contiguous array, we can't implement the [`Deref`] trait to
/// convert the listpack to a slice. Instead, we provide the
/// corresponding methods.
impl<Allocator> Listpack<Allocator>
where
    Allocator: CustomAllocator,
{
    /// Returns an element of the listpack at the given index.
    ///
    /// # Example
    ///
    /// ```
    /// use listpack_redis::Listpack;
    ///
    /// let mut listpack: Listpack = Listpack::default();
    /// listpack.push("Hello");
    /// listpack.push("World");
    /// assert_eq!(listpack.get(0).unwrap().data().unwrap().get_small_str().unwrap(), "Hello");
    /// assert_eq!(listpack.get(1).unwrap().data().unwrap().get_small_str().unwrap(), "World");
    /// assert!(listpack.get(2).is_none());
    /// ```
    pub fn get(&self, index: usize) -> Option<&ListpackEntryRef> {
        self.get_internal_entry_ptr(index)
            .map(ListpackEntryRef::ref_from_ptr)
    }

    /// Returns a mutable reference to element of the listpack at the
    /// given index.
    ///
    /// # Example
    ///
    /// ```
    /// use listpack_redis::Listpack;
    ///
    /// let mut listpack: Listpack = Listpack::default();
    /// listpack.push("Hello");
    /// listpack.push("World");
    /// assert_eq!(listpack.get_mut(0).unwrap().to_string(), "Hello");
    /// assert_eq!(listpack.get_mut(1).unwrap().to_string(), "World");
    /// assert!(listpack.get_mut(2).is_none());
    /// ```
    pub fn get_mut(&mut self, index: usize) -> Option<ListpackEntryMutable<Allocator>> {
        self.get_internal_entry_ptr(index).map(|ptr| {
            let entry = ListpackEntryRef::ref_from_ptr(ptr);
            ListpackEntryMutable::new(self, entry, index)
        })
    }
}

impl<Allocator> Index<usize> for Listpack<Allocator>
where
    Allocator: CustomAllocator,
{
    type Output = ListpackEntryRef;

    fn index(&self, index: usize) -> &Self::Output {
        self.get(index).expect("Index out of bounds.")
    }
}

impl<Allocator> IntoIterator for Listpack<Allocator>
where
    Allocator: CustomAllocator,
{
    type Item = ListpackEntryRemoved;
    type IntoIter = ListpackIntoIter<Allocator>;

    fn into_iter(self) -> Self::IntoIter {
        ListpackIntoIter {
            listpack: self,
            index: 0,
        }
    }
}

/// Specific methods for this list-pack implementation.
impl<Allocator> Listpack<Allocator>
where
    Allocator: CustomAllocator,
{
    fn increment_num_elements(&mut self) {
        let num_elements = self.get_header_ref().num_elements() as u16;
        self.set_num_elements(num_elements + 1);
    }

    fn set_num_elements(&mut self, num_elements: u16) {
        self.get_header_mut().set_num_elements(num_elements);
    }

    /// Validates the listpack by iterating over its memory and
    /// checking that the entries are correctly formatted.
    #[allow(unused)]
    fn validate(&self) -> Result {
        if self.is_empty() {
            return Ok(());
        }

        let mut current = 0;
        let mut data = self.allocation.data_start_slice();

        while current < self.len() {
            if data[0] == END_MARKER {
                return Err(crate::error::Error::UnexpectedEndMarker);
            }

            let entry = ListpackEntryRef::ref_from_slice(data);
            data = &data[entry.total_bytes()..];
            current += 1;
        }

        if data[0] != END_MARKER {
            return Err(crate::error::Error::MissingEndMarker);
        }

        Ok(())
    }

    fn read_element_length_from_the_end(ptr: *const u8) -> usize {
        let mut data = ptr;
        let mut bytes = [0u8; 5];
        let mut current = bytes.len() - 1;

        loop {
            let byte = unsafe { *data };
            bytes[current] = byte;

            if byte & 0b1000_0000 == 0 {
                break;
            }

            current -= 1;

            data = unsafe { data.sub(1) };
        }

        // Concatenate all the bytes from the left-to-right, ignoring
        // the most significant bit.
        let mut length = 0;

        for byte in bytes[current..].iter() {
            length = (length << 7) | (byte & 0b0111_1111) as usize;
        }

        // length + bytes.len() - 1 - current
        length + bytes.len() - current
    }

    fn get_internal_entry_ptr_from_start(&self, index: usize) -> Option<NonNull<u8>> {
        if self.is_empty() || index >= self.len() {
            return None;
        }

        let mut current = 0;

        let mut data = self.allocation.data_start_slice();

        while current < index {
            if data[0] == END_MARKER {
                return None;
            }

            let entry = ListpackEntryRef::ref_from_slice(data);
            data = data[entry.total_bytes()..].try_into().unwrap();
            current += 1;
        }

        Some(unsafe { NonNull::new_unchecked(data.as_ptr().cast_mut()) })
    }

    fn get_internal_entry_ptr_from_end(&self, index: usize) -> Option<NonNull<u8>> {
        if self.is_empty() || index >= self.len() {
            return None;
        }

        let mut current = self.len();
        // Point to the last byte of the last's element total element
        // length.
        let mut data = self.allocation.data_end_ptr();

        while current > index {
            let element_length = Self::read_element_length_from_the_end(unsafe { data.sub(1) });
            data = unsafe { data.sub(element_length) };

            if current == 0 {
                return None;
            }

            current -= 1;
        }

        Some(unsafe { NonNull::new_unchecked(data.cast_mut()) })
    }

    /// Returns a pointer to the listpack's entry at the given index.
    fn get_internal_entry_ptr(&self, index: usize) -> Option<NonNull<u8>> {
        // Check that the index is at the beginning or close to the end,
        // and search for the entry from the beginning or the end
        // respectively. This will reduce the number of iterations
        // needed to find the entry.

        if index < self.len() / 2 {
            self.get_internal_entry_ptr_from_start(index)
        } else {
            self.get_internal_entry_ptr_from_end(index)
        }
    }

    /// Returns the amount of bytes used by the listpack to store the
    /// elements.
    ///
    /// # Example
    ///
    /// ```
    /// use listpack_redis::Listpack;
    ///
    /// let mut listpack: Listpack = Listpack::default();
    /// assert_eq!(listpack.get_storage_bytes(), 7);
    /// listpack.push("Hello, world!");
    /// assert_eq!(listpack.get_storage_bytes(), 22);
    /// listpack.push("Hello!");
    /// assert_eq!(listpack.get_storage_bytes(), 30);
    /// let _ = listpack.pop();
    /// assert_eq!(listpack.get_storage_bytes(), 22);
    /// ```
    pub fn get_storage_bytes(&self) -> usize {
        self.get_header_ref().total_bytes()
    }

    /// Removes the elements in the specified range from the listpack.
    ///
    /// # Panics
    ///
    /// Panics if the range is out of bounds.
    ///
    /// # Example
    ///
    /// ```
    /// use listpack_redis::Listpack;
    ///
    /// let mut listpack: Listpack = Listpack::default();
    /// listpack.push("Hello, world!");
    /// listpack.push("Hello!");
    /// listpack.push("World!");
    /// assert_eq!(listpack.len(), 3);
    /// assert_eq!(listpack.get_storage_bytes(), 38);
    /// listpack.remove_range(1..3);
    /// assert_eq!(listpack.len(), 1);
    /// assert_eq!(listpack.get_storage_bytes(), 22);
    /// assert_eq!(listpack.get(0).unwrap().to_string(), "Hello, world!");
    /// ```
    pub fn remove_range(&mut self, range: std::ops::Range<usize>) {
        self.try_remove_range(range)
            .expect("Remove the range of elements.");
    }

    /// A safe version of [`Self::remove_range`].
    pub fn try_remove_range(&mut self, range: std::ops::Range<usize>) -> Result {
        let length = range.len();

        if range.is_empty() {
            return Ok(());
        }

        if range.end > self.len() {
            return Err(crate::error::DeletionError::IndexOutOfBounds {
                start_index: range.start,
                delete_count: length,
                length: self.len(),
            }
            .into());
        }

        // 1. Position a pointer to the start of the range.
        let start_element_ptr =
            self.get_internal_entry_ptr(range.start)
                .ok_or(crate::error::Error::Deletion(
                    crate::error::DeletionError::IndexOutOfBounds {
                        start_index: range.start,
                        delete_count: length,
                        length: self.len(),
                    },
                ))?;

        // 2. Determine the length of the range in bytes by iterating
        // over the elements and counting their sizes.
        // The `end_element_ptr` points to the beginning of the element
        // after the range (of the end marker).
        let (length_to_delete, end_element_ptr) = {
            let mut bytes = 0;
            let mut current = 0;
            let mut till_ptr = start_element_ptr.as_ptr();

            while current < length {
                if till_ptr.is_null() || unsafe { *till_ptr } == END_MARKER {
                    return Err(crate::error::Error::UnexpectedEndMarker);
                }

                let entry =
                    ListpackEntryRef::ref_from_ptr(unsafe { NonNull::new_unchecked(till_ptr) });

                till_ptr = unsafe { till_ptr.add(entry.total_bytes()) };
                bytes += entry.total_bytes();
                current += 1;
            }

            (bytes, till_ptr)
        };

        // 3. Delete the range by moving the elements to the left, and
        // then shrinking the listpack.

        let listpack_end_ptr = self.allocation.data_end_ptr();

        // The length of the elements after the range, that must be
        // moved to the left and left in the listpack.
        let rest_elements_length =
            unsafe { listpack_end_ptr.offset_from(end_element_ptr) } as usize;

        unsafe {
            std::ptr::copy(
                end_element_ptr,
                start_element_ptr.as_ptr(),
                rest_elements_length,
                // self.get_storage_bytes() - (data as usize - self.allocation.data_start_ptr().as_ptr() as usize),
            );
        }

        self.shrink_by(length_to_delete)
            .map_err(|_| AllocationError::FailedToShrink {
                size: length_to_delete,
            })?;

        self.set_num_elements((self.len() - range.count()) as u16);

        Ok(())
    }

    /// Removes all the elements outside of the range provided. Sort of
    /// an inverse of [`Self::try_remove_range`].
    ///
    /// # Example
    ///
    /// ```
    /// use listpack_redis::Listpack;
    ///
    /// let mut listpack: Listpack = Listpack::default();
    /// listpack.push("Hello, world!");
    /// listpack.push("Hello!");
    /// listpack.push("World!");
    ///
    /// listpack.keep_range(1..3);
    ///
    /// assert_eq!(listpack.len(), 2);
    /// assert_eq!(listpack.get(0).unwrap().to_string(), "Hello!");
    /// assert_eq!(listpack.get(1).unwrap().to_string(), "World!");
    /// ```
    pub fn try_keep_range(&mut self, range: std::ops::Range<usize>) -> Result {
        self.try_remove_range(range.end..self.len())
            .and_then(|_| self.try_remove_range(0..range.start))
    }

    /// A safe version of [`Self::keep_range`].
    pub fn keep_range(&mut self, range: std::ops::Range<usize>) {
        self.try_keep_range(range)
            .expect("Keep the range of elements.");
    }

    /// Inserts an element at the given index into the listpack, after
    /// the specified index.
    ///
    /// # Panics
    ///
    /// Panics if the string is too long to be stored in the listpack
    /// or if the index is out of bounds.
    ///
    /// # Example
    ///
    /// ```
    /// use listpack_redis::Listpack;
    ///
    /// let mut listpack: Listpack = Listpack::default();
    /// listpack.push("Hello, world!");
    /// listpack.insert_after(0, "Hello!");
    /// assert_eq!(listpack.len(), 2);
    /// assert_eq!(listpack.get(0).unwrap().to_string(), "Hello, world!");
    /// assert_eq!(listpack.get(1).unwrap().to_string(), "Hello!");
    /// ```
    pub fn insert_after<'a, T: Into<ListpackEntryInsert<'a>>>(&mut self, index: usize, entry: T) {
        self.insert_with_placement_internal(InsertionPlacement::After(index), entry)
    }

    /// Inserts an element at the given index into the listpack, after
    /// the specified index.
    ///
    /// The safe version of [`Self::insert_after`].
    ///
    /// # Example
    ///
    /// ```
    /// use listpack_redis::Listpack;
    ///
    /// let mut listpack: Listpack = Listpack::default();
    /// listpack.push("Hello, world!");
    /// assert!(listpack.try_insert_after(0, "Hello!").is_ok());
    ///
    /// assert_eq!(listpack.len(), 2);
    /// assert_eq!(listpack.get(0).unwrap().to_string(), "Hello, world!");
    /// assert_eq!(listpack.get(1).unwrap().to_string(), "Hello!");
    /// ```
    pub fn try_insert_after<'a, T: Into<ListpackEntryInsert<'a>>>(
        &mut self,
        index: usize,
        entry: T,
    ) -> Result {
        self.try_insert_with_placement_internal(InsertionPlacement::After(index), entry)
    }

    /// Replaces the element at the given index with the given element.
    ///
    /// # Panics
    ///
    /// Panics if the string is too long to be stored in the listpack
    /// or if the index is out of bounds.
    ///
    /// # Example
    ///
    /// ```
    /// use listpack_redis::Listpack;
    ///
    /// let mut listpack: Listpack = Listpack::default();
    /// listpack.push("Hello, world!");
    /// listpack.replace(0, "Hello!");
    /// assert_eq!(listpack.len(), 1);
    /// assert_eq!(listpack.get_storage_bytes(), 15);
    /// assert_eq!(listpack.get(0).unwrap().to_string(), "Hello!");
    /// assert_eq!(listpack.get_storage_bytes(), 15);
    /// ```
    pub fn replace<'a, T: Into<ListpackEntryInsert<'a>>>(&mut self, index: usize, entry: T) {
        self.try_replace(index, entry).expect("Replaced an element")
    }

    /// Replaces the element at the given index with the given element.
    ///
    /// The safe version of [`Self::replace`].
    ///
    /// # Example
    ///
    /// ```
    /// use listpack_redis::Listpack;
    ///
    /// let mut listpack: Listpack = Listpack::default();
    ///
    /// listpack.push("Hello, world!");
    ///
    /// assert!(listpack.try_replace(0, "Hello!").is_ok());
    ///
    /// assert_eq!(listpack.len(), 1);
    /// assert_eq!(listpack.get(0).unwrap().to_string(), "Hello!");
    /// ```
    pub fn try_replace<'a, T: Into<ListpackEntryInsert<'a>>>(
        &mut self,
        index: usize,
        entry: T,
    ) -> Result {
        self.try_insert_with_placement_internal(InsertionPlacement::Replace(index), entry)
    }
}

/// A macro that creates a new listpack from a list of elements.
/// An analogue of the [`vec!`] macro.
///
/// # Example
///
/// ```
/// use listpack_redis::{listpack, Listpack};
///
/// let listpack: Listpack = listpack!["Hello", "World"];
/// assert_eq!(listpack.len(), 2);
/// assert_eq!(listpack.get(0).unwrap().to_string(), "Hello");
/// assert_eq!(listpack.get(1).unwrap().to_string(), "World");
/// ```
/// Or a more vec-like equivalent:
/// ```
/// use listpack_redis::{listpack, Listpack};
///
/// let listpack: Listpack = listpack![1, 2, 3];
/// assert_eq!(listpack.len(), 3);
/// assert_eq!(listpack[0].to_string(), "1");
/// assert_eq!(listpack[1].to_string(), "2");
/// assert_eq!(listpack[2].to_string(), "3");
/// ```
/// It is also possible to specify different types, contrary to the
/// [`std::convert::From`] trait:
/// ```
/// use listpack_redis::{listpack, Listpack};
///
/// let listpack: Listpack = listpack![1, "Hello", 3];
/// assert_eq!(listpack.len(), 3);
/// assert_eq!(listpack[0].to_string(), "1");
/// assert_eq!(listpack[1].to_string(), "Hello");
/// assert_eq!(listpack[2].to_string(), "3");
/// ```
#[macro_export]
macro_rules! listpack {
    ( $ ( $ x : expr ) , * ) => {
        {
            let mut listpack = $crate::Listpack::default();
            $ (
                listpack.push($x);
            ) *
            listpack
        };
    }
}

#[cfg(test)]
mod tests {
    use crate::allocator::DefaultAllocator;

    use super::*;

    fn create_hello_world_listpack() -> Listpack {
        let mut listpack = Listpack::default();
        listpack.push("Hello");
        listpack.push("World");
        listpack
    }

    #[test]
    fn new_and_empty() {
        let allocator = DefaultAllocator;
        let listpack: Listpack = Listpack::new(allocator);
        drop(listpack);
    }

    #[test]
    fn short_lifetime() {
        let listpack: Listpack = Listpack::default();
        drop(listpack);
    }

    #[test]
    fn long_lifetime() {
        let mut listpack: Listpack = Listpack::default();
        listpack.push("hello");
        listpack.push("world");

        let entry = listpack.get(0).unwrap();
        assert_eq!(entry.to_string(), "hello");

        let entry = &listpack[1];
        assert_eq!(entry.to_string(), "world");

        listpack.replace(1, "rust");
        let entry = &listpack[1];
        assert_eq!(entry.to_string(), "rust");

        listpack.remove(0);
        let entry = &listpack[0];
        assert_eq!(entry.to_string(), "rust");

        listpack.clear();
        assert_eq!(listpack.len(), 0);
        assert!(listpack.is_empty());
    }

    #[test]
    fn header() {
        let mut listpack: Listpack = Listpack::default();

        assert_eq!(listpack.get_header_ref().total_bytes(), 7);
        assert_eq!(listpack.get_header_ref().num_elements(), 0);

        listpack.push("Hello");

        assert_eq!(listpack.get_header_ref().total_bytes(), 14);
        assert_eq!(listpack.get_header_ref().num_elements(), 1);

        listpack.push("World");

        assert_eq!(listpack.get_header_ref().total_bytes(), 21);
        assert_eq!(listpack.get_header_ref().num_elements(), 2);

        listpack.clear();

        assert_eq!(listpack.get_header_ref().total_bytes(), 7);
        assert_eq!(listpack.get_header_ref().num_elements(), 0);

        let header = ListpackHeader {
            total_bytes: 7,
            num_elements: 0,
        };

        let header_ref_from_ptr =
            unsafe { ListpackHeader::from_ptr(&header as *const ListpackHeader as *const u8) };

        assert_eq!(&header, header_ref_from_ptr);
    }

    #[test]
    fn starts_with() {
        let mut listpack: Listpack = Listpack::default();
        listpack.push("Hello");
        listpack.push("World");

        assert!(listpack.starts_with(&["Hello"]));
        assert!(listpack.starts_with(&["Hello", "World"]));
        assert!(!listpack.starts_with(&["Hello", "World", "!"]));
    }

    #[test]
    fn ends_with() {
        let mut listpack: Listpack = Listpack::default();
        listpack.push("Hello");
        listpack.push("World");

        assert!(listpack.ends_with(&["World"]));
        assert!(listpack.ends_with(&["Hello", "World"]));
        assert!(!listpack.ends_with(&["Hello", "World", "!"]));
    }

    #[test]
    fn debug() {
        let listpack = create_hello_world_listpack();
        assert!(!format!("{listpack:?}").is_empty());
        dbg!(&listpack);
    }

    #[test]
    fn display() {
        let listpack = create_hello_world_listpack();
        let display = format!("{listpack}");
        assert!(!display.is_empty());
        println!("{display}");
    }

    #[test]
    fn iter() {
        let mut listpack: Listpack = Listpack::default();
        let mut iter = listpack.iter();

        assert_eq!(iter.next(), None);

        listpack.push("Hello");
        listpack.push("World");

        let mut iter = listpack.iter();

        assert_eq!(
            iter.next()
                .unwrap()
                .data()
                .unwrap()
                .get_small_str()
                .unwrap(),
            "Hello"
        );
        assert_eq!(
            iter.next()
                .unwrap()
                .data()
                .unwrap()
                .get_small_str()
                .unwrap(),
            "World"
        );
        assert_eq!(iter.next(), None);
        assert_eq!(iter.size_hint(), (2, Some(2)));
    }

    #[test]
    fn get() {
        let listpack = create_hello_world_listpack();

        assert_eq!(
            listpack
                .get(0)
                .unwrap()
                .data()
                .unwrap()
                .get_small_str()
                .unwrap(),
            "Hello"
        );
        assert_eq!(
            listpack
                .get(1)
                .unwrap()
                .data()
                .unwrap()
                .get_small_str()
                .unwrap(),
            "World"
        );
        assert_eq!(listpack.get(2), None);
    }

    // These two ways of doing the same must have the same results.
    // The only difference between those is how the elements are
    // located.
    #[test]
    fn get_reversed() {
        let listpack = create_hello_world_listpack();

        assert_eq!(
            listpack.get_internal_entry_ptr_from_start(0),
            listpack.get_internal_entry_ptr_from_end(0)
        );

        assert_eq!(
            listpack.get_internal_entry_ptr_from_start(1),
            listpack.get_internal_entry_ptr_from_end(1)
        );

        assert_eq!(
            listpack.get_internal_entry_ptr_from_start(2),
            listpack.get_internal_entry_ptr_from_end(2)
        );
    }

    #[test]
    fn insert_before() {
        let mut listpack: Listpack = Listpack::default();
        listpack.push("Hello, world!");
        listpack.insert(0, "Hello!");
        assert_eq!(listpack.len(), 2);
        assert_eq!(listpack.get(0).unwrap().to_string(), "Hello!");
        assert_eq!(listpack.get(1).unwrap().to_string(), "Hello, world!");

        let mut listpack: Listpack = Listpack::default();
        listpack.push(1);
        listpack.validate().unwrap();
        listpack.push(2);
        listpack.validate().unwrap();
        listpack.push(3);
        listpack.validate().unwrap();

        listpack.insert(1, 4);
        assert_eq!(listpack.len(), 4);
        assert_eq!(listpack.get(0).unwrap().to_string(), "1");
        assert_eq!(listpack.get(1).unwrap().to_string(), "4");
        assert_eq!(listpack.get(2).unwrap().to_string(), "2");
        assert_eq!(listpack.get(3).unwrap().to_string(), "3");
    }

    #[test]
    fn insert_after() {
        let mut listpack: Listpack = Listpack::default();

        listpack.push("Hello, world!");
        listpack.insert_after(0, "Hello!");

        assert_eq!(listpack.len(), 2);
        assert_eq!(listpack.get(0).unwrap().to_string(), "Hello, world!");
        assert_eq!(listpack.get(1).unwrap().to_string(), "Hello!");
    }

    #[test]
    fn memory_consumption() {
        let mut listpack: Listpack = Listpack::default();
        assert_eq!(listpack.memory_consumption(), 15);

        listpack.push("Hello");
        assert_eq!(listpack.memory_consumption(), 22);

        listpack.push("World");
        assert_eq!(listpack.memory_consumption(), 29);

        listpack.pop();
        assert_eq!(listpack.memory_consumption(), 22);

        listpack.pop();
        assert_eq!(listpack.memory_consumption(), 15);
    }

    #[test]
    fn replace() {
        const SMALLER_STRING: &str = "a";
        const MIDDLE_STRING: &str = "ab";
        const LARGER_STRING: &str = "abc";

        let mut listpack: Listpack = Listpack::default();
        assert_eq!(listpack.memory_consumption(), 15);
        listpack.validate().unwrap();

        listpack.push(MIDDLE_STRING);
        listpack.validate().unwrap();
        assert_eq!(listpack.memory_consumption(), 19);
        assert_eq!(&listpack.get(0).unwrap().to_string(), MIDDLE_STRING);
        assert_eq!(listpack.len(), 1);

        // Downsize to a smaller string.
        listpack.replace(0, SMALLER_STRING);
        assert_eq!(listpack.memory_consumption(), 18);
        assert_eq!(listpack.len(), 1);
        assert_eq!(listpack.get(0).unwrap().to_string(), SMALLER_STRING);
        listpack.validate().unwrap();

        // Upsize to a larger string.
        listpack.replace(0, LARGER_STRING);
        assert_eq!(listpack.memory_consumption(), 20);
        assert_eq!(listpack.len(), 1);
        assert_eq!(listpack.get(0).unwrap().to_string(), LARGER_STRING);
        listpack.validate().unwrap();

        // Replace to the same string.
        listpack.replace(0, LARGER_STRING);
        assert_eq!(listpack.memory_consumption(), 20);
        assert_eq!(listpack.len(), 1);
        assert_eq!(listpack.get(0).unwrap().to_string(), LARGER_STRING);
        listpack.validate().unwrap();
    }

    #[test]
    fn clone() {
        let listpack = create_hello_world_listpack();

        assert_eq!(
            listpack
                .get(0)
                .unwrap()
                .data()
                .unwrap()
                .get_small_str()
                .unwrap(),
            "Hello"
        );
        assert_eq!(
            listpack
                .get(1)
                .unwrap()
                .data()
                .unwrap()
                .get_small_str()
                .unwrap(),
            "World"
        );
        assert_eq!(listpack.get(2), None);

        let cloned = listpack.clone();

        assert_eq!(
            cloned
                .get(0)
                .unwrap()
                .data()
                .unwrap()
                .get_small_str()
                .unwrap(),
            "Hello"
        );

        assert_eq!(
            cloned
                .get(1)
                .unwrap()
                .data()
                .unwrap()
                .get_small_str()
                .unwrap(),
            "World"
        );

        assert_eq!(cloned.get(2), None);

        assert_eq!(listpack.get(0), cloned.get(0));
        assert_eq!(listpack.get(1), cloned.get(1));
        assert_eq!(listpack.get(2), cloned.get(2));
    }

    #[test]
    fn pop() {
        let mut listpack = create_hello_world_listpack();

        assert_eq!(listpack.pop().unwrap().get_str().unwrap(), "World");
        assert_eq!(listpack.pop().unwrap().get_str().unwrap(), "Hello");
        assert_eq!(listpack.pop(), None);
    }

    #[test]
    fn index() {
        let listpack = create_hello_world_listpack();

        assert_eq!(listpack[0].data().unwrap().get_str().unwrap(), "Hello");
        assert_eq!(listpack[1].data().unwrap().get_str().unwrap(), "World");
    }

    #[test]
    fn get_storage_bytes() {
        let listpack: Listpack = Listpack::default();

        assert_eq!(listpack.get_storage_bytes(), 7);
    }

    #[test]
    fn entry_total_bytes() {
        let mut listpack: Listpack = Listpack::default();

        listpack.push("Hello");

        for (length, expected_length) in [
            (5, 7),
            (2usize.pow(7), 132),
            (2usize.pow(12), 4103),
            (2usize.pow(20), 1048584),
        ] {
            let string = "a".repeat(length);
            listpack.replace(0, &string);

            let entry = listpack.get(0).unwrap();
            dbg!(entry);
            let total_bytes = entry.total_bytes();
            assert_eq!(total_bytes, expected_length);
            assert_eq!(entry.to_string(), string);
        }
    }

    #[test]
    fn from_array() {
        let array = ["Hello", "World"];

        let listpack: Listpack = Listpack::from(&["Hello", "World"]);
        assert_eq!(listpack, &array);
    }

    #[test]
    fn from() {
        let listpack1: Listpack = Listpack::from(&["Hello"]);
        let mut listpack2: Listpack = Listpack::default();
        listpack2.push("Hello");

        assert_eq!(listpack1.len(), listpack2.len());
        assert_eq!(listpack1[0].to_string(), "Hello");
        assert_eq!(listpack2[0].to_string(), "Hello");
    }

    #[test]
    fn entry_can_store_and_extract_different_types() {
        let mut listpack: Listpack = Listpack::from(&["Hello"]);

        // Replace the `0`th element with the object of type above
        // and check if it can be extracted correctly and the value
        // is the same as the original one.
        let small_string = "a".repeat(63);
        let medium_string = "a".repeat(4095);
        let large_string = "a".repeat(2usize.pow(32) - 20);
        let objects = [
            ListpackEntryInsert::Integer(127),
            ListpackEntryInsert::String(&small_string),
            ListpackEntryInsert::Integer(4000),
            ListpackEntryInsert::String(&medium_string),
            ListpackEntryInsert::String(&large_string),
            ListpackEntryInsert::Integer(7800),
            ListpackEntryInsert::Integer(4_088_608),
            ListpackEntryInsert::Integer(1_047_483_648),
            ListpackEntryInsert::Integer(4_023_372_036_854_775_807),
            ListpackEntryInsert::Boolean(true),
            ListpackEntryInsert::Boolean(false),
            ListpackEntryInsert::Float(42.23f64),
            ListpackEntryInsert::CustomEmbeddedValue(0),
            ListpackEntryInsert::CustomEmbeddedValue(1),
            ListpackEntryInsert::CustomExtendedValueSlice(&[0, 1, 2, 3]),
        ];

        for object in &objects {
            listpack.replace(0, object.clone());
            let entry = listpack.get(0).unwrap();
            let data = entry.data().unwrap();
            match object {
                ListpackEntryInsert::Integer(integer) => {
                    assert_eq!(
                        data.get_integer().unwrap(),
                        *integer,
                        "with object: {object:?}"
                    );
                }
                ListpackEntryInsert::String(string) => {
                    assert_eq!(data.get_str().unwrap(), *string, "with object: {object:?}");
                }
                ListpackEntryInsert::Boolean(boolean) => {
                    assert_eq!(
                        data.get_bool().unwrap(),
                        *boolean,
                        "with object: {object:?}"
                    );
                }
                ListpackEntryInsert::Float(float) => {
                    assert_eq!(data.get_f64().unwrap(), *float, "with object: {object:?}");
                }
                ListpackEntryInsert::CustomEmbeddedValue(value) => {
                    assert_eq!(
                        data.get_custom_embedded().unwrap(),
                        *value,
                        "with object: {object:?}"
                    );
                }
                ListpackEntryInsert::CustomExtendedValueSlice(value) => {
                    assert_eq!(
                        data.get_custom_extended::<'_, &[u8]>().unwrap(),
                        *value,
                        "with object: {object:?}"
                    );
                }
                ListpackEntryInsert::CustomExtendedValueOwned(value) => {
                    assert_eq!(
                        data.get_custom_extended::<'_, &[u8]>().unwrap(),
                        *value,
                        "with object: {object:?}"
                    );
                }
            }
        }
    }

    #[test]
    fn calculate_element_length_from_the_end() {
        let entry = ListpackEntryInsert::from("Hello");
        let encoded = entry.try_encode().unwrap();
        let ptr = unsafe { encoded.as_ptr().add(encoded.len() - 1) };
        let length = Listpack::<DefaultAllocator>::read_element_length_from_the_end(ptr);

        // - 1 byte for the total element length of the small string.
        // So it occupies actually one byte for the encoding byte and
        // five for the string itself.
        assert_eq!(length, encoded.len());

        let string = "a".repeat(2usize.pow(12));
        let entry = ListpackEntryInsert::from(&string);
        let encoded = entry.try_encode().unwrap();
        let ptr = unsafe { encoded.as_ptr().add(encoded.len() - 1) };
        let length = Listpack::<DefaultAllocator>::read_element_length_from_the_end(ptr);

        // A large string occupies one byte for the encoding, then four
        // next bytes for the string length, and then the string itself.
        assert_eq!(length, encoded.len());
    }

    #[test]
    fn swaps_various() {
        let mut listpack: Listpack = Listpack::default();
        listpack.push("Hello");
        listpack.push("World");
        listpack.push("!");

        listpack.swap(0, 2);

        assert_eq!(listpack.len(), 3);
        assert_eq!(listpack[0].to_string(), "!");
        assert_eq!(listpack[1].to_string(), "World");
        assert_eq!(listpack[2].to_string(), "Hello");
    }

    #[test]
    fn swap_to_bigger() {
        let mut listpack: Listpack = Listpack::default();

        listpack.push("Hello");
        listpack.push("World!");

        unsafe { listpack.swap_unchecked(0, 1) };

        assert_eq!(listpack.len(), 2);

        assert_eq!(listpack[0].to_string(), "World!");
        assert_eq!(listpack[1].to_string(), "Hello");
    }

    #[test]
    fn swap_to_smaller() {
        let mut listpack: Listpack = Listpack::default();

        listpack.push("Hello");
        listpack.push("World!");

        unsafe { listpack.swap_unchecked(0, 1) };

        assert_eq!(listpack.len(), 2);

        assert_eq!(listpack[0].to_string(), "World!");
        assert_eq!(listpack[1].to_string(), "Hello");
    }

    #[test]
    fn swap_to_the_same_length() {
        let mut listpack: Listpack = Listpack::default();

        listpack.push("Hello");
        listpack.push("World");

        unsafe { listpack.swap_unchecked(0, 1) };

        assert_eq!(listpack.len(), 2);

        assert_eq!(listpack[0].to_string(), "World");
        assert_eq!(listpack[1].to_string(), "Hello");
    }

    #[test]
    fn data_end_ptr_is_valid() {
        let listpack: Listpack = Listpack::default();
        let data_end_ptr = listpack.allocation.data_end_ptr();

        assert!(!data_end_ptr.is_null());
        assert_eq!(unsafe { *data_end_ptr }, 0xff);
    }

    #[test]
    fn listpack_allocation_pointer_from_raw_ptr() {
        // let listpack: Listpack = Listpack::default();
        // let ptr = listpack.as_ptr().cast_mut();
        // let allocation_pointer =
        //     unsafe { ListpackAllocationPointer::from_raw_ptr(NonNull::new_unchecked(ptr)) }
        //         .unwrap();

        // assert_eq!(
        //     allocation_pointer.available_bytes(),
        //     listpack.get_header_ref().available_bytes()
        // );
        // assert_eq!(
        //     allocation_pointer.total_bytes(),
        //     listpack.get_header_ref().total_bytes()
        // );
        // assert_eq!(
        //     allocation_pointer.num_elements(),
        //     listpack.get_header_ref().num_elements()
        // );
        // assert_eq!(
        //     allocation_pointer.data_start_ptr(),
        //     listpack.allocation.data_start_ptr()
        // );
        // assert_eq!(
        //     allocation_pointer.data_end_ptr(),
        //     listpack.allocation.data_end_ptr()
        // );
    }

    #[test]
    fn listpack_from_ptr() {
        let listpack: Listpack = Listpack::default();
        let ptr = listpack.as_ptr().cast_mut();
        let listpack_from_ptr = unsafe { Listpack::from_ptr(ptr, DefaultAllocator) };

        assert_eq!(listpack, listpack_from_ptr);
    }
}
