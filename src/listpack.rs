//! The listpack interface.

use std::{
    alloc::Layout,
    fmt::{Debug, Write},
    ops::{Index, RangeBounds},
    ptr::NonNull,
};

use redis_custom_allocator::{CustomAllocator, MemoryConsumption};

use crate::{
    allocator::ListpackAllocator,
    entry::{ListpackEntry, ListpackEntryInsert, ListpackEntryMutable, ListpackEntryRemoved},
    error::{AllocationError, Result},
    iter::{ListpackChunks, ListpackIntoIter, ListpackIter, ListpackWindows},
};

/// The last byte of the allocator for the listpack should always be
/// this value. It is used to detect overflows in the listpack.
const END_MARKER: u8 = 0xFF;

/// The header of the listpack data structure. Can only be obtained
/// from an existing listpack using the [`Listpack::header_ref`] method.
#[repr(C, packed(1))]
#[derive(Debug, Copy, Clone)]
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

    /// Returns the total amount of bytes representing the listpack.
    ///
    /// # Example
    ///
    /// ```
    /// use listpack_redis::Listpack;
    ///
    /// let listpack: Listpack = Listpack::default();
    /// let header = unsafe { listpack.header_ref() };
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
    /// let header = unsafe { listpack.header_ref() };
    /// assert_eq!(header.num_elements(), 0);
    ///
    /// let listpack: Listpack = Listpack::from(&[1, 2, 3]);
    /// let header = unsafe { listpack.header_ref() };
    /// assert_eq!(header.num_elements(), 3);
    pub fn num_elements(&self) -> usize {
        self.num_elements as usize
    }

    /// Returns the amount of bytes available for the listpack to store
    /// new elements.
    pub fn available_bytes(&self) -> usize {
        Self::MAXIMUM_TOTAL_BYTES - self.total_bytes()
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

// impl Deref for ListpackHeaderRef<'_> {
//     type Target = Listpack;

//     fn deref(&self) -> &Self::Target {
//         unsafe { &*(self as *const _ as *const Listpack) }
//     }
// }

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

#[derive(Debug, Copy, Clone)]
struct HeaderPointer(NonNull<[u8]>, Layout);

impl HeaderPointer {
    /// Finds out the layout of the listpack by looking for the end
    /// marker.
    fn from_ptr(ptr: NonNull<[u8]>) -> Result<Self> {
        // TODO: check that we could just check the last byte to be the
        // end marker, instead of scanning the whole listpack.
        unsafe { ptr.as_ref() }
            .iter()
            .enumerate()
            .find_map(|(i, &b)| if b == END_MARKER { Some(i) } else { None })
            .map(|end_index| {
                // An impossible panic scenario, since all the
                // requirements for calling this function are met.
                let layout =
                    Layout::from_size_align(end_index, 1).expect("Could not create layout");

                Self(ptr, layout)
            })
            .ok_or(crate::error::Error::MissingEndMarker)
    }

    fn ptr(&self) -> NonNull<u8> {
        self.0.cast()
    }

    fn layout(&self) -> Layout {
        self.1
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
    const ZERO: Self = Self(0);
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
    allocation: HeaderPointer,
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
    Allocator: CustomAllocator, // Allocator: ListpackAllocator,
                                // <Allocator as CustomAllocator>::Error: Debug,
{
    fn drop(&mut self) {
        unsafe {
            self.allocator
                .deallocate(self.allocation.ptr(), self.allocation.layout())
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
                cloned.as_mut_ptr(),
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

impl<Allocator> Eq for Listpack<Allocator> where Allocator: CustomAllocator {}

impl<'a, T, Allocator> From<&'a [T]> for Listpack<Allocator>
where
    &'a T: Into<ListpackEntryInsert<'a>>,
    ListpackEntryInsert<'a>: std::convert::From<&'a T>,
    Allocator: ListpackAllocator,
    <Allocator as CustomAllocator>::Error: Debug,
{
    fn from(slice: &'a [T]) -> Self {
        let mut listpack = Listpack::with_capacity(slice.len());
        for item in slice {
            let item: ListpackEntryInsert<'a> = ListpackEntryInsert::from(item);
            listpack.push(item);
        }
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
        let mut listpack: Listpack<Allocator> = Listpack::with_capacity(slice.len());
        for item in slice {
            let item: ListpackEntryInsert<'a> = ListpackEntryInsert::from(item);
            listpack.push(item);
        }
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
    /// Returns true if the listpack is homogeneous, that is, all the
    /// elements have the same type.
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
    pub fn is_homogeneous(&self) -> bool {
        if self.is_empty() {
            return true;
        }

        let mut iter = self.iter();
        let first = iter.next().map(|e| e.encoding_type().unwrap()).unwrap();

        iter.all(|e| e.encoding_type().unwrap() == first)
    }

    /// Returns the allocator of the listpack.
    pub fn get_allocator(&self) -> &Allocator {
        &self.allocator
    }

    /// Returns a mutable reference to the allocator of the listpack.
    pub fn get_allocator_mut(&mut self) -> &mut Allocator {
        &mut self.allocator
    }

    /// Returns a raw pointer to the listpack. The returned pointer is
    /// never null.
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
        self.allocation.0.as_ptr().cast()
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
    pub fn as_mut_ptr(&mut self) -> *mut u8 {
        self.allocation.0.as_ptr().cast()
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
    /// # Safety
    ///
    /// The caller must ensure that the header is valid.
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
    /// let listpack: Listpack = Listpack::default();
    /// let header = unsafe { listpack.header_ref() };
    /// assert_eq!(header.num_elements(), 0);
    /// ```
    pub unsafe fn header_ref(&self) -> ListpackHeaderRef {
        // &*(self.ptr.as_ptr() as *const ListpackHeader)
        ListpackHeaderRef(
            (self.as_ptr() as *const ListpackHeader)
                .as_ref()
                .expect("Header is valid"),
        )
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
        let allocation = HeaderPointer::from_ptr(ptr).expect("The listpack is valid.");

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
    /// # Example
    ///
    /// ```
    /// use listpack_redis::Listpack;
    ///
    /// let mut listpack: Listpack = Listpack::default();
    ///
    /// let entry = "Hello, world!".into();
    /// let check = listpack.can_fit_entry(&entry, None);
    /// assert!(check.is_none());
    ///
    /// // The string is too long to be stored in the listpack.
    /// let string = "a".repeat(2usize.pow(32).into());
    /// let entry = (&string).into();
    /// let check = listpack.can_fit_entry(&entry, None);
    /// assert!(check.is_some());
    /// ```
    pub fn can_fit_entry(
        &self,
        entry: &ListpackEntryInsert,
        entry_to_replace: Option<&ListpackEntry>,
    ) -> Option<crate::error::Error> {
        let available_listpack_length = unsafe { self.header_ref().available_bytes() };
        let replacement_length = entry_to_replace
            .map(|e| e.total_bytes())
            .unwrap_or_default();

        match entry {
            ListpackEntryInsert::String(s) => {
                let len_bytes = s.len();

                if len_bytes == 0 {
                    return Some(crate::error::InsertionError::StringIsEmpty.into());
                }

                if len_bytes > std::u32::MAX as usize {
                    return Some(
                        crate::error::InsertionError::ListpackIsFull {
                            current_length: len_bytes,
                            available_listpack_length,
                        }
                        .into(),
                    );
                }

                let encoded_size = entry.full_encoded_size();

                if encoded_size > replacement_length
                    && (encoded_size - replacement_length) > available_listpack_length
                {
                    return Some(
                        crate::error::InsertionError::ListpackIsFull {
                            current_length: encoded_size,
                            available_listpack_length,
                        }
                        .into(),
                    );
                }
            }
            ListpackEntryInsert::Integer(_) => {
                let encoded_size = entry.full_encoded_size();

                if encoded_size > replacement_length
                    && (encoded_size - replacement_length) > available_listpack_length
                {
                    return Some(
                        crate::error::InsertionError::ListpackIsFull {
                            current_length: encoded_size,
                            available_listpack_length,
                        }
                        .into(),
                    );
                }
            }
        }

        None
    }

    /// Returns the first element of the listpack, or [`None`] if it is
    /// empty.
    pub fn first(&self) -> Option<&ListpackEntry> {
        self.get(0)
    }

    /// Returns the last element of the listpack, or [`None`] if it is
    /// empty.
    pub fn last(&self) -> Option<&ListpackEntry> {
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
    /// listpack.push("World");
    ///
    /// unsafe { listpack.swap_unchecked(0, 1) };
    ///
    /// assert_eq!(listpack.len(), 2);
    ///
    /// assert_eq!(listpack[0].to_string(), "World");
    /// assert_eq!(listpack[1].to_string(), "Hello");
    /// ```
    pub unsafe fn swap_unchecked(&mut self, a: usize, b: usize) {
        let a_object = ListpackEntryRemoved::from(self.get(a).expect("Get an entry from listpack"));
        let b_object = ListpackEntryRemoved::from(self.get(b).expect("Get an entry from listpack"));

        let b_object = ListpackEntryInsert::from(&b_object);
        self.replace(a, b_object);

        let a_object = ListpackEntryInsert::from(&a_object);
        self.replace(b, a_object);
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
    pub fn strip_prefix<'a, 'b, T>(&'b self, prefix: &'a [T]) -> Vec<&'b ListpackEntry>
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
    pub fn strip_suffix<'a, 'b, T>(&'b mut self, suffix: &'a [T]) -> Vec<&'b ListpackEntry>
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
        unimplemented!("The method is not implemented yet.")
        // let length = self.len();
        // if at > length {
        //     panic!("The index is out of bounds.")
        // }

        // let mut other = Self::with_capacity_and_allocator(length - at, self.allocator.clone());

        // self.drain(at..(at + length - 1))
        //     .for_each(|entry| other.push(ListpackEntryInsert::from(&entry)));

        // other
    }
}

impl<Allocator> Listpack<Allocator>
where
    Allocator: ListpackAllocator,
    <Allocator as CustomAllocator>::Error: Debug,
    // crate::error::Error: From<<Allocator as CustomAllocator>::Error>,
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
    ) -> Result<HeaderPointer, AllocatorError> {
        let bytes_to_allocate = capacity.0;

        // This is an impossible situation, as the maximum size of the
        // is already checked in the `ListpackCapacity::try_from`.
        let total_bytes: u32 = capacity
            .0
            .try_into()
            .expect("The bytes to allocate fits into the header.");

        // Another impossible scenario, as we have fully satisfy the
        // requirements for this function to avoid returning an error.
        let layout = std::alloc::Layout::from_size_align(bytes_to_allocate, 1)
            .expect("Could not create layout");

        let mut ptr = allocator.allocate(layout)?;

        let mut header_ptr = ptr.cast().as_ptr() as *mut ListpackHeader;

        unsafe {
            *header_ptr = ListpackHeader {
                total_bytes,
                num_elements: 0,
            };
        }

        Ok(HeaderPointer(ptr, layout))
    }

    /// Creates a new listpack with the given capacity (the number of
    /// bytes). There is no notion of "capacity" in the listpack, as it
    /// is a single allocation and all the elements may vary in size.
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
    pub fn with_capacity_and_allocator<T>(capacity: T, allocator: Allocator) -> Self
    where
        T: TryInto<ListpackCapacity>,
    {
        let capacity = match capacity.try_into() {
            Ok(capacity) => capacity,
            Err(e) => panic!("Couldn't convert the provided capacity to  listpack capacity"),
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
    /// Shrinks the capacity of the listpack to fit the number of
    /// elements.
    ///
    /// # Returns
    ///
    /// `true` if the listpack was shrunk, `false` if it wasn't.
    // Commented out, as this method seems redundant: it seems that
    // `shrink_to_fit` is called automatically when the listpack is
    // modified (at least always when something is deleted).
    // ///
    // /// # Example
    // ///
    // /// ```
    // /// use listpack_redis::Listpack;
    // ///
    // /// let mut listpack = Listpack::with_capacity(10);
    // /// assert_eq!(listpack.get_storage_bytes(), 7);
    // /// listpack.push("Hello, world!");
    // /// assert_eq!(listpack.get_storage_bytes(), 22);
    // /// listpack.push("Hello!");
    // /// assert_eq!(listpack.get_storage_bytes(), 30);
    // /// assert!(listpack.shrink_to_fit());
    // /// assert_eq!(listpack.get_storage_bytes(), 22);
    // /// let _ = listpack.pop();
    // /// assert_eq!(listpack.get_storage_bytes(), 20);
    // /// ```
    // ///
    // /// See [`Listpack::get_storage_bytes`] and
    // /// [`Listpack::get_total_bytes`] for more information.
    pub fn shrink_to_fit(&mut self) -> bool {
        unimplemented!("Shrink to fit is not implemented.")
        // if let Some(ptr) =
        //     NonNull::new(unsafe { bindings::lpShrinkToFit(self.allocation.as_ptr()) })
        // {
        //     self.allocation = ptr;
        //     true
        // } else {
        //     false
        // }
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
        unimplemented!("Truncate is not implemented.")
        // if len > self.len() {
        //     return;
        // }

        // let start = len;
        // let length = self.len() - len;
        // let ptr =
        //     unsafe { bindings::lpDeleteRange(self.allocation.as_ptr(), start as _, length as _) };

        // if let Some(ptr) = NonNull::new(ptr) {
        //     self.allocation = ptr;
        // }
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

    // pub fn allocator(&self) -> bindings::lpAlloc {
    //     unsafe { bindings::lpGetAlloc(self.ptr.as_ptr()) }
    // }

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
        // let entry = entry.into();
        // self.ptr = NonNull::new(match entry {
        //     ListpackEntryInsert::String(s) => {
        //         let string_ptr = s.as_ptr() as *mut _;
        //         let len_bytes = s.len();
        //         if len_bytes == 0 {
        //             return;
        //         }

        //         if len_bytes > std::u32::MAX as usize {
        //             panic!("The string is too long to be stored in the listpack.");
        //         }

        //         unsafe { bindings::lpAppend(self.ptr.as_ptr(), string_ptr, len_bytes as _) }
        //     }
        //     ListpackEntryInsert::Integer(n) => unsafe {
        //         bindings::lpAppendInteger(self.ptr.as_ptr(), n)
        //     },
        // })
        // .expect("Appended to listpack");
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
        unimplemented!("Insert is not implemented.")
        // self.insert_internal(index, entry, bindings::LP_BEFORE)
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
        unimplemented!("Try insert is not implemented.")
        // self.try_insert_internal(index, entry, bindings::LP_BEFORE)
    }

    fn insert_internal<'a, T: Into<ListpackEntryInsert<'a>>>(
        &mut self,
        index: usize,
        entry: T,
        location: u32,
    ) {
        self.try_insert_internal(index, entry, location)
            .expect("Insert an element in listpack");
    }

    fn try_insert_internal<'a, T: Into<ListpackEntryInsert<'a>>>(
        &mut self,
        index: usize,
        entry: T,
        location: u32,
    ) -> Result {
        unimplemented!("Try insert internal is not implemented.")
        // let entry = entry.into();

        // let referred_element_ptr =
        //     NonNull::new(unsafe { bindings::lpSeek(self.allocation.as_ptr(), index as _) }).ok_or(
        //         crate::error::InsertionError::IndexOutOfBounds {
        //             index,
        //             length: self.len(),
        //         },
        //     )?;

        // if let Some(e) = self.can_fit_entry(
        //     &entry,
        //     Some(ListpackEntry::ref_from_ptr(referred_element_ptr)),
        // ) {
        //     return Err(e);
        // }

        // let ptr = NonNull::new(match entry {
        //     ListpackEntryInsert::String(s) => {
        //         let string_ptr = s.as_ptr() as *mut _;
        //         let len_bytes = s.len();

        //         unsafe {
        //             bindings::lpInsertString(
        //                 self.allocation.as_ptr(),
        //                 string_ptr,
        //                 len_bytes as _,
        //                 referred_element_ptr.as_ptr(),
        //                 location as _,
        //                 std::ptr::null_mut(),
        //             )
        //         }
        //     }
        //     ListpackEntryInsert::Integer(n) => unsafe {
        //         bindings::lpInsertInteger(
        //             self.allocation.as_ptr(),
        //             n,
        //             referred_element_ptr.as_ptr(),
        //             location as _,
        //             std::ptr::null_mut(),
        //         )
        //     },
        // })
        // .ok_or(crate::error::InsertionError::ListpackIsFull {
        //     current_length: entry.full_encoded_size(),
        //     available_listpack_length: unsafe { self.header_ref().available_bytes() },
        // })?;

        // self.allocation = ptr;

        // Ok(())
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
        unimplemented!("Try push is not implemented.")
        // let entry = entry.into();

        // if let Some(e) = self.can_fit_entry(&entry, None) {
        //     return Err(e);
        // }

        // self.allocation = NonNull::new(match entry {
        //     ListpackEntryInsert::String(s) => {
        //         let string_ptr = s.as_ptr() as *mut _;
        //         let len_bytes = s.len();

        //         unsafe { bindings::lpAppend(self.allocation.as_ptr(), string_ptr, len_bytes as _) }
        //     }
        //     ListpackEntryInsert::Integer(n) => unsafe {
        //         bindings::lpAppendInteger(self.allocation.as_ptr(), n)
        //     },
        // })
        // .expect("Appended to listpack");

        // Ok(())
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
        self.remove_range(index, 1);
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
        F: FnMut(&ListpackEntry) -> bool,
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

    // /// Removes the elements in the specified range from the listpack
    // /// in bulk, returning all removed elements as an iterator.
    // ///
    // /// See [`ListpackDrain`].
    // ///
    // /// # Panics
    // ///
    // /// Panics if the starting point is greater than the end point
    // /// or if the end point is greater than the length of the listpack.
    // ///
    // /// # Example
    // ///
    // /// ```
    // /// use listpack_redis::Listpack;
    // ///
    // /// let mut listpack: Listpack = Listpack::default();
    // /// listpack.push("Hello, world!");
    // /// listpack.push("Hello!");
    // /// listpack.push("World!");
    // /// let removed = listpack.drain(1..3).collect::<Vec<_>>();
    // /// assert_eq!(listpack.len(), 1);
    // /// assert_eq!(removed.len(), 2);
    // /// assert_eq!(removed[0].get_str().unwrap(), "Hello!");
    // /// assert_eq!(removed[1].get_str().unwrap(), "World!");
    // /// ```
    // ///
    // /// Use it the same way as [`Self::clear`], if you want to remove
    // /// all elements from the listpack:
    // ///
    // /// ```
    // /// use listpack_redis::Listpack;
    // ///
    // /// let mut listpack: Listpack = Listpack::default();
    // /// listpack.push("Hello, world!");
    // /// listpack.push("Hello!");
    // /// listpack.push("World!");
    // /// let removed = listpack.drain(..).collect::<Vec<_>>();
    // /// assert!(listpack.is_empty());
    // /// assert_eq!(removed.len(), 3);
    // /// assert_eq!(removed[0].get_str().unwrap(), "Hello, world!");
    // /// assert_eq!(removed[1].get_str().unwrap(), "Hello!");
    // /// assert_eq!(removed[2].get_str().unwrap(), "World!");
    // /// ```
    // ///
    // /// See [std::vec::Vec::drain] for more information.
    // pub fn drain<R>(&mut self, range: R) -> impl std::iter::Iterator<Item = ListpackEntryRemoved>
    // where
    //     R: RangeBounds<usize>,
    // {
    //     unimplemented!("Drain is not implemented.");
    // use std::ops::Bound;

    // let start = match range.start_bound() {
    //     Bound::Included(&start) => start,
    //     Bound::Excluded(&start) => start + 1,
    //     Bound::Unbounded => 0,
    // };

    // let end = match range.end_bound() {
    //     Bound::Included(&end) => end + 1,
    //     Bound::Excluded(&end) => end,
    //     Bound::Unbounded => self.len(),
    // };

    // if start > end {
    //     panic!("The start is greater than the end.")
    // } else if end > self.len() {
    //     panic!("The end is greater than the length of the listpack.")
    // }

    // let length = end - start;
    // let removed_elements = self
    //     .iter()
    //     .skip(start)
    //     .take(length)
    //     .map(ListpackEntryRemoved::from)
    //     .collect::<Vec<_>>();
    // let ptr =
    //     unsafe { bindings::lpDeleteRange(self.allocation.as_ptr(), start as _, length as _) };

    // if let Some(ptr) = NonNull::new(ptr) {
    //     self.allocation = ptr;
    // } else {
    //     panic!("The range is out of bounds.");
    // }

    // removed_elements.into_iter()
    // }

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
        unimplemented!("Pop is not implemented.")
        // let ptr = NonNull::new(unsafe { bindings::lpLast(self.allocation.as_ptr()) });

        // if let Some(ptr) = ptr {
        //     let cloned = ListpackEntryRemoved::from(ptr);
        //     self.allocation = NonNull::new(unsafe {
        //         bindings::lpDelete(self.allocation.as_ptr(), ptr.as_ptr(), std::ptr::null_mut())
        //     })?;
        //     Some(cloned)
        // } else {
        //     None
        // }
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

    // // TODO: doc
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
    pub fn get(&self, index: usize) -> Option<&ListpackEntry> {
        self.get_internal_entry_ptr(index)
            .map(ListpackEntry::ref_from_ptr)
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
            let entry = ListpackEntry::ref_from_ptr(ptr);
            ListpackEntryMutable::new(self, entry, index)
        })
    }
}

impl<Allocator> Index<usize> for Listpack<Allocator>
where
    Allocator: CustomAllocator,
{
    type Output = ListpackEntry;

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
    /// Returns a pointer to the listpack's entry at the given index.
    fn get_internal_entry_ptr(&self, index: usize) -> Option<NonNull<u8>> {
        unimplemented!("Get internal entry pointer is not implemented.")
        // NonNull::new(unsafe { bindings::lpSeek(self.allocation.as_ptr(), index as _) })
    }

    /// Returns a pointer to the listpack's header.
    fn get_header_ref<'a>(&'a self) -> ListpackHeaderRef<'a> {
        unsafe { self.header_ref() }
    }

    /// Returns the amount of bytes used by the listpack to store the
    /// elements.
    ///
    /// # Example
    ///
    /// ```
    /// use listpack_redis::Listpack;
    ///
    /// let mut listpack: Listpack = Listpack::with_capacity(10);
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

    // Commented out, as listpack C API doesn't provide a method to
    // return the total bytes used by the listpack (including the
    // capacity).
    // /// Returns the total number of bytes used by the listpack,
    // /// not just the storage bytes (the actual elements), but also the
    // /// memory allocated for the capacity.
    // ///
    // /// # Example
    // ///
    // /// ```
    // /// use listpack_redis::Listpack;
    // ///
    // /// let mut listpack = Listpack::with_capacity(10);
    // /// assert_eq!(listpack.get_total_bytes(), 7);
    // /// assert_eq!(listpack.get_storage_bytes(), 7);
    // /// listpack.push("Hello, world!");
    // /// assert_eq!(listpack.get_storage_bytes(), 22);
    // /// assert_eq!(listpack.get_total_bytes(), 22);
    // /// ```
    // pub fn get_total_bytes(&self) -> usize {
    //     unsafe { self.header_ref() }.total_bytes()
    // }

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
    /// listpack.remove_range(1, 2);
    /// assert_eq!(listpack.len(), 1);
    /// assert_eq!(listpack.get(0).unwrap().to_string(), "Hello, world!");
    /// ```
    pub fn remove_range(&mut self, start: usize, length: usize) {
        unimplemented!("Remove range is not implemented.")
        // if start + length > self.len() {
        //     panic!("The range is out of bounds.");
        // }

        // let ptr =
        //     unsafe { bindings::lpDeleteRange(self.allocation.as_ptr(), start as _, length as _) };

        // if let Some(ptr) = NonNull::new(ptr) {
        //     self.allocation = ptr;
        // } else {
        //     panic!("The delete range failed.");
        // }
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
        unimplemented!("Insert after is not implemented.")
        // self.insert_internal(index, entry, bindings::LP_AFTER)
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
        unimplemented!("Try insert after is not implemented.")
        // self.try_insert_internal(index, entry, bindings::LP_AFTER)
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
    /// assert_eq!(listpack.get(0).unwrap().to_string(), "Hello!");
    /// ```
    pub fn replace<'a, T: Into<ListpackEntryInsert<'a>>>(&mut self, index: usize, entry: T) {
        unimplemented!("Replace is not implemented.")
        // self.insert_internal(index, entry, bindings::LP_REPLACE)
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
        unimplemented!("Try replace is not implemented.")
        // self.try_insert_internal(index, entry, bindings::LP_REPLACE)
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
    use super::*;

    fn create_hello_world_listpack() -> Listpack {
        let mut listpack = Listpack::default();
        listpack.push("Hello");
        listpack.push("World");
        listpack
    }

    #[test]
    fn short_lifetime() {
        let listpack: Listpack = Listpack::default();
        drop(listpack);
    }

    #[test]
    fn header() {
        let mut listpack: Listpack = Listpack::default();

        unsafe {
            assert_eq!(listpack.header_ref().total_bytes(), 7);
            assert_eq!(listpack.header_ref().num_elements(), 0);
        }

        listpack.push("Hello");

        unsafe {
            assert_eq!(listpack.header_ref().total_bytes(), 14);
            assert_eq!(listpack.header_ref().num_elements(), 1);
        }

        listpack.push("World");

        unsafe {
            assert_eq!(listpack.header_ref().total_bytes(), 21);
            assert_eq!(listpack.header_ref().num_elements(), 2);
        }

        listpack.clear();

        unsafe {
            assert_eq!(listpack.header_ref().total_bytes(), 7);
            assert_eq!(listpack.header_ref().num_elements(), 0);
        }
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
            (2usize.pow(7), 130),
            (2usize.pow(12), 4101),
            (2usize.pow(20), 1048581),
        ] {
            // A single ASCII-character repeated (2^7 + 1) times, to test
            // the 14-bit encoding (2 bytes for the length).
            let string = "a".repeat(length);
            listpack.replace(0, &string);

            let entry = listpack.get(0).unwrap();
            let total_bytes = entry.total_bytes();
            assert_eq!(total_bytes, expected_length);
            assert_eq!(entry.to_string(), string);
        }
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
        ];

        for object in objects.iter() {
            listpack.replace(0, *object);
            let entry = listpack.get(0).unwrap();
            let data = entry.data().unwrap();
            match object {
                ListpackEntryInsert::Integer(integer) => {
                    assert_eq!(data.get_integer().unwrap(), *integer);
                }
                ListpackEntryInsert::String(string) => {
                    assert_eq!(data.get_str().unwrap(), *string);
                }
            }
        }
    }
}
