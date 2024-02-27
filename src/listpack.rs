//! The listpack interface.

use std::{fmt::Debug, ptr::NonNull};

use crate::bindings;

// #[derive(Debug, Copy, Clone)]
// enum ListpackEntryType {
//     String,
//     Integer,
// }

#[derive(Debug, Copy, Clone)]
pub struct ListpackEntryRaw {
    ptr: NonNull<u8>,
    len: usize,
}

#[derive(Debug, Clone)]
pub enum ListpackEntry {
    String(String),
    Integer(i64),
}

impl From<NonNull<u8>> for ListpackEntry {
    fn from(ptr: NonNull<u8>) -> Self {
        unimplemented!()
    }
}

impl From<String> for ListpackEntry {
    fn from(s: String) -> Self {
        Self::String(s)
    }
}

macro_rules! impl_listpack_entry_from_number {
    ($($t:ty),*) => {
        $(
            impl From<$t> for ListpackEntry {
                fn from(n: $t) -> Self {
                    Self::Integer(n as i64)
                }
            }

            impl TryFrom<ListpackEntry> for $t {
                type Error = ();

                fn try_from(n: ListpackEntry) -> Result<Self, Self::Error> {
                    match n {
                        ListpackEntry::Integer(u) => Ok(u as $t),
                        _ => Err(()),
                    }
                }
            }
        )*
    };
}

impl_listpack_entry_from_number!(i8, i16, i32, i64, u8, u16, u32, u64);

impl From<&str> for ListpackEntry {
    fn from(s: &str) -> Self {
        Self::String(s.to_string())
    }
}

impl From<&String> for ListpackEntry {
    fn from(s: &String) -> Self {
        Self::String(s.clone())
    }
}

/// The listpack data structure.
pub struct Listpack {
    ptr: NonNull<u8>,
}

impl Default for Listpack {
    fn default() -> Self {
        Self::with_capacity(0)
    }
}

impl Debug for Listpack {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // let elements = self.iter().collect()
        f.debug_struct("Listpack")
            // .field("listpack_ptr", &self.listpack_ptr)
            // TODO: output the pointer and elements as an array.
            .finish()
    }
}

impl Drop for Listpack {
    fn drop(&mut self) {
        unsafe { bindings::lpFree(self.ptr.as_ptr()) }
    }
}

impl Clone for Listpack {
    fn clone(&self) -> Self {
        let ptr = unsafe { bindings::lpDup(self.ptr.as_ptr()) };

        Self {
            ptr: NonNull::new(ptr).expect("The listpack clones fine."),
        }
    }
}

/// The [`Vec`]-like interface for the listpack.
impl Listpack {
    /// Returns a new listpack.
    pub fn new() -> Self {
        Self::with_capacity(0)
    }

    /// Creates a new listpack with the given capacity.
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            ptr: NonNull::new(unsafe { bindings::lpNew(capacity) })
                .expect("could not create listpack"),
        }
    }

    /// Returns the number of elements of this listpack.
    pub fn len(&self) -> usize {
        unsafe { bindings::lpLength(self.ptr.as_ptr()) as usize }
    }

    /// Shrinks the capacity of the listpack to fit the number of
    /// elements.
    pub fn shrink_to_fit(&mut self) -> bool {
        if let Some(ptr) = NonNull::new(unsafe { bindings::lpShrinkToFit(self.ptr.as_ptr()) }) {
            self.ptr = ptr;
            true
        } else {
            false
        }
    }

    /// Truncates the listpack, keeping only the first `len` elements.
    pub fn truncate(&mut self, len: usize) {
        if len > self.len() {
            return;
        }

        let start = len;
        let length = self.len() - len;
        let ptr = unsafe { bindings::lpDeleteRange(self.ptr.as_ptr(), start as _, length as _) };

        if let Some(ptr) = NonNull::new(ptr) {
            self.ptr = ptr;
        }
    }

    /// Returns a raw pointer to the listpack.
    pub fn as_ptr(&self) -> *const u8 {
        self.ptr.as_ptr()
    }

    /// Returns a mutable raw pointer to the listpack.
    pub fn as_mut_ptr(&mut self) -> *mut u8 {
        self.ptr.as_ptr()
    }

    /// Clears the entire listpack.
    pub fn clear(&mut self) {
        self.truncate(self.len())
    }

    // pub fn allocator(&self) -> bindings::lpAlloc {
    //     unsafe { bindings::lpGetAlloc(self.ptr.as_ptr()) }
    // }

    /// Appends an element to the back of the listpack.
    ///
    /// # Panics
    ///
    /// Panics if the string is too long to be stored in the listpack.
    pub fn push<T: Into<ListpackEntry>>(&mut self, entry: ListpackEntry) {
        match entry {
            ListpackEntry::String(mut s) => {
                let string_ptr = s.as_mut_ptr();
                let len = s.len();
                if len == 0 {
                    return;
                } else if len > std::u32::MAX as usize {
                    panic!("The string is too long to be stored in the listpack.");
                }
                unsafe { bindings::lpAppend(self.ptr.as_ptr(), string_ptr, len as _) };
            }
            ListpackEntry::Integer(n) => {
                unsafe { bindings::lpAppendInteger(self.ptr.as_ptr(), n) };
            }
        }
    }

    /// Removes the last element from the listpack and returns it, or
    /// [`None`] if it is empty.
    pub fn pop(&mut self) -> Option<ListpackEntry> {
        let mut ptr = NonNull::new(unsafe { bindings::lpLast(self.ptr.as_ptr()) });

        if let Some(ptr) = ptr {
            unsafe { bindings::lpDelete(self.ptr.as_ptr(), ptr.as_ptr(), std::ptr::null_mut()) };
            Some(ListpackEntry::from(ptr))
        } else {
            None
        }
    }

    /// Returns an iterator over the elements of the listpack.
    pub fn iter(&self) -> ListpackIter {
        ListpackIter {
            listpack: self,
            index: 0,
        }
    }

    /// Returns an iterator over the elements of the listpack.
    pub fn iter_mut(&self) -> ListpackIterMut {
        ListpackIterMut {
            listpack: self,
            index: 0,
        }
    }
}

/// Specific methods for this list-pack implementation.
impl Listpack {
    /// Returns the amount of bytes used by the listpack to store the
    /// elements.
    pub fn get_storage_bytes(&self) -> usize {
        unsafe { bindings::lpBytes(self.ptr.as_ptr()) }
    }
}

/// An iterator over the elements of a listpack.
pub struct ListpackIter<'a> {
    listpack: &'a Listpack,
    index: usize,
}

impl Iterator for ListpackIter<'_> {
    type Item = String;

    fn next(&mut self) -> Option<Self::Item> {
        let mut len = 0;
        let mut ptr = std::ptr::null_mut();
        unsafe {
            bindings::lpGet(self.listpack.ptr.as_ptr(), self.index, &mut ptr, &mut len);
        }
        if ptr.is_null() {
            None
        } else {
            self.index += 1;
            Some(unsafe { String::from_raw_parts(ptr as *mut u8, len, len) })
        }
    }
}

/// A mutable iterator over the elements of a listpack.
pub struct ListpackIterMut<'a> {
    listpack: &'a Listpack,
    index: usize,
}
