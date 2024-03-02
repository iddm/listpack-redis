//! The listpack interface.

use std::{
    fmt::Debug,
    marker::PhantomData,
    mem::ManuallyDrop,
    ops::{Deref, Index},
    ptr::NonNull,
};

use crate::bindings;
use crate::error::Result;

/// The header of the listpack data structure.
#[repr(C)]
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
    /// Returns the total amount of bytes representing the listpack.
    pub fn total_bytes(&self) -> usize {
        self.total_bytes as usize
    }

    /// Returns the total number of elements the listpack holds.
    pub fn num_elements(&self) -> usize {
        self.num_elements as usize
    }

    /// Convert the header into a listpack.
    ///
    /// To do so, the header object must be located at the beginning of
    /// the listpack which is already allocated.
    ///
    /// # Safety
    ///
    /// This function is unsafe because it dereferences a raw pointer.
    /// It is the caller's responsibility to verify the location of the
    /// header and the validity of the listpack.
    ///
    /// # Panics
    ///
    /// Panics if the header is not valid.
    pub unsafe fn into_listpack(self) -> Listpack {
        Listpack {
            ptr: NonNull::new(&self as *const _ as *mut u8).expect("The header is valid."),
        }
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

impl Deref for ListpackHeaderRef<'_> {
    type Target = Listpack;

    fn deref(&self) -> &Self::Target {
        unsafe { &*(self as *const _ as *const Listpack) }
    }
}

impl ListpackHeaderRef<'_> {
    /// Returns the total amount of bytes representing the listpack.
    pub fn total_bytes(&self) -> usize {
        self.0.total_bytes as usize
    }

    /// Returns the total number of elements the listpack holds.
    pub fn num_elements(&self) -> usize {
        self.0.num_elements as usize
    }

    /// Convert the header into a listpack.
    ///
    /// To do so, the header object must be located at the beginning of
    /// the listpack which is already allocated.
    ///
    /// # Safety
    ///
    /// This function is unsafe because it dereferences a raw pointer.
    /// It is the caller's responsibility to verify the location of the
    /// header and the validity of the listpack.
    ///
    /// # Panics
    ///
    /// Panics if the header is not valid.
    pub unsafe fn into_listpack(self) -> Listpack {
        Listpack {
            ptr: NonNull::new(&self as *const _ as *mut u8).expect("The header is valid."),
        }
    }
}

/// The subencoding type of a listpack entry.
/// The subencoding is the encoding of a listpack entry, which is
/// more complex than the simple encoding types, meaning it can't fit
/// into a single byte of the header's encoding type and requires
/// additional bytes to represent the entry, the data block.
#[repr(u8)]
#[derive(Debug, Copy, Clone)]
pub enum ListpackEntrySubencodingType {
    /// A 13-bit signed integer: the higher three bits are `110`, and
    /// the following 13 bits are the integer itself.
    SignedInteger13Bit = 0b11000000,
    /// A string with length up to `4095` bytes: the higher four bits
    /// are `1110`, the lower four bytes are the length of the string.
    MediumString = 0b11100000,
    /// A large string with up to `2^32 - 1` bytes: the higher four bits
    /// are `1111`, the lower four bytes are always zero, designating
    /// the large string encoding. After the encoding type, the
    /// following four bytes are the length of the string (within the
    /// data block), and then the string data itself.
    LargeString = 0b11110000,
    /// A 16-bit signed integer: the higher four bits are `1111`, and
    /// the following four bits are `0001`. The following two bytes of
    /// the data block represent a 16 bits signed integer.
    SignedInteger16Bit = 0b11110001,
    /// A 24-bit signed integer: the higher four bits are `1111`, and
    /// the following four bits are `0010`. The following three bytes
    /// of the data block represent a 24 bits signed integer.
    SignedInteger24Bit = 0b11110010,
    /// A 32-bit signed integer: the higher four bits are `1111`, and
    /// the following four bits are `0011`. The following four bytes of
    /// the data block represent a 32 bits signed integer.
    SignedInteger32Bit = 0b11110011,
    /// A 64-bit signed integer: the higher four bits are `1111`, and
    /// the following four bits are `0100`. The following eight bytes of
    /// the data block represent a 64 bits signed integer.
    SignedInteger64Bit = 0b11110100,
}

impl TryFrom<u8> for ListpackEntrySubencodingType {
    type Error = crate::error::Error;

    fn try_from(encoding_byte: u8) -> Result<Self> {
        match encoding_byte {
            0b11000000 => Ok(Self::SignedInteger13Bit),
            0b11100000 => Ok(Self::MediumString),
            0b11110000 => Ok(Self::LargeString),
            0b11110001 => Ok(Self::SignedInteger16Bit),
            0b11110010 => Ok(Self::SignedInteger24Bit),
            0b11110011 => Ok(Self::SignedInteger32Bit),
            0b11110100 => Ok(Self::SignedInteger64Bit),
            _ => Err(crate::error::Error::UnknownEncodingType { encoding_byte }),
        }
    }
}

/// The encoding type of a listpack entry.
#[repr(u8)]
#[derive(Debug, Copy, Clone)]
pub enum ListpackEntryEncodingType {
    /// A small integer is encoded within the byte itself (the
    /// remaining 7 bits, meaning the values from 0 to 127 (a 7-bit
    /// unsigned integer)).
    SmallUnsignedInteger = 0b00000000,
    /// A small string is encoded within the data block (the one
    /// following the encoding byte). The length of such a small string
    /// is encoded within the 6 lower bits of the encoding byte, so the
    /// maximum length of a small string is 63 bytes (ASCII characters).
    SmallString = 0b10000000,
    /// If the higher 2 bits of the encoding byte are 11, the entry is
    /// of a complex type, which may only be known after parsing the
    /// following lower bits of the encoding type.
    ComplexType(ListpackEntrySubencodingType),
}

impl TryFrom<u8> for ListpackEntryEncodingType {
    type Error = crate::error::Error;

    fn try_from(encoding_byte: u8) -> Result<Self> {
        // Compare the highest two bits of the encoding byte, then if
        // those aren't matched, delegate to the subencoding type.
        match encoding_byte & 0b11000000 {
            // If the first bit is unset, it's a small unsigned integer.
            0b00000000 | 0b01000000 => Ok(Self::SmallUnsignedInteger),
            // If the first bit is set, following the second bit which
            // is unset, it's a small string.
            0b10000000 => Ok(Self::SmallString),
            // If the first two bits are set, it's a complex type.
            0b11000000 => Ok(Self::ComplexType(ListpackEntrySubencodingType::try_from(
                encoding_byte,
            )?)),
            // Ideally, this branch should never be reached.
            _ => Err(crate::error::Error::UnknownEncodingType { encoding_byte }),
        }
    }
}

/// The meaning of the encoding byte.
#[derive(Debug, Copy, Clone)]
pub enum ListpackEntryData<'a> {
    /// See [`ListpackEntryEncodingType::SmallUnsignedInteger`].
    SmallUnsignedInteger(u8),
    /// See [`ListpackEntryEncodingType::SmallString`].
    SmallString(&'a str),
    /// See [`ListpackEntrySubencodingType::SignedInteger13Bit`].
    SignedInteger13Bit(i16),
    /// See [`ListpackEntrySubencodingType::MediumString`].
    MediumString(&'a str),
    /// See [`ListpackEntrySubencodingType::LargeString`].
    LargeString(&'a str),
    /// See [`ListpackEntrySubencodingType::SignedInteger16Bit`].
    SignedInteger16Bit(i16),
    /// See [`ListpackEntrySubencodingType::SignedInteger24Bit`].
    SignedInteger24Bit(i32),
    /// See [`ListpackEntrySubencodingType::SignedInteger32Bit`].
    SignedInteger32Bit(i32),
    /// See [`ListpackEntrySubencodingType::SignedInteger64Bit`].
    SignedInteger64Bit(i64),
}

impl ListpackEntryData<'_> {
    /// Returns the encoding type of the entry.
    pub fn encoding_type(&self) -> ListpackEntryEncodingType {
        match self {
            ListpackEntryData::SmallUnsignedInteger(_) => {
                ListpackEntryEncodingType::SmallUnsignedInteger
            }
            ListpackEntryData::SmallString(_) => ListpackEntryEncodingType::SmallString,
            ListpackEntryData::SignedInteger13Bit(_) => ListpackEntryEncodingType::ComplexType(
                ListpackEntrySubencodingType::SignedInteger13Bit,
            ),
            ListpackEntryData::MediumString(_) => {
                ListpackEntryEncodingType::ComplexType(ListpackEntrySubencodingType::MediumString)
            }
            ListpackEntryData::LargeString(_) => {
                ListpackEntryEncodingType::ComplexType(ListpackEntrySubencodingType::LargeString)
            }
            ListpackEntryData::SignedInteger16Bit(_) => ListpackEntryEncodingType::ComplexType(
                ListpackEntrySubencodingType::SignedInteger16Bit,
            ),
            ListpackEntryData::SignedInteger24Bit(_) => ListpackEntryEncodingType::ComplexType(
                ListpackEntrySubencodingType::SignedInteger24Bit,
            ),
            ListpackEntryData::SignedInteger32Bit(_) => ListpackEntryEncodingType::ComplexType(
                ListpackEntrySubencodingType::SignedInteger32Bit,
            ),
            ListpackEntryData::SignedInteger64Bit(_) => ListpackEntryEncodingType::ComplexType(
                ListpackEntrySubencodingType::SignedInteger64Bit,
            ),
        }
    }

    /// Attempts to extract a small unsigned integer from the entry.
    pub fn get_u7(&self) -> Option<u8> {
        match self {
            ListpackEntryData::SmallUnsignedInteger(u) => Some(*u),
            _ => None,
        }
    }

    /// Attempts to extract a small string from the entry.
    pub fn get_small_str(&self) -> Option<&str> {
        match self {
            ListpackEntryData::SmallString(s) => Some(s),
            _ => None,
        }
    }

    /// Attempts to extract a signed 13-bit integer from the entry.
    pub fn get_i13(&self) -> Option<i16> {
        match self {
            ListpackEntryData::SignedInteger13Bit(i) => Some(*i),
            _ => None,
        }
    }

    /// Attempts to extract a medium string from the entry.
    pub fn get_medium_str(&self) -> Option<&str> {
        match self {
            ListpackEntryData::MediumString(s) => Some(s),
            _ => None,
        }
    }

    /// Attempts to extract a large string from the entry.
    pub fn get_large_str(&self) -> Option<&str> {
        match self {
            ListpackEntryData::LargeString(s) => Some(s),
            _ => None,
        }
    }

    /// Attempts to extract any kind of string from the entry.
    pub fn get_str(&self) -> Option<&str> {
        match self {
            ListpackEntryData::SmallString(s) => Some(s),
            ListpackEntryData::MediumString(s) => Some(s),
            ListpackEntryData::LargeString(s) => Some(s),
            _ => None,
        }
    }

    /// Attempts to extract a signed 16-bit integer from the entry.
    pub fn get_i16(&self) -> Option<i16> {
        match self {
            ListpackEntryData::SignedInteger16Bit(i) => Some(*i),
            _ => None,
        }
    }

    /// Attempts to extract a signed 24-bit integer from the entry.
    pub fn get_i24(&self) -> Option<i32> {
        match self {
            ListpackEntryData::SignedInteger24Bit(i) => Some(*i),
            _ => None,
        }
    }

    /// Attempts to extract a signed 32-bit integer from the entry.
    pub fn get_i32(&self) -> Option<i32> {
        match self {
            ListpackEntryData::SignedInteger32Bit(i) => Some(*i),
            _ => None,
        }
    }

    /// Attempts to extract a signed 64-bit integer from the entry.
    pub fn get_i64(&self) -> Option<i64> {
        match self {
            ListpackEntryData::SignedInteger64Bit(i) => Some(*i),
            _ => None,
        }
    }

    /// Returns `true` if the entry is a small unsigned integer.
    pub fn is_u7(&self) -> bool {
        self.get_u7().is_some()
    }

    /// Returns `true` if the entry is a small string.
    pub fn is_small_str(&self) -> bool {
        self.get_small_str().is_some()
    }

    /// Returns `true` if the entry is a signed 13-bit integer.
    pub fn is_i13(&self) -> bool {
        self.get_i13().is_some()
    }

    /// Returns `true` if the entry is a medium string.
    pub fn is_medium_str(&self) -> bool {
        self.get_medium_str().is_some()
    }

    /// Returns `true` if the entry is a large string.
    pub fn is_large_str(&self) -> bool {
        self.get_large_str().is_some()
    }

    /// Returns `true` if the entry is a signed 16-bit integer.
    pub fn is_i16(&self) -> bool {
        self.get_i16().is_some()
    }

    /// Returns `true` if the entry is a signed 24-bit integer.
    pub fn is_i24(&self) -> bool {
        self.get_i24().is_some()
    }

    /// Returns `true` if the entry is a signed 32-bit integer.
    pub fn is_i32(&self) -> bool {
        self.get_i32().is_some()
    }

    /// Returns `true` if the entry is a signed 64-bit integer.
    pub fn is_i64(&self) -> bool {
        self.get_i64().is_some()
    }
}

impl From<ListpackEntryData<'_>> for ListpackEntryEncodingType {
    fn from(data: ListpackEntryData) -> Self {
        data.encoding_type()
    }
}

macro_rules! impl_listpack_entry_data_from_number {
    ($($t:ty),*) => {
        $(
            impl From<$t> for ListpackEntryData<'_> {
                fn from(n: $t) -> Self {
                    let n = n as i64;

                    if (0..=127).contains(&n) {
                        Self::SmallUnsignedInteger(n as u8)
                    } else if (-4096..=4095).contains(&n) {
                        Self::SignedInteger13Bit(n as i16)
                    } else if (-32768..=32767).contains(&n) {
                        Self::SignedInteger16Bit(n as i16)
                    } else if (-8388608..=8388607).contains(&n) {
                        Self::SignedInteger24Bit(n as i32)
                    } else if (-2147483648..=2147483647).contains(&n) {
                        Self::SignedInteger32Bit(n as i32)
                    } else {
                        Self::SignedInteger64Bit(n)
                    }
                }
            }

            impl TryFrom<ListpackEntryData<'_>> for $t {
                type Error = crate::error::Error;

                fn try_from(n: ListpackEntryData<'_>) -> Result<Self> {
                    let min = <$t>::MIN as i64;
                    let max = <$t>::MAX as i64;

                    let range = min..=max;

                    Ok(match n {
                        ListpackEntryData::SmallUnsignedInteger(u) => if range.contains(&(u as i64)) {
                            u as $t
                        } else {
                            return Err(crate::error::Error::UnsupportedNumberDataTypeBitWidth {
                                bit_width: std::mem::size_of::<$t>() as u8 * 8,
                            });
                        },
                        ListpackEntryData::SignedInteger13Bit(i) => if range.contains(&(i as i64)) {
                            i as $t
                        } else {
                            return Err(crate::error::Error::UnsupportedNumberDataTypeBitWidth {
                                bit_width: std::mem::size_of::<$t>() as u8 * 8,
                            });
                        },
                        ListpackEntryData::SignedInteger16Bit(i) => if range.contains(&(i as i64)) {
                            i as $t
                        } else {
                            return Err(crate::error::Error::UnsupportedNumberDataTypeBitWidth {
                                bit_width: std::mem::size_of::<$t>() as u8 * 8,
                            });
                        },
                        ListpackEntryData::SignedInteger24Bit(i) => if range.contains(&(i as i64)) {
                            i as $t
                        } else {
                            return Err(crate::error::Error::UnsupportedNumberDataTypeBitWidth {
                                bit_width: std::mem::size_of::<$t>() as u8 * 8,
                            });
                        },
                        ListpackEntryData::SignedInteger64Bit(i) => if range.contains(&(i as i64)) {
                            i as $t
                        } else {
                            return Err(crate::error::Error::UnsupportedNumberDataTypeBitWidth {
                                bit_width: std::mem::size_of::<$t>() as u8 * 8,
                            });
                        }
                        _ => return Err(crate::error::Error::UnsupportedNumberDataTypeBitWidth {
                            bit_width: std::mem::size_of::<$t>() as u8 * 8,
                        }),
                    })
                }
            }
        )*
    };
}

impl_listpack_entry_data_from_number!(i8, i16, i32, i64, u8, u16, u32, u64);

impl<'a> From<&'a str> for ListpackEntryData<'a> {
    fn from(s: &'a str) -> Self {
        let len = s.len();
        if len <= 63 {
            Self::SmallString(s)
        } else if len <= 4095 {
            Self::MediumString(s)
        } else {
            Self::LargeString(s)
        }
    }
}

impl<'a> From<&'a String> for ListpackEntryData<'a> {
    fn from(s: &'a String) -> Self {
        Self::from(s.as_str())
    }
}

/// The raw representation of a listpack entry. This is a transparent,
/// zero-sized object, which designates a reference to the actual
/// listpack entry.
#[repr(transparent)]
#[derive(Debug)]
pub struct ListpackEntry(());

impl ListpackEntry {
    /// Returns the pointer to the entry.
    pub fn as_ptr(&self) -> *const u8 {
        self as *const _ as *const u8
    }

    /// Returns the mutable pointer to the entry.
    pub fn as_mut_ptr(&mut self) -> *mut u8 {
        self as *mut _ as *mut u8
    }

    /// Returns the byte (raw) representation of the encoding type.
    pub fn get_encoding_type_raw(&self) -> u8 {
        // unsafe { *self.ptr.as_ref() }
        // unsafe { *self.ptr.as_ptr() }
        unsafe { std::ptr::read(self.as_ptr()) }
    }

    /// Returns the encoding type of the entry, parsed from the byte.
    pub fn encoding_type(&self) -> Result<ListpackEntryEncodingType> {
        ListpackEntryEncodingType::try_from(self.get_encoding_type_raw())
    }

    /// Returns the dedicated data block of the entry, if there is one.
    /// An entry may or may not have a data block, depending on the
    /// encoding type.
    pub fn get_data_raw(&self) -> Option<&[u8]> {
        // Depending on the encoding type, the data block may or may not
        // be present. If it is present, it is located after the encoding
        // type byte.
        let encoding_type = self.encoding_type().ok()?;
        let encoding_type_byte = self.get_encoding_type_raw();

        match encoding_type {
            ListpackEntryEncodingType::SmallUnsignedInteger => None,
            ListpackEntryEncodingType::SmallString => {
                let len = (encoding_type_byte & 0b00111111) as usize;
                let data = unsafe {
                    let ptr = (self as *const Self as *const u8).add(1);
                    std::slice::from_raw_parts(ptr, len)
                };
                Some(data)
            }
            ListpackEntryEncodingType::ComplexType(subencoding_type) => match subencoding_type {
                ListpackEntrySubencodingType::SignedInteger13Bit => {
                    let data = unsafe {
                        let ptr = (self as *const Self as *const u8).add(1);
                        std::slice::from_raw_parts(ptr, 2)
                    };
                    Some(data)
                }
                ListpackEntrySubencodingType::MediumString => {
                    let data = unsafe {
                        let ptr = (self as *const Self as *const u8).add(1);
                        let len = ((*ptr as usize) << 8) | (*ptr.add(1) as usize);
                        let ptr = ptr.add(2);
                        std::slice::from_raw_parts(ptr, len)
                    };
                    Some(data)
                }
                ListpackEntrySubencodingType::LargeString => {
                    let data = unsafe {
                        let ptr = (self as *const Self as *const u8).add(1);
                        let len = ((*ptr as usize) << 24)
                            | ((*ptr.add(1) as usize) << 16)
                            | ((*ptr.add(2) as usize) << 8)
                            | (*ptr.add(3) as usize);
                        let ptr = ptr.add(4);
                        std::slice::from_raw_parts(ptr, len)
                    };
                    Some(data)
                }
                ListpackEntrySubencodingType::SignedInteger16Bit => {
                    let data = unsafe {
                        let ptr = (self as *const Self as *const u8).add(1);
                        std::slice::from_raw_parts(ptr, 2)
                    };
                    Some(data)
                }
                ListpackEntrySubencodingType::SignedInteger24Bit => {
                    let data = unsafe {
                        let ptr = (self as *const Self as *const u8).add(1);
                        std::slice::from_raw_parts(ptr, 3)
                    };
                    Some(data)
                }
                ListpackEntrySubencodingType::SignedInteger32Bit => {
                    let data = unsafe {
                        let ptr = (self as *const Self as *const u8).add(1);
                        std::slice::from_raw_parts(ptr, 4)
                    };
                    Some(data)
                }
                ListpackEntrySubencodingType::SignedInteger64Bit => {
                    let data = unsafe {
                        let ptr = (self as *const Self as *const u8).add(1);
                        std::slice::from_raw_parts(ptr, 8)
                    };
                    Some(data)
                }
            },
        }
    }

    /// Returns the number of bytes used to represent the entry.
    ///
    /// # Note
    ///
    /// Even though the return type is `usize`, the actual number of
    /// bytes is stored as a 4-byte unsigned integer.
    pub fn total_bytes(&self) -> usize {
        let mut total_bytes_offset = std::mem::size_of::<u8>();
        let data = self.get_data_raw();
        if let Some(data) = data {
            total_bytes_offset += data.len();
        }

        // Now return the total bytes as a 4-byte unsigned integer,
        // which is read from the beginning of `self` + the
        // `total_bytes_offset`.

        unsafe {
            let total_bytes_ptr = (self as *const Self as *const u8).add(total_bytes_offset);
            let total_bytes_ptr = total_bytes_ptr as *const u32;
            total_bytes_ptr.read_unaligned() as usize
            // *total_bytes_ptr as usize
        }
    }

    /// Returns the number of bytes used to represent the entry.
    /// This is not necessarily the data of the object stored, depending
    /// on the encoding type, it may contain the length of the data
    /// as well.

    /// Returns the data of the entry.
    pub fn data(&self) -> Result<ListpackEntryData> {
        let encoding_type = self.encoding_type()?;
        let encoding_type_byte = self.get_encoding_type_raw();

        Ok(match encoding_type {
            ListpackEntryEncodingType::SmallUnsignedInteger => {
                let value = encoding_type_byte & 0b01111111;
                ListpackEntryData::SmallUnsignedInteger(value)
            }
            ListpackEntryEncodingType::SmallString => {
                let data = self
                    .get_data_raw()
                    .ok_or(crate::error::Error::MissingDataBlock)?;
                let s = std::str::from_utf8(data)
                    .map_err(crate::error::Error::InvalidStringEncodingInsideDataBlock)?;
                ListpackEntryData::SmallString(s)
            }
            ListpackEntryEncodingType::ComplexType(subencoding_type) => match subencoding_type {
                ListpackEntrySubencodingType::SignedInteger13Bit => {
                    let data = self
                        .get_data_raw()
                        .ok_or(crate::error::Error::MissingDataBlock)?;
                    let n = ((data[0] as i16) << 8) | (data[1] as i16);
                    ListpackEntryData::SignedInteger13Bit(n)
                }
                ListpackEntrySubencodingType::MediumString => {
                    let data = self
                        .get_data_raw()
                        .ok_or(crate::error::Error::MissingDataBlock)?;
                    let len = ((data[0] as usize) << 8) | (data[1] as usize);
                    let s = std::str::from_utf8(&data[2..len + 2]).unwrap();
                    ListpackEntryData::MediumString(s)
                }
                ListpackEntrySubencodingType::LargeString => {
                    let data = self
                        .get_data_raw()
                        .ok_or(crate::error::Error::MissingDataBlock)?;
                    let len = ((data[0] as usize) << 24)
                        | ((data[1] as usize) << 16)
                        | ((data[2] as usize) << 8)
                        | (data[3] as usize);
                    let s = std::str::from_utf8(&data[4..len + 4]).unwrap();
                    ListpackEntryData::LargeString(s)
                }
                ListpackEntrySubencodingType::SignedInteger16Bit => {
                    let data = self
                        .get_data_raw()
                        .ok_or(crate::error::Error::MissingDataBlock)?;
                    let n = ((data[0] as i16) << 8) | (data[1] as i16);
                    ListpackEntryData::SignedInteger16Bit(n)
                }
                ListpackEntrySubencodingType::SignedInteger24Bit => {
                    let data = self
                        .get_data_raw()
                        .ok_or(crate::error::Error::MissingDataBlock)?;
                    let n = ((data[0] as i32) << 16) | ((data[1] as i32) << 8) | (data[2] as i32);
                    ListpackEntryData::SignedInteger24Bit(n)
                }
                ListpackEntrySubencodingType::SignedInteger32Bit => {
                    let data = self
                        .get_data_raw()
                        .ok_or(crate::error::Error::MissingDataBlock)?;
                    let n = ((data[0] as i32) << 24)
                        | ((data[1] as i32) << 16)
                        | ((data[2] as i32) << 8)
                        | (data[3] as i32);
                    ListpackEntryData::SignedInteger32Bit(n)
                }
                ListpackEntrySubencodingType::SignedInteger64Bit => {
                    let data = self
                        .get_data_raw()
                        .ok_or(crate::error::Error::MissingDataBlock)?;
                    let n = ((data[0] as i64) << 56)
                        | ((data[1] as i64) << 48)
                        | ((data[2] as i64) << 40)
                        | ((data[3] as i64) << 32)
                        | ((data[4] as i64) << 24)
                        | ((data[5] as i64) << 16)
                        | ((data[6] as i64) << 8)
                        | (data[7] as i64);
                    ListpackEntryData::SignedInteger64Bit(n)
                }
            },
        })
    }

    /// Returns a reference from a pointer.
    fn ref_from_ptr<'a>(ptr: NonNull<u8>) -> &'a ListpackEntry {
        unsafe { ptr.cast().as_ref() }
        // unsafe { &*ptr.as_ptr().cast::<Self>() }
    }
}

impl PartialEq for ListpackEntry {
    fn eq(&self, other: &Self) -> bool {
        self.total_bytes() == other.total_bytes()
            && self.get_encoding_type_raw() == other.get_encoding_type_raw()
            && self.get_data_raw() == other.get_data_raw()
    }
}

impl Eq for ListpackEntry {}

impl Drop for ListpackEntry {
    fn drop(&mut self) {
        let total_size = self.total_bytes();

        unsafe {
            std::alloc::dealloc(
                self.as_mut_ptr(),
                std::alloc::Layout::from_size_align_unchecked(
                    total_size,
                    std::mem::align_of::<u8>(),
                ),
            )
        }
    }
}

/// The allowed types to be inserted into a listpack.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum ListpackEntryInsert<'a> {
    /// A string to insert into a listpack.
    String(&'a str),
    /// An integer to insert into a listpack.
    Integer(i64),
}

impl<'a> From<&'a str> for ListpackEntryInsert<'a> {
    fn from(value: &'a str) -> Self {
        Self::String(value)
    }
}

macro_rules! impl_listpack_entry_insert_from_number {
    ($($t:ty),*) => {
        $(
            impl From<$t> for ListpackEntryInsert<'_> {
                fn from(n: $t) -> Self {
                    Self::Integer(n as i64)
                }
            }
        )*
    }
}

impl_listpack_entry_insert_from_number!(i8, i16, i32, i64, u8, u16, u32, u64);

/// The listpack entry which is removed from listpack.
#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum ListpackEntryRemoved {
    /// A string to insert into a listpack.
    String(String),
    /// An integer to insert into a listpack.
    Integer(i64),
}

impl From<&str> for ListpackEntryRemoved {
    fn from(value: &str) -> Self {
        Self::String(value.to_owned())
    }
}

impl From<&String> for ListpackEntryRemoved {
    fn from(value: &String) -> Self {
        Self::String(value.to_owned())
    }
}

impl From<NonNull<u8>> for ListpackEntryRemoved {
    fn from(ptr: NonNull<u8>) -> Self {
        let entry = ListpackEntry::ref_from_ptr(ptr);
        let data = entry.data().unwrap();

        match data {
            ListpackEntryData::SmallString(s)
            | ListpackEntryData::MediumString(s)
            | ListpackEntryData::LargeString(s) => Self::String(s.to_owned()),
            ListpackEntryData::SignedInteger13Bit(n) => Self::Integer(n as i64),
            ListpackEntryData::SignedInteger16Bit(n) => Self::Integer(n as i64),
            ListpackEntryData::SignedInteger24Bit(n) => Self::Integer(n as i64),
            ListpackEntryData::SignedInteger32Bit(n) => Self::Integer(n as i64),
            ListpackEntryData::SignedInteger64Bit(n) => Self::Integer(n),
            ListpackEntryData::SmallUnsignedInteger(u) => Self::Integer(u as i64),
        }
    }
}

macro_rules! impl_listpack_entry_removed_from_number {
    ($($t:ty),*) => {
        $(
            impl From<$t> for ListpackEntryRemoved {
                fn from(n: $t) -> Self {
                    Self::Integer(n as i64)
                }
            }
        )*
    }
}

impl_listpack_entry_removed_from_number!(i8, i16, i32, i64, u8, u16, u32, u64);

/// The listpack data structure.
#[repr(transparent)]
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
    pub unsafe fn header_ref(&self) -> ListpackHeaderRef {
        // &*(self.ptr.as_ptr() as *const ListpackHeader)
        ListpackHeaderRef(
            (self.ptr.as_ptr() as *const ListpackHeader)
                .as_ref()
                .expect("Header is valid"),
        )
    }

    /// Creates a new listpack with the given capacity.
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            ptr: NonNull::new(unsafe { bindings::lpNew(capacity) })
                .expect("could not create listpack"),
        }

        // let mut ptr =
        //     NonNull::new(unsafe { bindings::lpNew(capacity) }).expect("could not create listpack");
        // unsafe { std::ptr::read(ptr.as_mut() as *mut _ as *mut Self) }
    }

    /// Returns the number of elements of this listpack.
    pub fn len(&self) -> usize {
        unsafe { bindings::lpLength(self.ptr.as_ptr()) as usize }
    }

    /// Returns the length of the listpack, describing how many elements
    /// are currently in this listpack.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
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
    pub fn push<'a, T: Into<ListpackEntryInsert<'a>>>(&mut self, entry: T) {
        let entry = entry.into();
        self.ptr = NonNull::new(match entry {
            ListpackEntryInsert::String(s) => {
                let string_ptr = s.as_ptr() as *mut _;
                let len_bytes = s.len();
                if len_bytes == 0 {
                    return;
                }

                if len_bytes > std::u32::MAX as usize {
                    panic!("The string is too long to be stored in the listpack.");
                }

                unsafe { bindings::lpAppend(self.ptr.as_ptr(), string_ptr, len_bytes as _) }
            }
            ListpackEntryInsert::Integer(n) => unsafe {
                bindings::lpAppendInteger(self.ptr.as_ptr(), n)
            },
        })
        .expect("Appended to listpack");
    }

    /// Removes the last element from the listpack and returns it, or
    /// [`None`] if it is empty. The returned [`ListpackEntry`] is not
    /// a part of the listpack anymore.
    pub fn pop(&mut self) -> Option<ListpackEntryRemoved> {
        let ptr = NonNull::new(unsafe { bindings::lpLast(self.ptr.as_ptr()) });

        if let Some(ptr) = ptr {
            let cloned = ListpackEntryRemoved::from(ptr);
            self.ptr = NonNull::new(unsafe {
                bindings::lpDelete(self.ptr.as_ptr(), ptr.as_ptr(), std::ptr::null_mut())
            })?;
            Some(cloned)
        } else {
            None
        }
    }

    /// Removes the element at the given index from the listpack and
    /// returns it, or [`None`] if the index is out of bounds.
    ///
    /// # Panics
    ///
    /// Panics if the index is out of bounds.
    pub fn swap_remove(&mut self, index: usize) -> ListpackEntryRemoved {
        let ptr = NonNull::new(unsafe { bindings::lpSeek(self.ptr.as_ptr(), index as _) })
            .expect("Index out of bounds.");
        let cloned = ListpackEntryRemoved::from(ptr);
        self.ptr = NonNull::new(unsafe {
            bindings::lpDelete(self.ptr.as_ptr(), ptr.as_ptr(), std::ptr::null_mut())
        })
        .expect("Deleted from listpack");
        cloned
    }

    /// Returns an iterator over the elements of the listpack.
    pub fn iter(&self) -> ListpackIter {
        ListpackIter {
            listpack: self,
            index: 0,
        }
    }

    // TODO:
    // /// Returns an iterator over the elements of the listpack.
    // pub fn iter_mut(&self) -> ListpackIterMut {
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
impl Listpack {
    /// Returns an element of the listpack at the given index.
    pub fn get(&self, index: usize) -> Option<&ListpackEntry> {
        NonNull::new(unsafe { bindings::lpSeek(self.ptr.as_ptr(), index as _) })
            .map(ListpackEntry::ref_from_ptr)
    }
}

impl Index<usize> for Listpack {
    type Output = ListpackEntry;

    fn index(&self, index: usize) -> &Self::Output {
        self.get(index).expect("Index out of bounds.")
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

impl<'a> Iterator for ListpackIter<'a> {
    type Item = &'a ListpackEntry;

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

// TODO:
// /// A mutable iterator over the elements of a listpack.
// pub struct ListpackIterMut<'a> {
//     listpack: &'a Listpack,
//     index: usize,
// }

// impl Iterator for ListpackIterMut<'_> {
//     type Item = ListpackEntry;

//     fn next(&mut self) -> Option<Self::Item> {
//         if self.index >= self.listpack.len() {
//             return None;
//         }

//         let element = self.listpack.get_mut(self.index).unwrap();

//         self.index += 1;

//         Some(element)
//     }
// }

#[cfg(test)]
mod tests {
    use super::*;

    fn create_hello_world_listpack() -> Listpack {
        let mut listpack = Listpack::new();
        listpack.push("Hello");
        listpack.push("World");
        listpack
    }

    #[test]
    fn test_listpack_header() {
        let mut listpack = Listpack::new();

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
    fn test_listpack_iter() {
        let mut listpack = Listpack::new();
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
    fn test_listpack_get() {
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
    fn test_listpack_clone() {
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
    fn test_listpack_index() {
        let listpack = create_hello_world_listpack();

        assert_eq!(listpack[0].data().unwrap().get_str().unwrap(), "Hello");
        assert_eq!(listpack[1].data().unwrap().get_str().unwrap(), "World");
    }

    #[test]
    fn test_listpack_get_storage_bytes() {
        let listpack = Listpack::new();

        assert_eq!(listpack.get_storage_bytes(), 7);
    }
}
