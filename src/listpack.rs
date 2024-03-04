//! The listpack interface.

use std::{
    fmt::{Debug, Write},
    ops::{Deref, Index, RangeBounds},
    ptr::NonNull,
};

use crate::bindings;
use crate::error::Result;

/// The header of the listpack data structure. Can only be obtained
/// from an existing listpack using the [`Listpack::header_ref`] method.
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
    ///
    /// # Example
    ///
    /// ```
    /// use listpack_redis::Listpack;
    ///
    /// let listpack = Listpack::new();
    /// let header = unsafe { listpack.header_ref() };
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
    /// let listpack = Listpack::new();
    /// let header = unsafe { listpack.header_ref() };
    /// assert_eq!(header.num_elements(), 0);
    ///
    /// let listpack = Listpack::from(&[1, 2, 3]);
    /// let header = unsafe { listpack.header_ref() };
    /// assert_eq!(header.num_elements(), 3);
    pub fn num_elements(&self) -> usize {
        self.num_elements as usize
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
    ///
    /// See [`ListpackHeader::total_bytes`].
    pub fn total_bytes(&self) -> usize {
        self.0.total_bytes as usize
    }

    /// Returns the total number of elements the listpack holds.
    ///
    /// See [`ListpackHeader::num_elements`].
    pub fn num_elements(&self) -> usize {
        self.0.num_elements as usize
    }
}

/// The subencoding type of a listpack entry.
/// The subencoding is the encoding of a listpack entry, which is
/// more complex than the simple encoding types, meaning it can't fit
/// into a single byte of the header's encoding type and requires
/// additional bytes to represent the entry, the data block.
#[repr(u8)]
#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
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
#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
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

impl From<ListpackEntryEncodingType> for u8 {
    fn from(encoding_type: ListpackEntryEncodingType) -> u8 {
        match encoding_type {
            ListpackEntryEncodingType::SmallUnsignedInteger => 0b00000000,
            ListpackEntryEncodingType::SmallString => 0b10000000,
            ListpackEntryEncodingType::ComplexType(subencoding_type) => match subencoding_type {
                ListpackEntrySubencodingType::SignedInteger13Bit => 0b11000000,
                ListpackEntrySubencodingType::MediumString => 0b11100000,
                ListpackEntrySubencodingType::LargeString => 0b11110000,
                ListpackEntrySubencodingType::SignedInteger16Bit => 0b11110001,
                ListpackEntrySubencodingType::SignedInteger24Bit => 0b11110010,
                ListpackEntrySubencodingType::SignedInteger32Bit => 0b11110011,
                ListpackEntrySubencodingType::SignedInteger64Bit => 0b11110100,
            },
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

    /// Attempts to extract an integer from the entry.
    pub fn get_integer(&self) -> Option<i64> {
        Some(match self {
            ListpackEntryData::SmallUnsignedInteger(u) => *u as i64,
            ListpackEntryData::SignedInteger13Bit(i) => *i as i64,
            ListpackEntryData::SignedInteger16Bit(i) => *i as i64,
            ListpackEntryData::SignedInteger24Bit(i) => *i as i64,
            ListpackEntryData::SignedInteger32Bit(i) => *i as i64,
            ListpackEntryData::SignedInteger64Bit(i) => *i,
            _ => return None,
        })
    }
}

impl From<ListpackEntryData<'_>> for ListpackEntryEncodingType {
    fn from(data: ListpackEntryData) -> Self {
        data.encoding_type()
    }
}

impl std::fmt::Display for ListpackEntryData<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ListpackEntryData::SmallUnsignedInteger(u) => write!(f, "{u}"),
            ListpackEntryData::SmallString(s) => write!(f, "{s}"),
            ListpackEntryData::SignedInteger13Bit(i) => write!(f, "{i}"),
            ListpackEntryData::MediumString(s) => write!(f, "{s}"),
            ListpackEntryData::LargeString(s) => write!(f, "{s}"),
            ListpackEntryData::SignedInteger16Bit(i) => write!(f, "{i}"),
            ListpackEntryData::SignedInteger24Bit(i) => write!(f, "{i}"),
            ListpackEntryData::SignedInteger32Bit(i) => write!(f, "{i}"),
            ListpackEntryData::SignedInteger64Bit(i) => write!(f, "{i}"),
        }
    }
}

impl<'a> TryFrom<&'a ListpackEntryData<'a>> for ListpackEntryInsert<'a> {
    type Error = crate::error::Error;

    fn try_from(data: &'a ListpackEntryData<'a>) -> Result<Self> {
        if let Some(data) = data.get_str() {
            Ok(Self::String(data))
        } else if let Some(data) = data.get_i64() {
            Ok(Self::Integer(data))
        } else {
            Err(crate::error::Error::UnknownEncodingType {
                encoding_byte: data.encoding_type().into(),
            })
        }
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
pub struct ListpackEntry(());

impl ListpackEntry {
    /// Returns the pointer to the entry.
    ///
    /// # Example
    ///
    /// ```
    /// use listpack_redis::Listpack;
    ///
    /// let mut listpack = Listpack::new();
    /// listpack.push("Hello");
    /// let entry = listpack.get(0).unwrap();
    /// let ptr = unsafe { entry.as_ptr() };
    /// ```
    pub fn as_ptr(&self) -> *const u8 {
        self as *const _ as *const u8
    }

    // TODO: add an example using the mutable ListpackEntry.
    /// Returns the mutable pointer to the entry.
    pub fn as_mut_ptr(&mut self) -> *mut u8 {
        self as *mut _ as *mut u8
    }

    /// Returns the byte (raw) representation of the encoding type.
    ///
    /// # Example
    ///
    /// ```
    /// use listpack_redis::Listpack;
    ///
    /// let mut listpack = Listpack::new();
    /// listpack.push("Hello");
    /// let entry = listpack.get(0).unwrap();
    /// let encoding_type = unsafe { entry.get_encoding_type_raw() };
    /// ```
    pub fn get_encoding_type_raw(&self) -> u8 {
        unsafe { std::ptr::read_unaligned(self.as_ptr()) }
    }

    /// Returns the encoding type of the entry, parsed from the byte.
    ///
    /// # Example
    ///
    /// ```
    /// use listpack_redis::Listpack;
    ///
    /// let mut listpack = Listpack::new();
    /// listpack.push("Hello");
    /// let entry = listpack.get(0).unwrap();
    /// let encoding_type = entry.encoding_type().unwrap();
    /// assert_eq!(encoding_type, listpack_redis::ListpackEntryEncodingType::SmallString);
    /// ```
    pub fn encoding_type(&self) -> Result<ListpackEntryEncodingType> {
        ListpackEntryEncodingType::try_from(self.get_encoding_type_raw())
    }

    fn get_data_raw_and_total_bytes(&self) -> Option<(&[u8], usize)> {
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
                    let data = std::slice::from_raw_parts(ptr, len);
                    let total_bytes = ptr.add(len).cast::<u8>().read_unaligned() as _;
                    (data, total_bytes)
                };
                Some(data)
            }
            ListpackEntryEncodingType::ComplexType(subencoding_type) => match subencoding_type {
                ListpackEntrySubencodingType::SignedInteger13Bit => {
                    let data = unsafe {
                        let ptr = (self as *const Self as *const u8).add(1);
                        let data = std::slice::from_raw_parts(ptr, 2);
                        let total_bytes = ptr.add(2).cast::<u8>().read_unaligned() as _;
                        (data, total_bytes)
                    };
                    Some(data)
                }
                ListpackEntrySubencodingType::MediumString => {
                    let data = unsafe {
                        let ptr = (self as *const Self as *const u8).add(1);
                        let len = ((*ptr as usize) << 8) | (*ptr.add(1) as usize);
                        let ptr = ptr.add(2);
                        let data = std::slice::from_raw_parts(ptr, len);
                        // TODO: either u8 or u16, in big endian.
                        let total_bytes = ptr.add(len).cast::<u8>().read_unaligned() as _;
                        (data, total_bytes)
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
                        let data = std::slice::from_raw_parts(ptr, len);
                        // TODO: either u16, u24, or u32, in big endian.
                        let total_bytes = ptr.add(len).cast::<u16>().read_unaligned() as _;
                        (data, total_bytes)
                    };
                    Some(data)
                }
                ListpackEntrySubencodingType::SignedInteger16Bit => {
                    let data = unsafe {
                        let ptr = (self as *const Self as *const u8).add(1);
                        let data = std::slice::from_raw_parts(ptr, 2);
                        let total_bytes = ptr.add(2).cast::<u8>().read_unaligned() as _;
                        (data, total_bytes)
                    };
                    Some(data)
                }
                ListpackEntrySubencodingType::SignedInteger24Bit => {
                    let data = unsafe {
                        let ptr = (self as *const Self as *const u8).add(1);
                        let data = std::slice::from_raw_parts(ptr, 3);
                        let total_bytes = ptr.add(3).cast::<u8>().read_unaligned() as _;
                        (data, total_bytes)
                    };
                    Some(data)
                }
                ListpackEntrySubencodingType::SignedInteger32Bit => {
                    let data = unsafe {
                        let ptr = (self as *const Self as *const u8).add(1);
                        let data = std::slice::from_raw_parts(ptr, 4);
                        let total_bytes = ptr.add(4).cast::<u8>().read_unaligned() as _;
                        (data, total_bytes)
                    };
                    Some(data)
                }
                ListpackEntrySubencodingType::SignedInteger64Bit => {
                    let data = unsafe {
                        let ptr = (self as *const Self as *const u8).add(1);
                        let data = std::slice::from_raw_parts(ptr, 8);
                        let total_bytes = ptr.add(8).cast::<u8>().read_unaligned() as _;
                        (data, total_bytes)
                    };
                    Some(data)
                }
            },
        }
    }

    /// Returns the dedicated data block of the entry, if there is one.
    /// An entry may or may not have a data block, depending on the
    /// encoding type.
    ///
    /// The returned block of memory should be treated as a chunk of
    /// bytes, the interpretation of which should be dealth with by the
    /// [`ListpackEntryData`] object, which correctly parses the block,
    /// depending on the encoding type.
    ///
    /// # Example
    ///
    /// ```
    /// use listpack_redis::Listpack;
    ///
    /// let mut listpack = Listpack::new();
    /// listpack.push("Hello");
    /// let entry = listpack.get(0).unwrap();
    /// let data = entry.get_data_raw().unwrap();
    /// ```
    pub fn get_data_raw(&self) -> Option<&[u8]> {
        self.get_data_raw_and_total_bytes().map(|(data, _)| data)
    }

    /// Returns the number of bytes used to represent the entry.
    ///
    /// # Note
    ///
    /// Even though the return type is `usize`, the actual number of
    /// bytes is stored as a 4-byte unsigned integer.
    ///
    /// # Example
    ///
    /// ```
    /// use listpack_redis::Listpack;
    ///
    /// let mut listpack = Listpack::new();
    /// listpack.push("Hello");
    /// let entry = listpack.get(0).unwrap();
    /// let total_bytes = entry.total_bytes();
    /// // Five ascii characters, plus the encoding type byte.
    /// assert_eq!(total_bytes, 6);
    /// ```
    pub fn total_bytes(&self) -> usize {
        self.get_data_raw_and_total_bytes()
            .map(|(_, total_bytes)| total_bytes)
            .unwrap_or(0)
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

impl std::fmt::Debug for ListpackEntry {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let data = self.data().map_err(|_| std::fmt::Error)?;

        write!(f, "{data:?}")
    }
}

impl std::fmt::Display for ListpackEntry {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let data = self.data().map_err(|_| std::fmt::Error)?;

        write!(f, "{data}")
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

impl<'a> From<&'a &str> for ListpackEntryInsert<'a> {
    fn from(value: &'a &str) -> Self {
        Self::String(value)
    }
}

impl<'a> From<&'a String> for ListpackEntryInsert<'a> {
    fn from(value: &'a String) -> Self {
        Self::String(value.as_str())
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

            impl From<&$t> for ListpackEntryInsert<'_> {
                fn from(n: &$t) -> Self {
                    Self::Integer(*n as i64)
                }
            }
        )*
    }
}

impl_listpack_entry_insert_from_number!(i8, i16, i32, i64, u8, u16, u32, u64);

/// The listpack entry which is removed from listpack.
#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum ListpackEntryRemoved {
    /// A string which was removed from a listpack.
    String(String),
    /// An integer which was removed from a listpack.
    Integer(i64),
}

impl ListpackEntryRemoved {
    /// Returns the string representation of the entry, if it is a
    /// string.
    ///
    /// # Example
    ///
    /// ```
    /// use listpack_redis::ListpackEntryRemoved;
    ///
    /// let entry = ListpackEntryRemoved::String("Hello, world!".to_owned());
    /// assert_eq!(entry.get_str(), Some("Hello, world!"));
    /// ```
    pub fn get_str(&self) -> Option<&str> {
        match self {
            Self::String(s) => Some(s),
            _ => None,
        }
    }

    /// Returns the integer representation of the entry, if it is an
    /// integer.
    ///
    /// # Example
    ///
    /// ```
    /// use listpack_redis::ListpackEntryRemoved;
    ///
    /// let entry = ListpackEntryRemoved::Integer(42);
    /// assert_eq!(entry.get_i64(), Some(42));
    /// ```
    pub fn get_i64(&self) -> Option<i64> {
        match self {
            Self::Integer(n) => Some(*n),
            _ => None,
        }
    }
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
    /// A pointer to the listpack object in C.
    ptr: NonNull<u8>,
}

impl Default for Listpack {
    fn default() -> Self {
        Self::with_capacity(0)
    }
}

impl Debug for Listpack {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Listpack")
            .field("ptr", &self.ptr)
            .field("elements", &self.iter().collect::<Vec<_>>())
            .finish()
    }
}

impl std::fmt::Display for Listpack {
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

impl<'a, T> From<&'a [T]> for Listpack
where
    &'a T: Into<ListpackEntryInsert<'a>>,
    ListpackEntryInsert<'a>: std::convert::From<&'a T>,
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

impl<'a, T, const N: usize> From<&'a [T; N]> for Listpack
where
    &'a T: Into<ListpackEntryInsert<'a>>,
    ListpackEntryInsert<'a>: std::convert::From<&'a T>,
{
    fn from(slice: &'a [T; N]) -> Self {
        let mut listpack = Listpack::with_capacity(slice.len());
        for item in slice {
            let item: ListpackEntryInsert<'a> = ListpackEntryInsert::from(item);
            listpack.push(item);
        }
        listpack
    }
}

/// The [`Vec`]-like interface for the listpack.
impl Listpack {
    /// Returns a new listpack.
    ///
    /// # Example
    ///
    /// ```
    /// use listpack_redis::Listpack;
    ///
    /// let listpack = Listpack::new();
    /// assert!(listpack.is_empty());
    /// ```
    pub fn new() -> Self {
        Self::with_capacity(0)
    }

    /// Creates a new listpack with the given capacity.
    ///
    /// # Example
    ///
    /// ```
    /// use listpack_redis::Listpack;
    ///
    /// let listpack = Listpack::with_capacity(10);
    /// assert!(listpack.is_empty());
    /// ```
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            ptr: NonNull::new(unsafe { bindings::lpNew(capacity) })
                .expect("could not create listpack"),
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
    /// let mut old = Listpack::new();
    /// old.push("Hello, world!");
    /// let ptr = unsafe { NonNull::new_unchecked(old.as_mut_ptr()) };
    /// let new = unsafe { Listpack::from_raw_parts(ptr) };
    /// assert_eq!(old.get(0), new.get(0));
    ///
    /// // The old listpack is forgotten so that there is no
    /// // double-free.
    /// std::mem::forget(old);
    /// ```
    pub unsafe fn from_raw_parts(ptr: NonNull<u8>) -> Self {
        Self { ptr }
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
    /// let listpack = Listpack::new();
    /// let header = unsafe { listpack.header_ref() };
    /// assert_eq!(header.num_elements(), 0);
    /// ```
    pub unsafe fn header_ref(&self) -> ListpackHeaderRef {
        // &*(self.ptr.as_ptr() as *const ListpackHeader)
        ListpackHeaderRef(
            (self.ptr.as_ptr() as *const ListpackHeader)
                .as_ref()
                .expect("Header is valid"),
        )
    }

    /// Returns the number of elements of this listpack.
    ///
    /// # Example
    ///
    /// ```
    /// use listpack_redis::Listpack;
    ///
    /// let mut listpack = Listpack::new();
    /// listpack.push("Hello, world!");
    /// assert_eq!(listpack.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        unsafe { bindings::lpLength(self.ptr.as_ptr()) as usize }
    }

    /// Returns the length of the listpack, describing how many elements
    /// are currently in this listpack.
    ///
    /// # Example
    ///
    /// ```
    /// use listpack_redis::Listpack;
    ///
    /// let mut listpack = Listpack::new();
    /// listpack.push("Hello, world!");
    /// assert!(!listpack.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

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
        if let Some(ptr) = NonNull::new(unsafe { bindings::lpShrinkToFit(self.ptr.as_ptr()) }) {
            self.ptr = ptr;
            true
        } else {
            false
        }
    }

    /// Truncates the listpack, keeping only the first `len` elements.
    ///
    /// # Example
    ///
    /// ```
    /// use listpack_redis::Listpack;
    ///
    /// let mut listpack = Listpack::new();
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
        let length = self.len() - len;
        let ptr = unsafe { bindings::lpDeleteRange(self.ptr.as_ptr(), start as _, length as _) };

        if let Some(ptr) = NonNull::new(ptr) {
            self.ptr = ptr;
        }
    }

    /// Returns a raw pointer to the listpack. The returned pointer is
    /// never null.
    ///
    /// # Example
    ///
    /// ```
    /// use listpack_redis::Listpack;
    ///
    /// let listpack = Listpack::new();
    /// let ptr = listpack.as_ptr();
    /// assert!(!ptr.is_null());
    /// ```
    pub fn as_ptr(&self) -> *const u8 {
        self.ptr.as_ptr()
    }

    /// Returns a mutable raw pointer to the listpack. The returned
    /// pointer is never null.
    ///
    /// # Example
    ///
    /// ```
    /// use listpack_redis::Listpack;
    ///
    /// let mut listpack = Listpack::new();
    /// let ptr = listpack.as_mut_ptr();
    /// assert!(!ptr.is_null());
    /// ```
    pub fn as_mut_ptr(&mut self) -> *mut u8 {
        self.ptr.as_ptr()
    }

    /// Clears the entire listpack. Same as calling [`Self::truncate()`]
    /// with `0` as an argument.
    ///
    /// # Example
    ///
    /// ```
    /// use listpack_redis::Listpack;
    /// let mut listpack = Listpack::new();
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
    /// let mut listpack = Listpack::new();
    /// listpack.push("Hello, world!");
    /// assert_eq!(listpack.len(), 1);
    /// ```
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

    // TODO: doc
    /// Inserts an element at the given index into the listpack.
    pub fn insert<'a, T: Into<ListpackEntryInsert<'a>>>(&mut self, index: usize, entry: T) {
        todo!("Implement insert method.")
        // let entry = entry.into();
        // let ptr = NonNull::new(unsafe { bindings::lpSeek(self.ptr.as_ptr(), index as _) })
        //     .expect("Index out of bounds.");

        // let ptr = NonNull::new(match entry {
        //     ListpackEntryInsert::String(s) => {
        //         let string_ptr = s.as_ptr() as *mut _;
        //         let len_bytes = s.len();
        //         if len_bytes == 0 {
        //             return;
        //         }

        //         if len_bytes > std::u32::MAX as usize {
        //             panic!("The string is too long to be stored in the listpack.");
        //         }

        //         unsafe {
        //             bindings::lpInsert(self.ptr.as_ptr(), ptr.as_ptr(), string_ptr, len_bytes as _)
        //         }
        //     }
        //     ListpackEntryInsert::Integer(n) => unsafe {
        //         bindings::lpInsertInteger(self.ptr.as_ptr(), ptr.as_ptr(), n)
        //     },
        // })
        // .expect("Inserted into listpack");

        // self.ptr = ptr;
    }

    // TODO: doc
    /// Removes the element at the given index from the listpack and
    /// returns it.
    pub fn remove(&mut self, index: usize) -> ListpackEntryRemoved {
        todo!("Implement remove method.")
        // let ptr = NonNull::new(unsafe { bindings::lpSeek(self.ptr.as_ptr(), index as _) })
        //     .expect("Index out of bounds.");
        // let cloned = ListpackEntryRemoved::from(ptr);
        // self.ptr = NonNull::new(unsafe {
        //     bindings::lpDelete(self.ptr.as_ptr(), ptr.as_ptr(), std::ptr::null_mut())
        // })
        // .expect("Deleted from listpack");
        // cloned
    }

    // TODO: doc
    /// Retains only the elements specified by the predicate.
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&ListpackEntry) -> bool,
    {
        todo!("Implement retain method.")
        // let mut index = 0;
        // while index < self.len() {
        //     let entry = self.get(index).unwrap();
        //     if !f(entry) {
        //         let _ = self.remove(index);
        //     } else {
        //         index += 1;
        //     }
        // }
    }

    // TODO: doc
    /// Appends the elements of another listpack to the back of this
    /// listpack.
    pub fn append(&mut self, other: &mut Self) {
        todo!("Implement append method.")
        // let ptr = NonNull::new(unsafe { bindings::lpAppendLP(self.ptr.as_ptr(), other.ptr.as_ptr()) })
        //     .expect("Appended to listpack");
        // self.ptr = ptr;
    }

    // TODO: doc
    /// Removes the elements in the specified range from the listpack
    /// in bulk, returning all removed elements as an iterator.
    pub fn drain<R>(&mut self, range: R) -> ListpackDrain
    where
        R: RangeBounds<usize>,
    {
        todo!("Implement drain method.")
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

        // let length = end - start;
        // let ptr = unsafe { bindings::lpDeleteRange(self.ptr.as_ptr(), start as _, length as _) };

        // if let Some(ptr) = NonNull::new(ptr) {
        //     self.ptr = ptr;
        // }

        // ListpackDrain {
        //     listpack: self,
        //     start,
        //     end,
        // }
    }

    /// Splits the listpack into two at the given index. Returns a new
    /// listpack containing the elements from `at` to the end, and
    /// removes those elements from the original listpack.
    pub fn split_off(&mut self, at: usize) -> Self {
        todo!("Implement split_off method.")
    }

    // TODO: doc
    /// Appends all the elements of a slice to the listpack.
    pub fn extend_from_slice<'a, T: Into<ListpackEntryInsert<'a>>>(&mut self, slice: &'a [T]) {
        todo!("Implement extend_from_slice method.")
        // for item in slice {
        //     self.push(item);
        // }
    }

    // TODO: doc
    /// Removes consecutive repeated elements from the listpack.
    pub fn dedup(&mut self) {
        todo!("Implement dedup method.")
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

    // TODO: more elements from slice.
    /// Reverses the order of the elements in the listpack in place.
    pub fn reverse(&mut self) {
        todo!("Implement reverse method.")
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
    pub fn windows(&self, size: usize) -> ListpackWindows {
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
    pub fn chunks(&self, size: usize) -> ListpackChunks {
        if size == 0 {
            panic!("The size must be greater than zero.");
        }

        ListpackChunks {
            listpack: self,
            size,
            index: 0,
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
    /// let mut listpack = Listpack::new();
    /// listpack.push("Hello, world!");
    /// assert_eq!(listpack.len(), 1);
    /// let removed = listpack.pop().unwrap();
    /// assert_eq!(listpack.len(), 0);
    /// assert_eq!(removed.get_str().unwrap(), "Hello, world!");
    /// ```
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
    // /// let mut listpack = Listpack::new();
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

    /// Returns `true` if the listpack contains an element with the
    /// given value.
    ///
    /// # Example
    ///
    /// ```
    /// use listpack_redis::Listpack;
    ///
    /// let mut listpack = Listpack::new();
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
    // pub fn contains<'a, T: Into<ListpackEntryInsert<'a>>>(&self, object: T) -> bool {
    //     let object = object.into();

    //     self.iter().any(|entry| -> bool {
    //         if let Ok(data) = entry
    //             .data()
    //             .and_then(|data| ListpackEntryInsert::try_from(&data))
    //         {
    //             data == object
    //         } else {
    //             false
    //         }
    //     })
    // }

    /// Returns `true` if the listpack begins with the elements of the
    /// given prefix.
    ///
    /// # Example
    ///
    /// ```
    /// use listpack_redis::Listpack;
    ///
    /// let mut listpack = Listpack::new();
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
    /// let mut listpack = Listpack::new();
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
    ///
    /// # Example
    ///
    /// ```
    /// use listpack_redis::Listpack;
    ///
    /// let mut listpack = Listpack::new();
    /// listpack.push("Hello");
    /// listpack.push("World");
    /// assert_eq!(listpack.get(0).unwrap().data().unwrap().get_small_str().unwrap(), "Hello");
    /// assert_eq!(listpack.get(1).unwrap().data().unwrap().get_small_str().unwrap(), "World");
    /// assert!(listpack.get(2).is_none());
    /// ```
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
    ///
    /// # Example
    ///
    /// ```
    /// use listpack_redis::Listpack;
    ///
    /// let mut listpack = Listpack::with_capacity(10);
    /// assert_eq!(listpack.get_storage_bytes(), 7);
    /// listpack.push("Hello, world!");
    /// assert_eq!(listpack.get_storage_bytes(), 22);
    /// listpack.push("Hello!");
    /// assert_eq!(listpack.get_storage_bytes(), 30);
    /// let _ = listpack.pop();
    /// assert_eq!(listpack.get_storage_bytes(), 22);
    /// ```
    pub fn get_storage_bytes(&self) -> usize {
        unsafe { bindings::lpBytes(self.ptr.as_ptr()) }
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

impl DoubleEndedIterator for ListpackIter<'_> {
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

/// An iterator over the elements of a listpack, which removes the
/// elements from the listpack.
pub struct ListpackDrain<'a> {
    listpack: &'a mut Listpack,
}

/// An iterator over the elements of a listpack, which returns
/// contiguous windows of elements.
///
/// # Example
///
/// ```
/// use listpack_redis::Listpack;
///
/// let mut listpack = Listpack::new();
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
/// let mut listpack = Listpack::new();
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
pub struct ListpackWindows<'a> {
    listpack: &'a Listpack,
    size: usize,
    index: usize,
}

impl<'a> Iterator for ListpackWindows<'a> {
    type Item = Vec<&'a ListpackEntry>;

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

impl DoubleEndedIterator for ListpackWindows<'_> {
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
/// let mut listpack = Listpack::new();
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
/// let mut listpack = Listpack::new();
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

pub struct ListpackChunks<'a> {
    listpack: &'a Listpack,
    size: usize,
    index: usize,
}

impl<'a> Iterator for ListpackChunks<'a> {
    type Item = Vec<&'a ListpackEntry>;

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
    fn header() {
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
    fn starts_with() {
        let mut listpack = Listpack::new();
        listpack.push("Hello");
        listpack.push("World");

        assert!(listpack.starts_with(&["Hello"]));
        assert!(listpack.starts_with(&["Hello", "World"]));
        assert!(!listpack.starts_with(&["Hello", "World", "!"]));
    }

    #[test]
    fn ends_with() {
        let mut listpack = Listpack::new();
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
        let listpack = Listpack::new();

        assert_eq!(listpack.get_storage_bytes(), 7);
    }

    #[test]
    fn entry_total_bytes() {
        let mut listpack = Listpack::new();

        listpack.push("Hello");

        let entry = listpack.get(0).unwrap();
        let total_bytes = entry.total_bytes();
        assert_eq!(total_bytes, 6);
    }
}
