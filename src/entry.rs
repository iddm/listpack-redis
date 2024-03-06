//! Listpack entries.

use std::{ops::Deref, ptr::NonNull};

use crate::{error::Result, Listpack};

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
    const ENCODING_TYPE_BYTE_LENGTH: usize = std::mem::size_of::<u8>();

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
    #[inline]
    pub fn as_ptr(&self) -> *const u8 {
        self as *const _ as *const u8
    }

    /// Returns the mutable pointer to the entry.
    #[inline]
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
    #[inline]
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
    #[inline]
    pub fn encoding_type(&self) -> Result<ListpackEntryEncodingType> {
        ListpackEntryEncodingType::try_from(self.get_encoding_type_raw())
    }

    /// This method doesn't return the total number of bytes from the
    /// entry, but rather calculates it on the fly, as the length is
    /// already known when reading from the left-to-right.
    fn get_data_raw_and_total_bytes(&self) -> Option<(&[u8], usize)> {
        // Depending on the encoding type, the data block may or may not
        // be present. If it is present, it is located after the encoding
        // type byte.
        let encoding_type = self.encoding_type().ok()?;
        let encoding_type_byte = self.get_encoding_type_raw();
        // Skip the encoding byte.
        let ptr = unsafe { (self as *const Self as *const u8).add(1) };

        match encoding_type {
            ListpackEntryEncodingType::SmallUnsignedInteger => None,
            ListpackEntryEncodingType::SmallString => {
                let len = (encoding_type_byte & 0b00111111) as usize;
                let data = unsafe {
                    let data = std::slice::from_raw_parts(ptr, len);
                    let total_bytes = ptr.add(len).cast::<u8>().read_unaligned() as _;
                    (data, total_bytes)
                };
                Some(data)
            }
            ListpackEntryEncodingType::ComplexType(subencoding_type) => match subencoding_type {
                ListpackEntrySubencodingType::SignedInteger13Bit => {
                    let data = unsafe {
                        let data = std::slice::from_raw_parts(ptr, 2);
                        let total_bytes = ptr.add(2).cast::<u8>().read_unaligned() as _;
                        (data, total_bytes)
                    };
                    Some(data)
                }
                ListpackEntrySubencodingType::MediumString => {
                    let data = unsafe {
                        let len = ((encoding_type_byte & 0b00001111) as usize) << 8 | *ptr as usize;
                        let ptr = ptr.add(1);
                        let data = std::slice::from_raw_parts(ptr, len);
                        // One extra byte for the length of the data block.
                        let extra_length = Self::ENCODING_TYPE_BYTE_LENGTH + 1;
                        (data, len + extra_length)
                    };
                    Some(data)
                }
                ListpackEntrySubencodingType::LargeString => {
                    let data = unsafe {
                        let len = ((*ptr.add(3) as usize) << 24)
                            | ((*ptr.add(2) as usize) << 16)
                            | ((*ptr.add(1) as usize) << 8)
                            | (*ptr as usize);
                        let ptr = ptr.add(4);
                        let data = std::slice::from_raw_parts(ptr, len);
                        // Four extra bytes for the length of the data block.
                        let extra_length = Self::ENCODING_TYPE_BYTE_LENGTH + 4;
                        (data, len + extra_length)
                    };
                    Some(data)
                }
                ListpackEntrySubencodingType::SignedInteger16Bit => {
                    let data = unsafe {
                        let data = std::slice::from_raw_parts(ptr, 2);
                        let total_bytes = ptr.add(2).cast::<u8>().read_unaligned() as _;
                        (data, total_bytes)
                    };
                    Some(data)
                }
                ListpackEntrySubencodingType::SignedInteger24Bit => {
                    let data = unsafe {
                        let data = std::slice::from_raw_parts(ptr, 3);
                        let total_bytes = ptr.add(3).cast::<u8>().read_unaligned() as _;
                        (data, total_bytes)
                    };
                    Some(data)
                }
                ListpackEntrySubencodingType::SignedInteger32Bit => {
                    let data = unsafe {
                        let data = std::slice::from_raw_parts(ptr, 4);
                        let total_bytes = ptr.add(4).cast::<u8>().read_unaligned() as _;
                        (data, total_bytes)
                    };
                    Some(data)
                }
                ListpackEntrySubencodingType::SignedInteger64Bit => {
                    let data = unsafe {
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
                    let s = std::str::from_utf8(data).unwrap();
                    ListpackEntryData::MediumString(s)
                }
                ListpackEntrySubencodingType::LargeString => {
                    let data = self
                        .get_data_raw()
                        .ok_or(crate::error::Error::MissingDataBlock)?;
                    let s = std::str::from_utf8(data).unwrap();
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
    pub(crate) fn ref_from_ptr<'a>(ptr: NonNull<u8>) -> &'a ListpackEntry {
        unsafe { ptr.cast().as_ref() }
    }

    // /// Returns a mutable reference from a pointer.
    // fn ref_mut_from_ptr<'a>(ptr: NonNull<u8>) -> &'a mut ListpackEntry {
    //     unsafe { ptr.cast().as_mut() }
    // }
}

impl PartialEq for ListpackEntry {
    fn eq(&self, other: &Self) -> bool {
        self.total_bytes() == other.total_bytes()
            && self.get_encoding_type_raw() == other.get_encoding_type_raw()
            && self.get_data_raw() == other.get_data_raw()
    }
}

impl PartialEq<str> for ListpackEntry {
    fn eq(&self, other: &str) -> bool {
        self.data()
            .map(|data| data.get_str() == Some(other))
            .unwrap_or(false)
    }
}

impl PartialEq<i64> for ListpackEntry {
    fn eq(&self, other: &i64) -> bool {
        self.data()
            .map(|data| data.get_integer() == Some(*other))
            .unwrap_or(false)
    }
}

impl PartialEq<ListpackEntryInsert<'_>> for ListpackEntry {
    fn eq(&self, other: &ListpackEntryInsert) -> bool {
        match other {
            ListpackEntryInsert::String(s) => self == *s,
            ListpackEntryInsert::Integer(n) => self == n,
        }
    }
}

impl PartialEq<ListpackEntryInsert<'_>> for &ListpackEntry {
    fn eq(&self, other: &ListpackEntryInsert) -> bool {
        match other {
            ListpackEntryInsert::String(s) => *self == *s,
            ListpackEntryInsert::Integer(n) => *self == n,
        }
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

impl std::fmt::Display for ListpackEntryRemoved {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::String(s) => write!(f, "{s}"),
            Self::Integer(n) => write!(f, "{n}"),
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

impl From<ListpackEntry> for ListpackEntryRemoved {
    fn from(entry: ListpackEntry) -> Self {
        Self::from(&entry)
    }
}

impl From<&ListpackEntry> for ListpackEntryRemoved {
    fn from(entry: &ListpackEntry) -> Self {
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

impl<'a> From<&'a ListpackEntryRemoved> for ListpackEntryInsert<'a> {
    fn from(removed: &'a ListpackEntryRemoved) -> Self {
        match removed {
            ListpackEntryRemoved::String(s) => Self::String(s),
            ListpackEntryRemoved::Integer(n) => Self::Integer(*n),
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

/// A mutable reference to an entry in a listpack, mainly used for
/// modifying the entry in place using the mutable iterator.
#[derive(Debug)]
pub struct ListpackEntryMutable<'a> {
    listpack: &'a mut Listpack,
    entry: &'a ListpackEntry,
    index: usize,
}

impl<'a> ListpackEntryMutable<'a> {
    /// Creates a new mutable listpack entry reference object.
    pub(crate) fn new(listpack: &'a mut Listpack, entry: &'a ListpackEntry, index: usize) -> Self {
        Self {
            listpack,
            entry,
            index,
        }
    }

    /// Modifies the value of the entry in-place.
    ///
    /// See [`Listpack::replace`] for more information.
    pub fn set<T>(&mut self, value: T)
    where
        ListpackEntryInsert<'a>: std::convert::From<T>,
    {
        let entry = ListpackEntryInsert::from(value);
        self.listpack.replace(self.index, entry);
    }

    /// Returns a reference to this entry.
    pub fn get(&self) -> &ListpackEntry {
        self.entry
    }
}

impl<'a> Deref for ListpackEntryMutable<'a> {
    type Target = ListpackEntry;

    fn deref(&self) -> &Self::Target {
        self.entry
    }
}
