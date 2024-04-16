//! Listpack entries.

use std::{ops::Deref, ptr::NonNull};

use redis_custom_allocator::{CustomAllocator, MemoryConsumption};

use crate::{error::Result, Listpack};

const SMALL_STRING_MAXIMUM_LENGTH: usize = 63;
const MEDIUM_STRING_MAXIMUM_LENGTH: usize = 4095;

/// The encoded presentation of the object as a byte array.
pub trait Encode {
    /// Return a byte representation of the object.
    fn encode(&self) -> Result<Vec<u8>>;
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
    /// are `1110`, the lower four bytes are the highest integer part of
    /// the length of the string, with the next byte being the lowest 8
    /// bits of the length.
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
    /// A 64-bit floating-point number: the higher four bits are `1111`,
    /// and the following four bits are `0101`. The following eight
    /// bytes of the data block represent a 64 bits floating-point
    /// number.
    FloatingPoint64Bit = 0b11110101,
    /// A boolean value: the value is embedded directly into the
    /// encoding byte. The higher four bits are `1111`, the further
    /// 3 bits are `011`, and the last remaining bit is the boolean
    /// value itself.
    Boolean = 0b11110110,
    /// A custom embedded value. For example, a custom data structure
    /// which data can be embedded into the entry header's last bit.
    CustomEmbeddedValue = 0b11111000,
    // TODO: this comment needs to be confirmed to comply with the spec
    // and the maximum possible length, as it must not exceed the
    // total-element-length length.
    /// A custom extended value, whose data is stored in the data block.
    /// The maximum length of the extended value is not limited by the
    /// encoding type, but by the maximum size of the data block. The
    /// interpretation of the data stored is up to the user.
    ///
    /// The extended value layout is as follows:
    ///
    /// <1 encoding byte> <1 byte count of the data length> <length> <data> <total-element-length>
    ///
    /// In case the data length is 0, the extended value layout is:
    ///
    /// <1 encoding byte> <0> <total-element-length>
    ///
    /// So the data and the length of the data are not stored at all,
    /// which saves space. In case the data length is of one byte:
    ///
    /// <1 encoding byte> <1> <1 byte data length> <data> <total-element-length>
    ///
    /// Let's say we store a string "Hello":
    ///
    /// <11111010> <0b00000001> <0b00000101> "Hello" <total-element-length>
    CustomExtendedValue = 0b11111010,
}

impl Encode for ListpackEntrySubencodingType {
    fn encode(&self) -> Result<Vec<u8>> {
        // Handle the special cases of the internal encoding types.
        match self {
            // Only boolean and the custom embedded value have the value
            // embedded into the encoding byte itself.
            Self::Boolean => Ok(vec![0b1111_0110]),
            Self::CustomEmbeddedValue => Ok(vec![0b1111_1000]),
            _ => Ok(vec![*self as u8]),
        }
    }
}

impl TryFrom<u8> for ListpackEntrySubencodingType {
    type Error = crate::error::Error;

    fn try_from(encoding_byte: u8) -> Result<Self> {
        match encoding_byte {
            0b1111_0101 => Ok(Self::FloatingPoint64Bit),
            0b1111_0110 | 0b1111_0111 => Ok(Self::Boolean),
            0b1111_1000 | 0b1111_1001 => Ok(Self::CustomEmbeddedValue),
            0b1111_1010 => Ok(Self::CustomExtendedValue),
            0b1111_0000 => Ok(Self::LargeString),
            0b1111_0001 => Ok(Self::SignedInteger16Bit),
            0b1111_0010 => Ok(Self::SignedInteger24Bit),
            0b1111_0011 => Ok(Self::SignedInteger32Bit),
            0b1111_0100 => Ok(Self::SignedInteger64Bit),
            _ => {
                if encoding_byte & 0b1110_0000 == 0b1100_0000 {
                    Ok(Self::SignedInteger13Bit)
                } else if encoding_byte & 0b1111_0000 == 0b1110_0000 {
                    Ok(Self::MediumString)
                } else {
                    Err(crate::error::Error::UnknownEncodingType { encoding_byte })
                }
            }
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

impl Encode for ListpackEntryEncodingType {
    fn encode(&self) -> Result<Vec<u8>> {
        Ok(vec![u8::from(*self)])
    }
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
                ListpackEntrySubencodingType::FloatingPoint64Bit => 0b11110101,
                ListpackEntrySubencodingType::Boolean => 0b11110110,
                ListpackEntrySubencodingType::CustomEmbeddedValue => 0b11111000,
                ListpackEntrySubencodingType::CustomExtendedValue => 0b11111010,
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
    /// See [`ListpackEntrySubencodingType::FloatingPoint64Bit`].
    FloatingPoint64Bit(f64),
    /// See [`ListpackEntrySubencodingType::Boolean`].
    Boolean(bool),
    /// See [`ListpackEntrySubencodingType::CustomEmbeddedValue`].
    CustomEmbeddedValue(u8),
    /// See [`ListpackEntrySubencodingType::CustomExtendedValue`].
    CustomExtendedValue(&'a [u8]),
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
            ListpackEntryData::FloatingPoint64Bit(_) => ListpackEntryEncodingType::ComplexType(
                ListpackEntrySubencodingType::FloatingPoint64Bit,
            ),
            ListpackEntryData::Boolean(_) => {
                ListpackEntryEncodingType::ComplexType(ListpackEntrySubencodingType::Boolean)
            }
            ListpackEntryData::CustomEmbeddedValue(_) => ListpackEntryEncodingType::ComplexType(
                ListpackEntrySubencodingType::CustomEmbeddedValue,
            ),
            ListpackEntryData::CustomExtendedValue(_) => ListpackEntryEncodingType::ComplexType(
                ListpackEntrySubencodingType::CustomExtendedValue,
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

    /// Attempts to extract a 64-bit floating point value from the
    /// entry.
    pub fn get_f64(&self) -> Option<f64> {
        match self {
            ListpackEntryData::FloatingPoint64Bit(f) => Some(*f),
            _ => None,
        }
    }

    /// Attempts to extract a boolean value from the entry.
    pub fn get_bool(&self) -> Option<bool> {
        match self {
            ListpackEntryData::Boolean(b) => Some(*b),
            _ => None,
        }
    }

    /// Attempts to extract a custom embedded value from the entry.
    pub fn get_custom_embedded(&self) -> Option<u8> {
        match self {
            ListpackEntryData::CustomEmbeddedValue(v) => Some(*v),
            _ => None,
        }
    }

    /// Attempts to extract a custom embedded value from the entry.
    pub fn get_custom_extended(&self) -> Option<&[u8]> {
        match self {
            ListpackEntryData::CustomExtendedValue(v) => Some(v),
            _ => None,
        }
    }

    /// Returns `true` if the entry is a boolean.
    pub fn is_bool(&self) -> bool {
        self.get_bool().is_some()
    }

    /// Returns `true` if the entry is a custom embedded value.
    pub fn is_custom_embedded(&self) -> bool {
        self.get_custom_embedded().is_some()
    }

    /// Returns `true` if the entry is a custom extended value.
    pub fn is_custom_extended(&self) -> bool {
        self.get_custom_extended().is_some()
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

    /// Returns `true` if the entry is a 64-bit floating point value.
    pub fn is_f64(&self) -> bool {
        self.get_f64().is_some()
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

/// The encoded number of bytes of the total element length, which spans
/// across several bytes, depending on the length of the data block.
///
/// The value does not include the total-element-length byte(s) itself.
fn encode_total_element_length(length: usize) -> Result<Vec<u8>> {
    Ok(match length {
        // 1. If it fits into a 7-bit integer, store it as a single byte.
        //
        // 2. If it doesn't fit into 7 bits, but fits into 14 bits, store
        // it as a two-byte integer, with the first byte having the
        // highest bit set to zero and the highest 7 bits of the value,
        // and the second byte having the highest bit set to 1 and the
        // lowest 7 bits of the value.
        //
        // 3. If it doesn't fit into 14 bits, but fits into 21 bits, store
        // it as a three-byte integer, with the first byte having the
        // highest bit set to 0 and the lowest 7 bits to the highest 7
        // bits of the value, the second byte having the highest bit set
        // to 1 and the further lowest 7 bits of the value, and the
        // third byte having the highest bit set to 1 and the lowest 7
        // bits of the value.
        //
        // 4. If it doesn't fit into 21 bits, but fits into 28 bits,
        // store it as a four-byte integer, with the first byte having
        // the highest bit set to 0 and the lowest 7 bits to the highest
        // 7 bits of the value, the second byte having the highest bit
        // set to 1 and the further lowest 7 bits of the value, the third
        // byte having the highest bit set to 1 and the further lowest 7
        // bits of the value, and the fourth byte having the highest bit
        // set to 1 and the lowest 7 bits of the value.
        //
        // 5. If it doesn't fit into 28 bits, but fits into 35 bits, store
        // it as a five-byte integer, with the first byte having the
        // highest bit set to 0 and the lowest 7 bits to the highest 7
        // bits of the value, the second byte having the highest bit set
        // to 1 and the further lowest 7 bits of the value, the third
        // byte having the highest bit set to 1 and the further lowest 7
        // bits of the value, the fourth byte having the highest bit set
        // to 1 and the further lowest 7 bits of the value, and the fifth
        // byte having the highest bit set to 1 and the lowest 7 bits of
        // the value.
        0..=127 => vec![length as u8],
        128..=16383 => {
            let mut data = vec![(length >> 7) as u8, (length & 0b01111111) as u8];
            data[1] |= 0b10000000;
            data
        }
        16384..=2097151 => {
            let mut data = vec![
                (length >> 14) as u8,
                ((length >> 7) & 0b01111111) as u8,
                (length & 0b01111111) as u8,
            ];
            data[1] |= 0b10000000;
            data[2] |= 0b10000000;
            data
        }
        2097152..=268435455 => {
            let mut data = vec![
                (length >> 21) as u8,
                ((length >> 14) & 0b01111111) as u8,
                ((length >> 7) & 0b01111111) as u8,
                (length & 0b01111111) as u8,
            ];
            data[1] |= 0b10000000;
            data[2] |= 0b10000000;
            data[3] |= 0b10000000;
            data
        }
        268435456..=34359738367 => {
            let mut data = vec![
                (length >> 28) as u8,
                ((length >> 21) & 0b01111111) as u8,
                ((length >> 14) & 0b01111111) as u8,
                ((length >> 7) & 0b01111111) as u8,
                (length & 0b01111111) as u8,
            ];
            data[1] |= 0b10000000;
            data[2] |= 0b10000000;
            data[3] |= 0b10000000;
            data[4] |= 0b10000000;
            data
        }
        _ => {
            return Err(crate::error::Error::ObjectIsTooBigForEncoding {
                size: length,
                max_size: 34359738367,
            })
        }
    })
}

/// Returns the number of bytes the `total-element-length` part of the
/// element should occupy.
fn calculate_total_element_length(object_length: usize) -> usize {
    // We need to take the "len" and count how many times we can split
    // it into 7-bit integers.

    count_shifts(object_length, 7)
}

/// Returns the number of fully-utilised bytes required to store a value
/// in the `number`.
fn count_bytes_in_number(number: usize) -> usize {
    count_shifts(number, 8)
}

/// Returns the number of bytes required to store a value in the
/// `number`, when shifted by `shift_by`.
fn count_shifts(number: usize, shift_by: u8) -> usize {
    let mut count = 1;
    let mut remainder = number;

    loop {
        remainder >>= shift_by;

        if remainder > 0 {
            count += 1;
        } else {
            break;
        }
    }

    count
}

impl<'a> Encode for ListpackEntryData<'a> {
    /// The encoding of the data block is as follows:
    ///
    /// 1. If the data block is a small unsigned integer, the encoding
    ///  byte is the integer itself.
    ///
    /// 2. If the data block is a small string, the encoding byte is the
    /// length of the string, and the following bytes are the string
    /// itself.
    ///
    /// 3. If the data block is a complex type, the encoding byte is the
    /// type of the complex type, and the following bytes are the data
    /// block itself.
    ///
    /// The total-element-length byte(s) is(are) located behind the data
    /// block, and is encoded as a variable-length integer from right
    /// to left.
    fn encode(&self) -> Result<Vec<u8>> {
        let encoding_type_byte: u8 = self.encoding_type().into();

        // TODO: can be optimised without an allocation to a vec, but
        // rather going through the bytes of the target object instead.
        Ok(match self {
            // The small unsigned integer is embedded into the encoding
            // byte itself, so appending only the total-element-length
            // byte which equals to one: the encoding byte itself.
            Self::SmallUnsignedInteger(u) => vec![u & 0b01111111, 1],
            Self::SignedInteger13Bit(i) => {
                let mut block = vec![encoding_type_byte | ((i >> 8) as u8), (*i as u8)];

                let mut length = encode_total_element_length(block.len())?;
                block.append(&mut length);
                block
            }
            Self::SignedInteger16Bit(i) => {
                let mut block = vec![encoding_type_byte];

                let mut data = i.to_le_bytes().to_vec();
                block.append(&mut data);

                let mut length = encode_total_element_length(block.len())?;
                block.append(&mut length);
                block
            }
            Self::SignedInteger24Bit(i) | Self::SignedInteger32Bit(i) => {
                let mut block = vec![encoding_type_byte];

                let mut data = i.to_le_bytes().to_vec();
                block.append(&mut data);

                // If the number is 24-bit, the last byte is zero, so we
                // need to remove it.
                if block.ends_with(&[0]) {
                    block.pop();
                }

                let mut length = encode_total_element_length(block.len())?;
                block.append(&mut length);
                block
            }
            Self::SignedInteger64Bit(i) => {
                let mut block = vec![encoding_type_byte];

                let mut data = i.to_le_bytes().to_vec();
                block.append(&mut data);

                let mut length = encode_total_element_length(block.len())?;
                block.append(&mut length);
                block
            }
            // The length of the small string is embedded into the
            // encoding byte itself.
            Self::SmallString(s) => {
                let string_length = s.len();

                if string_length > SMALL_STRING_MAXIMUM_LENGTH {
                    return Err(crate::error::Error::ObjectIsTooBigForEncoding {
                        size: string_length,
                        max_size: SMALL_STRING_MAXIMUM_LENGTH,
                    });
                }

                let mut block = vec![encoding_type_byte | (string_length as u8)];

                let mut data = s.as_bytes().to_vec();
                block.append(&mut data);

                let mut length = encode_total_element_length(block.len())?;
                block.append(&mut length);
                block
            }
            Self::MediumString(s) => {
                let string_length = s.len();

                if string_length > MEDIUM_STRING_MAXIMUM_LENGTH {
                    return Err(crate::error::Error::ObjectIsTooBigForEncoding {
                        size: string_length,
                        max_size: MEDIUM_STRING_MAXIMUM_LENGTH,
                    });
                }

                let mut block = vec![
                    encoding_type_byte | ((string_length >> 8) as u8),
                    (string_length as u8),
                ];

                let mut data = s.as_bytes().to_vec();
                block.append(&mut data);

                let mut length = encode_total_element_length(block.len())?;
                block.append(&mut length);
                block
            }
            Self::LargeString(s) => {
                let string_length = s.len();

                if string_length > std::u32::MAX as usize {
                    return Err(crate::error::Error::ObjectIsTooBigForEncoding {
                        size: string_length,
                        max_size: std::u32::MAX as usize,
                    });
                }

                let string_length = string_length as u32;

                let mut block = vec![encoding_type_byte];
                block.append(&mut string_length.to_le_bytes().to_vec());

                let mut data = s.as_bytes().to_vec();
                block.append(&mut data);

                let mut length = encode_total_element_length(block.len())?;
                block.append(&mut length);
                block
            }
            Self::FloatingPoint64Bit(f) => {
                let mut block = vec![encoding_type_byte];

                let mut data = f.to_le_bytes().to_vec();
                block.append(&mut data);

                let mut length = encode_total_element_length(block.len())?;
                block.append(&mut length);
                block
            }
            Self::Boolean(b) => {
                let mut block = vec![encoding_type_byte | (*b as u8)];

                let mut length = encode_total_element_length(block.len())?;
                block.append(&mut length);
                block
            }
            Self::CustomEmbeddedValue(v) => {
                let mut block = vec![encoding_type_byte | *v];

                let mut length = encode_total_element_length(block.len())?;
                block.append(&mut length);
                block
            }
            Self::CustomExtendedValue(v) => {
                let mut block = vec![encoding_type_byte];

                let data_length = v.len();

                if data_length > 0 {
                    let data_length_length = count_bytes_in_number(data_length) as u8;
                    block.append(&mut data_length_length.to_le_bytes().to_vec());
                    let mut data_length_length_bytes = data_length.to_le_bytes().to_vec();
                    while let Some(0) = data_length_length_bytes.last() {
                        data_length_length_bytes.pop();
                    }
                    block.append(&mut data_length_length_bytes);
                    block.append(&mut v.to_vec());
                }

                let mut length = encode_total_element_length(block.len())?;
                block.append(&mut length);
                block
            }
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
            ListpackEntryData::FloatingPoint64Bit(v) => write!(f, "{v}"),
            ListpackEntryData::Boolean(b) => write!(f, "{b}"),
            ListpackEntryData::CustomEmbeddedValue(v) => write!(f, "{v}"),
            ListpackEntryData::CustomExtendedValue(v) => write!(f, "{v:?}"),
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
        } else if let Some(data) = data.get_f64() {
            Ok(Self::Float(data))
        } else if let Some(data) = data.get_bool() {
            Ok(Self::Boolean(data))
        } else if let Some(data) = data.get_custom_embedded() {
            Ok(Self::CustomEmbeddedValue(data))
        } else if let Some(data) = data.get_custom_extended() {
            Ok(Self::CustomExtendedValue(data))
        } else {
            Err(crate::error::Error::UnknownEncodingType {
                encoding_byte: data.encoding_type().into(),
            })
        }
    }
}

macro_rules! impl_listpack_entry_data_from_integer {
    ($($t:ty),*) => {
        $(
            impl From<$t> for ListpackEntryData<'_> {
                fn from(n: $t) -> Self {
                    let n = n as i64;

                    if (0..=127).contains(&n) {
                        Self::SmallUnsignedInteger(n as u8)
                    } else if (-4096..=4095).contains(&n) {
                        Self::SignedInteger13Bit(n as i16)
                    } else if (-32_768..=32_767).contains(&n) {
                        Self::SignedInteger16Bit(n as i16)
                    } else if (-8_388_608..=8_388_607).contains(&n) {
                        Self::SignedInteger24Bit(n as i32)
                    } else if (-2_147_483_648..=2_147_483_647).contains(&n) {
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

impl_listpack_entry_data_from_integer!(i8, i16, i32, i64, u8, u16, u32, u64);

impl<'a> From<&'a str> for ListpackEntryData<'a> {
    fn from(s: &'a str) -> Self {
        let len = s.len();
        if len <= SMALL_STRING_MAXIMUM_LENGTH {
            Self::SmallString(s)
        } else if len <= MEDIUM_STRING_MAXIMUM_LENGTH {
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

impl From<f64> for ListpackEntryData<'_> {
    fn from(f: f64) -> Self {
        Self::FloatingPoint64Bit(f)
    }
}

impl From<bool> for ListpackEntryData<'_> {
    fn from(b: bool) -> Self {
        Self::Boolean(b)
    }
}

impl<'a> From<&'a [u8]> for ListpackEntryData<'a> {
    fn from(v: &'a [u8]) -> Self {
        Self::CustomExtendedValue(v)
    }
}

impl<'a> From<ListpackEntryInsert<'a>> for ListpackEntryData<'a> {
    fn from(insert: ListpackEntryInsert<'a>) -> Self {
        match insert {
            ListpackEntryInsert::String(s) => Self::from(s),
            ListpackEntryInsert::Integer(i) => Self::from(i),
            ListpackEntryInsert::Float(f) => Self::from(f),
            ListpackEntryInsert::Boolean(b) => Self::from(b),
            ListpackEntryInsert::CustomEmbeddedValue(v) => Self::CustomEmbeddedValue(v),
            ListpackEntryInsert::CustomExtendedValue(v) => Self::from(v),
        }
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
    /// let mut listpack: Listpack = Listpack::default();
    /// listpack.push("Hello");
    /// let entry = listpack.get(0).unwrap();
    /// let ptr = unsafe { entry.as_ptr() };
    /// ```
    #[inline]
    pub fn as_ptr(&self) -> *const u8 {
        self as *const _ as *const u8
    }

    /// Returns the byte (raw) representation of the encoding type.
    ///
    /// # Example
    ///
    /// ```
    /// use listpack_redis::Listpack;
    ///
    /// let mut listpack: Listpack = Listpack::default();
    /// listpack.push("Hello");
    /// let entry = listpack.get(0).unwrap();
    /// let encoding_type = unsafe { entry.get_encoding_type_raw() };
    /// ```
    #[inline]
    pub fn get_encoding_type_raw(&self) -> u8 {
        unsafe { std::ptr::read_unaligned(self.as_ptr()) }
    }

    /// Returns a byte slice of the entry, including its encoding type,
    /// data and the total-element-length byte(s).
    ///
    /// # Example
    ///
    /// ```
    /// use listpack_redis::Listpack;
    ///
    /// let mut listpack: Listpack = Listpack::default();
    /// listpack.push("Hello");
    /// let entry = listpack.get(0).unwrap();
    /// let bytes = entry.as_slice();
    /// assert_eq!(bytes, &[0b10000101, b'H', b'e', b'l', b'l', b'o', 6]);
    /// assert_eq!(bytes.len(), 7);
    /// ```
    #[inline]
    pub fn as_slice(&self) -> &[u8] {
        let len = self.total_bytes();
        unsafe { std::slice::from_raw_parts(self.as_ptr(), len) }
    }

    /// Returns a mutable byte slice to the entry.
    ///
    /// # Safety
    ///
    /// This method is unsafe because it allows for the modification of
    /// the entry's data, which can lead to undefined behaviour if not
    /// handled correctly.
    ///
    /// # Example
    ///
    /// ```
    /// use listpack_redis::Listpack;
    ///
    /// let mut listpack: Listpack = Listpack::default();
    /// listpack.push("Hello");
    /// let entry = listpack.get(0).unwrap();
    /// let bytes = unsafe { entry.as_slice_mut() };
    /// bytes[1] = b'W';
    /// bytes[2] = b'o';
    /// bytes[3] = b'r';
    /// bytes[4] = b'l';
    /// bytes[5] = b'd';
    /// assert_eq!(entry.to_string(), "World");
    #[inline]
    #[allow(clippy::mut_from_ref)]
    pub unsafe fn as_slice_mut(&self) -> &mut [u8] {
        let len = self.total_bytes();
        std::slice::from_raw_parts_mut(self.as_ptr().cast_mut(), len)
    }

    /// Returns the encoding type of the entry, parsed from the byte.
    ///
    /// # Example
    ///
    /// ```
    /// use listpack_redis::Listpack;
    ///
    /// let mut listpack: Listpack = Listpack::default();
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
            ListpackEntryEncodingType::SmallUnsignedInteger => {
                Some((unsafe { std::slice::from_raw_parts(ptr, 1) }, 2))
            }
            ListpackEntryEncodingType::SmallString => {
                let len = (encoding_type_byte & 0b00111111) as usize;
                let data = unsafe {
                    let data = std::slice::from_raw_parts(ptr, len);
                    let total_bytes = len + Self::ENCODING_TYPE_BYTE_LENGTH + 1;
                    (data, total_bytes)
                };
                Some(data)
            }
            ListpackEntryEncodingType::ComplexType(subencoding_type) => match subencoding_type {
                ListpackEntrySubencodingType::SignedInteger13Bit => {
                    let data = unsafe {
                        let data = std::slice::from_raw_parts(ptr, 2);
                        // The encoding byte + 5 bits of the integer,
                        // the 8 bits of the integer,
                        // the total length of the data block.
                        let total_bytes = Self::ENCODING_TYPE_BYTE_LENGTH + 1 + 1;
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
                        let object_length = len + extra_length;
                        let total_bytes =
                            object_length + calculate_total_element_length(object_length);
                        (data, total_bytes)
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
                        let object_length = len + extra_length;
                        let total_bytes =
                            object_length + calculate_total_element_length(object_length);
                        (data, total_bytes)
                    };
                    Some(data)
                }
                ListpackEntrySubencodingType::SignedInteger16Bit => {
                    let data = unsafe {
                        let data = std::slice::from_raw_parts(ptr, 2);
                        let total_bytes = Self::ENCODING_TYPE_BYTE_LENGTH + 2 + 1;
                        (data, total_bytes)
                    };
                    Some(data)
                }
                ListpackEntrySubencodingType::SignedInteger24Bit => {
                    let data = unsafe {
                        let data = std::slice::from_raw_parts(ptr, 3);
                        let total_bytes = Self::ENCODING_TYPE_BYTE_LENGTH + 3 + 1;
                        (data, total_bytes)
                    };
                    Some(data)
                }
                ListpackEntrySubencodingType::SignedInteger32Bit => {
                    let data = unsafe {
                        let data = std::slice::from_raw_parts(ptr, 4);
                        let total_bytes = Self::ENCODING_TYPE_BYTE_LENGTH + 4 + 1;
                        (data, total_bytes)
                    };
                    Some(data)
                }
                // These two share the same structure.
                ListpackEntrySubencodingType::SignedInteger64Bit
                | ListpackEntrySubencodingType::FloatingPoint64Bit => {
                    let data = unsafe {
                        let data = std::slice::from_raw_parts(ptr, 8);
                        let total_bytes = Self::ENCODING_TYPE_BYTE_LENGTH + 8 + 1;
                        (data, total_bytes)
                    };
                    Some(data)
                }
                ListpackEntrySubencodingType::CustomExtendedValue => {
                    let data = unsafe {
                        let extended_length = *ptr.add(0) as usize;

                        let mut data_len = 0;

                        for i in 0..extended_length {
                            data_len = (data_len << 8) | (*ptr.add(1 + i) as usize);
                        }

                        if data_len == 0 {
                            return Some((&[], 3));
                        }

                        let ptr = ptr.add(extended_length);
                        let data = std::slice::from_raw_parts(ptr.add(1), data_len);
                        let extra_length = Self::ENCODING_TYPE_BYTE_LENGTH + extended_length;
                        let object_length = data_len + extra_length;
                        let total_bytes =
                            object_length + calculate_total_element_length(object_length);
                        (data, total_bytes)
                    };
                    Some(data)
                }
                // The value is stored in the entry header itself.
                ListpackEntrySubencodingType::Boolean
                | ListpackEntrySubencodingType::CustomEmbeddedValue => {
                    Some((unsafe { std::slice::from_raw_parts(ptr, 1) }, 2))
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
    /// let mut listpack: Listpack = Listpack::default();
    /// listpack.push("Hello");
    /// let entry = listpack.get(0).unwrap();
    /// let data = entry.get_data_raw().unwrap();
    /// ```
    pub fn get_data_raw(&self) -> Option<&[u8]> {
        self.get_data_raw_and_total_bytes().map(|(data, _)| data)
    }

    /// Returns the number of bytes used to represent the entry,
    /// including the encoding byte and the total element length byte(s).
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
    /// let mut listpack: Listpack = Listpack::default();
    /// listpack.push("Hello");
    /// let entry = listpack.get(0).unwrap();
    /// let total_bytes = entry.total_bytes();
    /// // Five ascii characters, plus the encoding type byte, plus
    /// // the total-element-length byte.
    /// assert_eq!(total_bytes, 7);
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
                    let n = (((encoding_type_byte & 0b00011111) as i16) << 8) | (data[0] as i16);
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
                    let n = ((data[1] as i16) << 8) | (data[0] as i16);
                    ListpackEntryData::SignedInteger16Bit(n)
                }
                ListpackEntrySubencodingType::SignedInteger24Bit => {
                    let data = self
                        .get_data_raw()
                        .ok_or(crate::error::Error::MissingDataBlock)?;
                    let n = ((data[2] as i32) << 16) | ((data[1] as i32) << 8) | (data[0] as i32);
                    ListpackEntryData::SignedInteger24Bit(n)
                }
                ListpackEntrySubencodingType::SignedInteger32Bit => {
                    let data = self
                        .get_data_raw()
                        .ok_or(crate::error::Error::MissingDataBlock)?;
                    let n = ((data[3] as i32) << 24)
                        | ((data[2] as i32) << 16)
                        | ((data[1] as i32) << 8)
                        | (data[0] as i32);
                    ListpackEntryData::SignedInteger32Bit(n)
                }
                ListpackEntrySubencodingType::SignedInteger64Bit => {
                    let data = self
                        .get_data_raw()
                        .ok_or(crate::error::Error::MissingDataBlock)?;
                    let n = ((data[7] as i64) << 56)
                        | ((data[6] as i64) << 48)
                        | ((data[5] as i64) << 40)
                        | ((data[4] as i64) << 32)
                        | ((data[3] as i64) << 24)
                        | ((data[2] as i64) << 16)
                        | ((data[1] as i64) << 8)
                        | (data[0] as i64);
                    ListpackEntryData::SignedInteger64Bit(n)
                }
                ListpackEntrySubencodingType::FloatingPoint64Bit => {
                    let data = self
                        .get_data_raw()
                        .ok_or(crate::error::Error::MissingDataBlock)?;
                    let n = f64::from_le_bytes(data.try_into().unwrap());
                    ListpackEntryData::FloatingPoint64Bit(n)
                }
                ListpackEntrySubencodingType::Boolean => {
                    let value = encoding_type_byte & 0b00000001 == 1;
                    ListpackEntryData::Boolean(value)
                }
                ListpackEntrySubencodingType::CustomEmbeddedValue => {
                    let value = encoding_type_byte & 0b00000001;
                    ListpackEntryData::CustomEmbeddedValue(value)
                }
                ListpackEntrySubencodingType::CustomExtendedValue => {
                    let data = self
                        .get_data_raw()
                        .ok_or(crate::error::Error::MissingDataBlock)?;
                    ListpackEntryData::CustomExtendedValue(data)
                }
            },
        })
    }

    /// Returns a reference from a pointer.
    pub(crate) fn ref_from_ptr<'a>(ptr: NonNull<u8>) -> &'a ListpackEntry {
        unsafe { ptr.cast().as_ref() }
    }

    pub(crate) fn ref_from_slice(slice: &[u8]) -> &ListpackEntry {
        unsafe { &*(slice.as_ptr() as *const ListpackEntry) }
    }
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

impl PartialEq<f64> for ListpackEntry {
    fn eq(&self, other: &f64) -> bool {
        self.data()
            .map(|data| data.get_f64() == Some(*other))
            .unwrap_or(false)
    }
}

impl PartialEq<bool> for ListpackEntry {
    fn eq(&self, other: &bool) -> bool {
        self.data()
            .map(|data| data.get_bool() == Some(*other))
            .unwrap_or(false)
    }
}

impl PartialEq<u8> for ListpackEntry {
    fn eq(&self, other: &u8) -> bool {
        self.data()
            .map(|data| data.get_custom_embedded() == Some(*other))
            .unwrap_or(false)
    }
}

impl PartialEq<&[u8]> for ListpackEntry {
    fn eq(&self, other: &&[u8]) -> bool {
        self.data()
            .map(|data| data.get_custom_extended() == Some(*other))
            .unwrap_or(false)
    }
}

impl PartialEq<ListpackEntryInsert<'_>> for ListpackEntry {
    fn eq(&self, other: &ListpackEntryInsert) -> bool {
        match other {
            ListpackEntryInsert::String(s) => self == *s,
            ListpackEntryInsert::Integer(n) => self == n,
            ListpackEntryInsert::Float(f) => self == f,
            ListpackEntryInsert::Boolean(b) => self == b,
            ListpackEntryInsert::CustomEmbeddedValue(v) => *self == *v,
            ListpackEntryInsert::CustomExtendedValue(v) => *self == *v,
        }
    }
}

impl PartialEq<ListpackEntryInsert<'_>> for &ListpackEntry {
    fn eq(&self, other: &ListpackEntryInsert) -> bool {
        match other {
            ListpackEntryInsert::String(s) => *self == *s,
            ListpackEntryInsert::Integer(n) => *self == n,
            ListpackEntryInsert::Float(f) => *self == f,
            ListpackEntryInsert::Boolean(b) => *self == b,
            ListpackEntryInsert::CustomEmbeddedValue(v) => **self == *v,
            ListpackEntryInsert::CustomExtendedValue(v) => **self == *v,
        }
    }
}

impl Eq for ListpackEntry {}

impl std::fmt::Debug for ListpackEntry {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let data = self.data().map_err(|_| std::fmt::Error)?;

        f.debug_struct("ListpackEntry")
            .field("encoding_type_raw", &self.get_encoding_type_raw())
            .field("data", &data)
            .field("total_element_length", &self.total_bytes())
            .finish()
    }
}

impl std::fmt::Display for ListpackEntry {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let data = self.data().map_err(|_| std::fmt::Error)?;

        write!(f, "{data}")
    }
}

impl MemoryConsumption for ListpackEntry {
    fn memory_consumption(&self) -> usize {
        self.total_bytes()
    }
}

/// The allowed types to be inserted into a listpack.
#[derive(Debug, Copy, Clone, PartialEq, PartialOrd)]
pub enum ListpackEntryInsert<'a> {
    /// A string to insert into a listpack.
    String(&'a str),
    /// An integer to insert into a listpack.
    Integer(i64),
    /// A float to insert into a listpack.
    Float(f64),
    /// A boolean to insert into a listpack.
    Boolean(bool),
    /// A custom value to be embedded into an entry in a listpack.
    CustomEmbeddedValue(u8),
    /// A bigger custom value to be inserted into a listpack.
    CustomExtendedValue(&'a [u8]),
}

impl ListpackEntryInsert<'_> {
    /// Returns the full encoded size of the entry, including:
    /// - the encoding byte,
    /// - the data block length.
    /// - the total-element-length byte(s).
    ///
    /// # Example
    ///
    /// ```
    /// use listpack_redis::ListpackEntryInsert;
    ///
    /// let entry = ListpackEntryInsert::String("Hello, world!");
    /// assert_eq!(entry.full_encoded_size(), 15);
    ///
    /// let string = "a".repeat(2usize.pow(32).into());
    /// let entry = ListpackEntryInsert::String(&string);
    /// assert_eq!(entry.full_encoded_size(), 4294967306);
    /// ```
    pub fn full_encoded_size(&self) -> usize {
        match self {
            Self::String(s) => {
                let len = s.len();
                if len <= SMALL_STRING_MAXIMUM_LENGTH {
                    // 1: The length is stored in the encoding byte.
                    // 1: The "total-element-length" byte length.
                    len + 1 + 1
                } else if len <= MEDIUM_STRING_MAXIMUM_LENGTH {
                    // 2: The length is stored in the encoding byte and one
                    // extra byte.
                    //
                    // 2: The "total-element-length" byte length.
                    let object_length = len + 2;

                    object_length + calculate_total_element_length(object_length)
                } else {
                    let object_length = len + 5;

                    object_length + calculate_total_element_length(object_length)
                }
            }
            Self::Integer(n) => {
                if (0..=127).contains(n) {
                    // 1: 7-bit integer => everything is encoded in the
                    // encoding byte.
                    // 1: the total-element-length of one byte.
                    1 + 1
                } else if (-4096..=4095).contains(n) {
                    // 1: encoding byte with 5 bits of size.
                    // 1: 8-bit integer (in total 13-bit integer).
                    // 1: total-byte-length of one byte.
                    3
                } else if (-32768..=32767).contains(n) {
                    // 1: encoding byte.
                    // 2: 16-bit integer.
                    // 1: total-byte-length of one byte.
                    4
                } else if (-8388608..=8388607).contains(n) {
                    // 1: encoding byte.
                    // 3: 24-bit integer.
                    // 1: total-byte-length of one byte.
                    5
                } else if (-2147483648..=2147483647).contains(n) {
                    // 1: encoding byte.
                    // 4: 32-bit integer.
                    // 1: total-byte-length of one byte.
                    6
                } else {
                    // 1: encoding byte.
                    // 8: 64-bit integer.
                    // 1: total-byte-length of one byte.
                    10
                }
            }
            Self::Float(_) => {
                // 1: encoding byte.
                // 8: 64-bit float.
                // 1: total-byte-length of one byte.
                10
            }
            Self::Boolean(_) => {
                // 1: encoding byte and the boolean value.
                // 1: total-byte-length of one byte.
                2
            }
            Self::CustomEmbeddedValue(_) => {
                // 1: encoding byte and the custom value.
                // 1: total-byte-length of one byte.
                2
            }
            Self::CustomExtendedValue(v) => {
                // 1: encoding byte.
                // 1: the length of the extended value (m).
                // 1-m: the extended value length.
                // n: the extended value.
                // 1: total-byte-length of one byte.
                if v.is_empty() {
                    3
                } else {
                    let data_length = v.len();
                    let extended_length = count_bytes_in_number(data_length);
                    2 + extended_length + data_length + 1
                }
            }
        }
    }
}

impl<'a> Encode for ListpackEntryInsert<'a> {
    fn encode(&self) -> Result<Vec<u8>> {
        ListpackEntryData::from(*self).encode()
    }
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
#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub enum ListpackEntryRemoved {
    /// A string which was removed from a listpack.
    String(String),
    /// An integer which was removed from a listpack.
    Integer(i64),
    /// A floating point value which was removed from a listpack.
    Float(f64),
    /// A boolean value which was removed from a listpack.
    Boolean(bool),
    /// A custom embedded value which was removed from a listpack.
    CustomEmbeddedValue(u8),
    /// A custom extended value which was removed from a listpack.
    CustomExtendedValue(Vec<u8>),
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
            Self::Float(n) => write!(f, "{n}"),
            Self::CustomEmbeddedValue(v) => write!(f, "{:?}", v),
            Self::CustomExtendedValue(v) => write!(f, "{:?}", v),
            Self::Boolean(b) => write!(f, "{b}"),
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
        Self::from(ListpackEntry::ref_from_ptr(ptr))
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
            ListpackEntryData::FloatingPoint64Bit(n) => Self::Float(n),
            ListpackEntryData::Boolean(b) => Self::Boolean(b),
            ListpackEntryData::CustomEmbeddedValue(v) => Self::CustomEmbeddedValue(v),
            ListpackEntryData::CustomExtendedValue(v) => Self::CustomExtendedValue(v.to_vec()),
        }
    }
}

impl<'a> From<&'a ListpackEntryRemoved> for ListpackEntryInsert<'a> {
    fn from(removed: &'a ListpackEntryRemoved) -> Self {
        match removed {
            ListpackEntryRemoved::String(s) => Self::String(s),
            ListpackEntryRemoved::Integer(n) => Self::Integer(*n),
            ListpackEntryRemoved::Float(n) => Self::Float(*n),
            ListpackEntryRemoved::Boolean(b) => Self::Boolean(*b),
            ListpackEntryRemoved::CustomEmbeddedValue(v) => Self::CustomEmbeddedValue(*v),
            ListpackEntryRemoved::CustomExtendedValue(v) => Self::CustomExtendedValue(v),
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
pub struct ListpackEntryMutable<'a, Allocator>
where
    Allocator: CustomAllocator,
{
    listpack: &'a mut Listpack<Allocator>,
    entry: &'a ListpackEntry,
    index: usize,
}

impl<'a, Allocator> ListpackEntryMutable<'a, Allocator>
where
    Allocator: CustomAllocator,
{
    /// Creates a new mutable listpack entry reference object.
    pub(crate) fn new(
        listpack: &'a mut Listpack<Allocator>,
        entry: &'a ListpackEntry,
        index: usize,
    ) -> Self {
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

impl<'a, Allocator> Deref for ListpackEntryMutable<'a, Allocator>
where
    Allocator: CustomAllocator,
{
    type Target = ListpackEntry;

    fn deref(&self) -> &Self::Target {
        self.entry
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    mod encoding {
        use super::*;

        #[test]
        fn total_element_length_calculation() {
            assert_eq!(calculate_total_element_length(0), 1);
            assert_eq!(calculate_total_element_length(1), 1);
            assert_eq!(calculate_total_element_length(127), 1);
            assert_eq!(calculate_total_element_length(128), 2);
            assert_eq!(calculate_total_element_length(3000), 2);
            assert_eq!(calculate_total_element_length(16383), 2);
            assert_eq!(calculate_total_element_length(16384), 3);
            assert_eq!(calculate_total_element_length(2097151), 3);
            assert_eq!(calculate_total_element_length(2097152), 4);
            assert_eq!(calculate_total_element_length(268435455), 4);
            assert_eq!(calculate_total_element_length(268435456), 5);
            assert_eq!(calculate_total_element_length(34359738367), 5);
        }

        #[test]
        fn total_element_length() {
            assert_eq!(encode_total_element_length(0).unwrap(), vec![0]);
            assert_eq!(encode_total_element_length(1).unwrap(), vec![1]);
            assert_eq!(
                encode_total_element_length(128).unwrap(),
                // 1, 128
                vec![0b00000001, 0b10000000]
            );
            assert_eq!(
                encode_total_element_length(500).unwrap(),
                // 3, 244
                vec![0b00000011, 0b11110100]
            );

            assert_eq!(
                encode_total_element_length(16383).unwrap(),
                vec![0b01111111, 0b11111111]
            );

            assert_eq!(
                encode_total_element_length(16384).unwrap(),
                vec![0b00000001, 0b10000000, 0b10000000]
            );

            assert_eq!(
                encode_total_element_length(2097151).unwrap(),
                vec![0b01111111, 0b11111111, 0b11111111]
            );

            assert_eq!(
                encode_total_element_length(2097152).unwrap(),
                vec![0b00000001, 0b10000000, 0b10000000, 0b10000000]
            );

            assert_eq!(
                encode_total_element_length(268435455).unwrap(),
                vec![0b01111111, 0b11111111, 0b11111111, 0b11111111]
            );

            assert_eq!(
                encode_total_element_length(268435456).unwrap(),
                vec![0b00000001, 0b10000000, 0b10000000, 0b10000000, 0b10000000]
            );

            assert_eq!(
                encode_total_element_length(34359738367).unwrap(),
                vec![0b01111111, 0b11111111, 0b11111111, 0b11111111, 0b11111111]
            );
        }

        #[test]
        fn entry_bool() {
            let entry = ListpackEntryInsert::Boolean(false);
            let encoded = entry.encode().unwrap();
            let decoded = ListpackEntry::ref_from_slice(encoded.as_slice());
            let ty = decoded.encoding_type().unwrap();
            assert_eq!(
                ty,
                ListpackEntryEncodingType::ComplexType(ListpackEntrySubencodingType::Boolean)
            );
            assert!(!decoded.data().unwrap().get_bool().unwrap());

            let entry = ListpackEntryInsert::Boolean(true);
            let encoded = entry.encode().unwrap();
            let decoded = ListpackEntry::ref_from_slice(encoded.as_slice());
            assert!(decoded.data().unwrap().get_bool().unwrap());
        }

        #[test]
        fn entry_f64() {
            let entry = ListpackEntryInsert::Float(55.66f64);
            let encoded = entry.encode().unwrap();
            let decoded = ListpackEntry::ref_from_slice(encoded.as_slice());
            let ty = decoded.encoding_type().unwrap();
            assert_eq!(
                ty,
                ListpackEntryEncodingType::ComplexType(
                    ListpackEntrySubencodingType::FloatingPoint64Bit
                )
            );
            assert_eq!(decoded.data().unwrap().get_f64().unwrap(), 55.66f64);
        }

        #[test]
        fn entry_custom_embedded() {
            let entry = ListpackEntryInsert::CustomEmbeddedValue(0);
            let encoded = entry.encode().unwrap();
            let decoded = ListpackEntry::ref_from_slice(encoded.as_slice());
            let ty = decoded.encoding_type().unwrap();
            assert_eq!(
                ty,
                ListpackEntryEncodingType::ComplexType(
                    ListpackEntrySubencodingType::CustomEmbeddedValue
                )
            );
            assert_eq!(decoded.data().unwrap().get_custom_embedded().unwrap(), 0);
        }

        #[test]
        fn entry_custom_extended_non_empty() {
            let array = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9];
            let entry = ListpackEntryInsert::CustomExtendedValue(&array);
            let encoded = entry.encode().unwrap();
            let decoded = ListpackEntry::ref_from_slice(encoded.as_slice());
            let ty = decoded.encoding_type().unwrap();
            assert_eq!(
                ty,
                ListpackEntryEncodingType::ComplexType(
                    ListpackEntrySubencodingType::CustomExtendedValue
                )
            );
            assert_eq!(
                decoded.data().unwrap().get_custom_extended().unwrap(),
                &array
            );
            assert_eq!(decoded.total_bytes(), 13);
        }

        #[test]
        fn entry_custom_extended_empty() {
            let array = [];
            let entry = ListpackEntryInsert::CustomExtendedValue(&array);
            let encoded = entry.encode().unwrap();
            let decoded = ListpackEntry::ref_from_slice(encoded.as_slice());
            let ty = decoded.encoding_type().unwrap();
            assert_eq!(
                ty,
                ListpackEntryEncodingType::ComplexType(
                    ListpackEntrySubencodingType::CustomExtendedValue
                )
            );
            assert_eq!(
                decoded.data().unwrap().get_custom_extended().unwrap(),
                &array
            );
            assert_eq!(decoded.total_bytes(), 3);
        }

        #[test]
        fn entry_u7() {
            let entry = ListpackEntryInsert::Integer(15);
            let encoded = entry.encode().unwrap();
            let decoded = ListpackEntry::ref_from_slice(encoded.as_slice());
            assert_eq!(decoded.data().unwrap().get_u7().unwrap(), 15);
        }

        #[test]
        fn entry_i13() {
            let entry = ListpackEntryInsert::Integer(4095);
            let encoded = entry.encode().unwrap();
            let decoded = ListpackEntry::ref_from_slice(encoded.as_slice());
            assert_eq!(decoded.data().unwrap().get_i13().unwrap(), 4095);
        }

        #[test]
        fn entry_i16() {
            let entry = ListpackEntryInsert::Integer(10000);
            let encoded = entry.encode().unwrap();
            let decoded = ListpackEntry::ref_from_slice(encoded.as_slice());
            assert_eq!(decoded.data().unwrap().get_i16().unwrap(), 10000);
        }

        #[test]
        fn entry_i24() {
            let entry = ListpackEntryInsert::Integer(8388607);
            let encoded = entry.encode().unwrap();
            let decoded = ListpackEntry::ref_from_slice(encoded.as_slice());
            assert_eq!(decoded.data().unwrap().get_i24().unwrap(), 8388607);
        }

        #[test]
        fn entry_i32() {
            let entry = ListpackEntryInsert::Integer(2147483647);
            let encoded = entry.encode().unwrap();
            let decoded = ListpackEntry::ref_from_slice(encoded.as_slice());
            assert_eq!(decoded.data().unwrap().get_i32().unwrap(), 2147483647);
        }

        #[test]
        fn entry_i64() {
            let entry = ListpackEntryInsert::Integer(2147483648);
            let encoded = entry.encode().unwrap();
            let decoded = ListpackEntry::ref_from_slice(encoded.as_slice());
            assert_eq!(decoded.data().unwrap().get_i64().unwrap(), 2147483648);
        }

        #[test]
        fn entry_small_string() {
            let entry = ListpackEntryInsert::String("Hello, world!");
            let encoded = entry.encode().unwrap();
            let decoded = ListpackEntry::ref_from_slice(encoded.as_slice());
            assert_eq!(
                decoded.data().unwrap().get_small_str().unwrap(),
                "Hello, world!"
            );
        }

        #[test]
        fn entry_medium_string() {
            let medium_string = "a".repeat(MEDIUM_STRING_MAXIMUM_LENGTH - 1);
            let entry = ListpackEntryInsert::String(&medium_string);
            let encoded = entry.encode().unwrap();
            let decoded = ListpackEntry::ref_from_slice(encoded.as_slice());
            assert_eq!(
                decoded.data().unwrap().get_medium_str().unwrap(),
                medium_string,
            );
        }

        #[test]
        fn entry_large_string() {
            let large_string = "a".repeat(MEDIUM_STRING_MAXIMUM_LENGTH + 1);
            let entry = ListpackEntryInsert::String(&large_string);
            let encoded = entry.encode().unwrap();
            let decoded = ListpackEntry::ref_from_slice(encoded.as_slice());
            assert_eq!(
                decoded.data().unwrap().get_large_str().unwrap(),
                large_string,
            );
        }
    }
}
