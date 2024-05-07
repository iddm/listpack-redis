//! Compression utilities.

// Allowing the dead code as it might be used as a library.
#![allow(dead_code)]

use std::ops::Deref;

use crate::error::Result;

/// The encoded presentation of the object as a byte array. This is
/// useful particularly for encoding objects into byte arrays for
/// storage in the listpack data structure.
pub trait TryEncode {
    /// Return a byte representation of the object.
    fn try_encode(&self) -> Result<Vec<u8>>;
}

impl<T> TryEncode for T
where
    T: Encode,
{
    fn try_encode(&self) -> Result<Vec<u8>> {
        Ok(self.encode())
    }
}

/// A fail-free encoding trait. This trait is used to encode objects
/// into byte arrays without the possibility of failure.
pub trait Encode {
    /// Encodes the [`Self`] object into a byte array.
    fn encode(&self) -> Vec<u8>;
}

/// Allows to convert the implementing type into a seven-bit variable
/// length integer.
pub trait AsSevenBitVariableLengthInteger {
    /// Converts the object into a seven-bit variable length integer.
    fn as_seven_bit_variable_length_integer(&self) -> SevenBitVariableLengthInteger;
}

/// Allows to convert the implementing type into a seven-bit variable
/// length integer in the reversed format.
pub trait AsSevenBitVariableLengthIntegerReversed {
    /// Converts the object into a seven-bit variable length integer.
    fn as_seven_bit_variable_length_integer_reversed(
        &self,
    ) -> SevenBitVariableLengthIntegerReversed;
}

macro_rules! impl_as_seven_bit_variable_length_integer_for_unsigned_integers {
    ($($type:ty),*) => {
        $(
            impl AsSevenBitVariableLengthInteger for $type {
                fn as_seven_bit_variable_length_integer(&self) -> SevenBitVariableLengthInteger {
                    SevenBitVariableLengthInteger::from(*self)
                }
            }

            impl AsSevenBitVariableLengthIntegerReversed for $type {
                fn as_seven_bit_variable_length_integer_reversed(&self) -> SevenBitVariableLengthIntegerReversed {
                    SevenBitVariableLengthIntegerReversed::from(*self)
                }
            }
        )*
    };
}

impl_as_seven_bit_variable_length_integer_for_unsigned_integers!(u8, u16, u32, u64, u128, usize);

/// The reversed (byte-wise) version of
/// [`SevenBitVariableLengthInteger`].
#[repr(transparent)]
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SevenBitVariableLengthIntegerReversed(Vec<u8>);

impl Default for SevenBitVariableLengthIntegerReversed {
    fn default() -> Self {
        Self(vec![0])
    }
}

impl From<SevenBitVariableLengthInteger> for SevenBitVariableLengthIntegerReversed {
    fn from(value: SevenBitVariableLengthInteger) -> Self {
        Self(value.0.into_iter().rev().collect())
    }
}

impl From<SevenBitVariableLengthIntegerReversed> for SevenBitVariableLengthInteger {
    fn from(value: SevenBitVariableLengthIntegerReversed) -> Self {
        Self(value.0.into_iter().rev().collect())
    }
}

impl SevenBitVariableLengthIntegerReversed {
    /// Return a slice of bytes of the encoded value.
    pub fn get_byte_slice(&self) -> &[u8] {
        &self.0
    }

    /// Return a vector of bytes of the encoded value.
    pub fn get_bytes(&self) -> Vec<u8> {
        self.0.clone()
    }

    /// The maximum number allowed by the variable length integer. As
    /// this is the maximum value, it is always possible to get it back
    /// from the encoded byte sequence.
    fn get_u128(&self) -> u128 {
        let mut value = 0u128;
        let mut shift = 0;

        for byte in self.get_byte_slice() {
            value |= ((byte & 0x7F) as u128) << shift;
            shift += 7;
        }

        value
    }

    /// Attempts to return a `u64` value from the encoded bytes.
    fn try_get_u64(&self) -> Option<u64> {
        let value = self.get_u128();

        if value > u64::MAX as u128 {
            return None;
        }

        Some(value as u64)
    }

    fn try_get_u32(&self) -> Option<u32> {
        let value = self.get_u128();

        if value > u32::MAX as u128 {
            return None;
        }

        Some(value as u32)
    }

    fn try_get_u16(&self) -> Option<u16> {
        let value = self.get_u128();

        if value > u16::MAX as u128 {
            return None;
        }

        Some(value as u16)
    }

    fn try_get_u8(&self) -> Option<u8> {
        let value = self.get_u128();

        if value > u8::MAX as u128 {
            return None;
        }

        Some(value as u8)
    }
}

/// A seven-bit variable-length integer encoding. The encoding is used
/// to compress unsigned integer values into a variable-length byte
/// sequence. The encoding uses the lower 7 bits of each byte to store
/// the integer value, and the highest bit to indicate that there are
/// more bytes to come.
///
/// An example usage of the encoding is to compress the length of an
/// entry in the listpack data structure (see
/// [`crate::entry::ListpackEntry`]).
#[repr(transparent)]
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SevenBitVariableLengthInteger(Vec<u8>);

impl Default for SevenBitVariableLengthInteger {
    /// Implements the default trait for the seven-bit variable-length
    /// integer encoding. The default value is a single byte with the
    /// value of zero, meaning it encoded value is zero.
    fn default() -> Self {
        Self(vec![0])
    }
}

impl SevenBitVariableLengthInteger {
    /// Return a slice of bytes of the encoded value.
    pub fn get_bytes(&self) -> &[u8] {
        &self.0
    }

    /// The maximum number allowed by the variable length integer. As
    /// this is the maximum value, it is always possible to get it back
    /// from the encoded byte sequence.
    fn get_u128(&self) -> u128 {
        let mut value = 0u128;
        let mut shift = 0;

        for byte in self.get_bytes() {
            value |= ((byte & 0x7F) as u128) << shift;
            shift += 7;
        }

        value
    }

    /// Attempts to return a `u64` value from the encoded bytes.
    fn try_get_u64(&self) -> Option<u64> {
        let value = self.get_u128();

        if value > u64::MAX as u128 {
            return None;
        }

        Some(value as u64)
    }

    fn try_get_u32(&self) -> Option<u32> {
        let value = self.get_u128();

        if value > u32::MAX as u128 {
            return None;
        }

        Some(value as u32)
    }

    fn try_get_u16(&self) -> Option<u16> {
        let value = self.get_u128();

        if value > u16::MAX as u128 {
            return None;
        }

        Some(value as u16)
    }

    fn try_get_u8(&self) -> Option<u8> {
        let value = self.get_u128();

        if value > u8::MAX as u128 {
            return None;
        }

        Some(value as u8)
    }
}

impl Deref for SevenBitVariableLengthInteger {
    type Target = [u8];

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

macro_rules! impl_from_for_unsigned_integers {
    ($($type:ty),*) => {
        $(
            impl From<$type> for SevenBitVariableLengthInteger {
                /// Encodes the given unsigned integer value into a
                /// variable-length byte sequence.
                fn from(mut value: $type) -> Self {
                    let mut encoded = Vec::new();

                    loop {
                        // Take the lower 7 bits of the value.
                        let mut byte = (value & 0x7F) as u8;

                        // Shift the value to the right by 7 bits to prepare for the
                        // next iteration.
                        value >>= 7;

                        if value != 0 {
                            // Set the highest bit to indicate that there are more
                            // bytes to come.
                            byte |= 0x80;
                        }

                        // Push the byte to the encoded vector.
                        encoded.push(byte);

                        if value == 0 {
                            break;
                        }
                    }

                    Self(encoded)
                }
            }

            impl From<$type> for SevenBitVariableLengthIntegerReversed {
                /// Encodes the given unsigned integer value into a
                /// variable-length byte sequence.
                fn from(mut value: $type) -> Self {
                    let mut encoded = Vec::new();

                    loop {
                        // Take the lower 7 bits of the value.
                        let mut byte = (value & 0x7F) as u8;

                        // Shift the value to the right by 7 bits to prepare for the
                        // next iteration.
                        value >>= 7;

                        if value != 0 {
                            // Set the highest bit to indicate that there are more
                            // bytes to come.
                            byte |= 0x80;
                        }

                        // Push the byte to the encoded vector.
                        encoded.insert(0, byte);

                        if value == 0 {
                            break;
                        }
                    }

                    Self(encoded)
                }
            }
        )*
    };
}

macro_rules! impl_try_from_for_unsigned_integers_from_seven_bit_variable_length_integer {
    ($($type:ty),*) => {
        $(
            impl TryFrom<SevenBitVariableLengthInteger> for $type {
                type Error = &'static str;

                fn try_from(value: SevenBitVariableLengthInteger) -> Result<$type, Self::Error> {
                    let value = value.get_u128();

                    if value > <$type>::MAX as u128 {
                        return Err("Value is too large to fit into the target type");
                    }

                    Ok(value as $type)
                }
            }

            impl TryFrom<SevenBitVariableLengthIntegerReversed> for $type {
                type Error = &'static str;

                fn try_from(value: SevenBitVariableLengthIntegerReversed) -> Result<$type, Self::Error> {
                    let value = value.get_u128();

                    if value > <$type>::MAX as u128 {
                        return Err("Value is too large to fit into the target type");
                    }

                    Ok(value as $type)
                }
            }
        )*
    };
}

impl_from_for_unsigned_integers!(u8, u16, u32, u64, u128, usize);
impl_try_from_for_unsigned_integers_from_seven_bit_variable_length_integer!(
    u8, u16, u32, u64, u128, usize
);

impl<T: Encode> From<T> for SevenBitVariableLengthInteger {
    fn from(value: T) -> Self {
        Self(value.encode())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    mod seven_bit_normal {
        use super::*;

        #[test]
        fn try_from_integers() {
            let value = 127u8;
            let encoded = SevenBitVariableLengthInteger::from(value);
            let decoded = u8::try_from(encoded).unwrap();
            assert_eq!(value, decoded);

            let value = 16383u16;
            let encoded = SevenBitVariableLengthInteger::from(value);
            let decoded = u16::try_from(encoded).unwrap();
            assert_eq!(value, decoded);

            let value = 2097151u32;
            let encoded = SevenBitVariableLengthInteger::from(value);
            let decoded = u32::try_from(encoded).unwrap();
            assert_eq!(value, decoded);

            let value = 268435455u64;
            let encoded = SevenBitVariableLengthInteger::from(value);
            let decoded = u64::try_from(encoded).unwrap();
            assert_eq!(value, decoded);

            let value = 34359738367u64;
            let encoded = SevenBitVariableLengthInteger::from(value);
            let decoded = u64::try_from(encoded).unwrap();
            assert_eq!(value, decoded);
        }

        #[test]
        fn encode_zero() {
            assert_eq!(
                0u8.as_seven_bit_variable_length_integer().get_bytes(),
                vec![0]
            );
        }

        #[test]
        fn encode_small_number() {
            assert_eq!(
                127u8.as_seven_bit_variable_length_integer().get_bytes(),
                vec![127]
            );
        }

        #[test]
        fn encode_medium_number() {
            assert_eq!(
                128u8.as_seven_bit_variable_length_integer().get_bytes(),
                vec![0x80, 1]
            );
        }

        #[test]
        fn encode_large_number() {
            assert_eq!(
                16383u16.as_seven_bit_variable_length_integer().get_bytes(),
                vec![0xFF, 0x7F]
            );
        }

        #[test]
        fn encode_very_large_number() {
            assert_eq!(
                2097151u32
                    .as_seven_bit_variable_length_integer()
                    .get_bytes(),
                vec![0xFF, 0xFF, 0x7F]
            );
        }

        #[test]
        fn encode_huge_number() {
            assert_eq!(
                268435455u64
                    .as_seven_bit_variable_length_integer()
                    .get_bytes(),
                vec![0xFF, 0xFF, 0xFF, 0x7F]
            );
        }

        #[test]
        fn encode_extremely_large_number() {
            assert_eq!(
                34359738367u64
                    .as_seven_bit_variable_length_integer()
                    .get_bytes(),
                vec![0xFF, 0xFF, 0xFF, 0xFF, 0x7F]
            );
        }
    }

    mod seven_bit_reversed {
        use super::*;

        #[test]
        fn try_from_integers() {
            let value = 127u8;
            let encoded = SevenBitVariableLengthIntegerReversed::from(value);
            let decoded = u8::try_from(encoded).unwrap();
            assert_eq!(value, decoded);

            let value = 16383u16;
            let encoded = SevenBitVariableLengthIntegerReversed::from(value);
            let decoded = u16::try_from(encoded).unwrap();
            assert_eq!(value, decoded);

            let value = 2097151u32;
            let encoded = SevenBitVariableLengthIntegerReversed::from(value);
            let decoded = u32::try_from(encoded).unwrap();
            assert_eq!(value, decoded);

            let value = 268435455u64;
            let encoded = SevenBitVariableLengthIntegerReversed::from(value);
            let decoded = u64::try_from(encoded).unwrap();
            assert_eq!(value, decoded);

            let value = 34359738367u64;
            let encoded = SevenBitVariableLengthIntegerReversed::from(value);
            let decoded = u64::try_from(encoded).unwrap();
            assert_eq!(value, decoded);
        }

        #[test]
        fn encode_zero() {
            assert_eq!(
                0u8.as_seven_bit_variable_length_integer_reversed()
                    .get_bytes(),
                vec![0]
            );
        }

        #[test]
        fn encode_small_number() {
            assert_eq!(
                127u8
                    .as_seven_bit_variable_length_integer_reversed()
                    .get_bytes(),
                vec![127]
            );
        }

        #[test]
        fn encode_medium_number() {
            assert_eq!(
                128u8
                    .as_seven_bit_variable_length_integer_reversed()
                    .get_bytes(),
                vec![1, 0x80]
            );
        }

        #[test]
        fn encode_large_number() {
            assert_eq!(
                16383u16
                    .as_seven_bit_variable_length_integer_reversed()
                    .get_bytes(),
                vec![0x7F, 0xFF]
            );
        }

        #[test]
        fn encode_very_large_number() {
            assert_eq!(
                2097151u32
                    .as_seven_bit_variable_length_integer_reversed()
                    .get_bytes(),
                vec![0x7F, 0xFF, 0xFF]
            );
        }

        #[test]
        fn encode_huge_number() {
            assert_eq!(
                268435455u64
                    .as_seven_bit_variable_length_integer_reversed()
                    .get_bytes(),
                vec![0x7F, 0xFF, 0xFF, 0xFF]
            );
        }
    }
}
