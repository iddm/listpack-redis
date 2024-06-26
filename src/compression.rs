//! Compression utilities.

// Allowing the dead code as it might be used as a library.
#![allow(dead_code)]

use std::{
    iter::Product,
    ops::{
        Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Deref, Div,
        DivAssign, Mul, MulAssign, Not, Rem, RemAssign, Sub, SubAssign,
    },
    ptr::NonNull,
};

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

/// A struct containing the number of bytes that are unused in the
/// virtual memory addressing.
#[repr(transparent)]
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct VirtualMemoryUnusedBitsCount(u8);

impl Deref for VirtualMemoryUnusedBitsCount {
    type Target = u8;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl std::fmt::Display for VirtualMemoryUnusedBitsCount {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} unused bits", self.0)
    }
}

// A compile-time function to parse a number from string.
const fn parse_usize_from_str(string: &str) -> usize {
    let mut value: usize = 0;
    let mut bytes = string.as_bytes();

    while let [byte, rest @ ..] = bytes {
        bytes = rest;
        if let b'0'..=b'9' = byte {
            value *= 10;
            value += (*byte - b'0') as usize;
        } else {
            panic!("The provided string is not a number.")
        }
    }

    value
}

/// The actual maximum number of unused bits in the virtual memory
/// addressing. This value is determined by the CPU architecture and
/// the operating system. The value of this object must remain private
/// and only exposed via the [`VirtualMemoryUnusedBitsCount`] type.
///
/// The value is set at compile-time, as the target architecture is
/// known at compile-time and must not change during the runtime.
const ACTUAL_MAXIMUM_UNUSED_BITS_COUNTS_AT_COMPILE_TIME: u8 =
    parse_usize_from_str(env!("VIRTUAL_ADDRESS_UNUSED_SIZE")) as u8;

/// The minimum mappable address offset. This value is set at
/// compile-time but may be changed at runtime.
///
/// See <https://github.com/torvalds/linux/blob/master/mm/Kconfig#L708>
/// , section `"config DEFAULT_MMAP_MIN_ADDR"` for more information.
pub const MINIMUM_MAPPABLE_ADDRESS_OFFSET: usize =
    parse_usize_from_str(env!("MINIMUM_MAPPABLE_ADDRESS_OFFSET"));

impl VirtualMemoryUnusedBitsCount {
    /// To be on the safe side, the implementor should consider a lower
    /// value: the maximum value used by the pointers is 48 bits, but,
    /// as it depends on the architecture, the implementor must choose
    /// accordingly how many bytes will be used as a storage to avoid
    /// corrupting the pointer value.
    ///
    /// The maximum number of used bits I've seen was 52.
    pub const MAXIMUM_UNUSED_BITS_COUNTS: Self = Self::SIXTEEN;

    /// This is the maximum safe number of unused bits. This number is
    /// taken from the current CPU architectures capabilities. One of
    /// the architectures uses 52 bits of the virtual memory addressing,
    /// this is where this number comes from.
    ///
    /// For the reference:
    /// - `ARMv8` architecture uses `52` bits.
    /// - `x86_64` uses `48` bits.
    /// - Apple Silicon uses `47` bits.
    ///
    /// This number is highly likely to be always safe to use.
    pub const SAFE_UNUSED_BITS_COUNTS: Self = Self::TWELVE;

    /// The minimum number is obviously 1.
    pub const MINIMUM_UNUSED_BITS_COUNTS: Self = Self::ONE;

    /// The range of unused bits.
    pub const UNUSED_BITS_RANGE: std::ops::RangeInclusive<Self> =
        Self::MINIMUM_UNUSED_BITS_COUNTS..=Self::MAXIMUM_UNUSED_BITS_COUNTS;

    /// One bit unused.
    pub const ONE: Self = Self(1);
    /// Two bits unused.
    pub const TWO: Self = Self(2);
    /// Three bits unused.
    pub const THREE: Self = Self(3);
    /// Four bits unused.
    pub const FOUR: Self = Self(4);
    /// Five bits unused.
    pub const FIVE: Self = Self(5);
    /// Six bits unused.
    pub const SIX: Self = Self(6);
    /// Seven bits unused.
    pub const SEVEN: Self = Self(7);
    /// Eight bits unused.
    pub const EIGHT: Self = Self(8);
    /// Nine bits unused.
    pub const NINE: Self = Self(9);
    /// Ten bits unused.
    pub const TEN: Self = Self(10);
    /// Eleven bits unused.
    pub const ELEVEN: Self = Self(11);
    /// Twelve bits unused.
    pub const TWELVE: Self = Self(12);
    /// Thirteen bits unused.
    pub const THIRTEEN: Self = Self(13);
    /// Fourteen bits unused.
    pub const FOURTEEN: Self = Self(14);
    /// Fifteen bits unused.
    pub const FIFTEEN: Self = Self(15);
    /// Sixteen bits unused.
    pub const SIXTEEN: Self = Self(16);

    /// Creates a new instance of the virtual memory unused bytes count.
    pub fn new(count: u8) -> Self {
        if Self::UNUSED_BITS_RANGE.contains(&Self(count)) {
            Self(count)
        } else {
            panic!(
                "The number of unused bits must be in the range of {}..={}",
                Self::MINIMUM_UNUSED_BITS_COUNTS,
                Self::MAXIMUM_UNUSED_BITS_COUNTS
            );
        }
    }

    /// Returns the number of bytes that are unused in the virtual
    /// memory addressing.
    pub const fn get_count(self) -> u8 {
        self.0
    }

    /// Returns the number of bytes that are unused in the virtual
    /// memory as a [`usize`] value (see
    /// [`Self::get_count`]).
    pub const fn get_count_usize(self) -> usize {
        self.0 as usize
    }

    /// Returns the number of bits that are **used** in the virtual
    /// memory addressing of the current CPU architecture this program
    /// is running on. The function runs at runtime.
    pub fn get_actual_virtual_address_size() -> Result<u8, &'static str> {
        // Read the /proc/cpuinfo file, find there the value for the
        // "Address sizes" field, and return that number.
        // An example string:
        //
        // "address sizes	: 48 bits physical, 48 bits virtual"
        //
        // we return the number 48.

        let address_sizes = std::fs::read_to_string("/proc/cpuinfo")
            .map_err(|_| "Couldn't read the /proc/cpuinfo file.")?;

        let address_sizes = address_sizes
            .lines()
            .find(|line| line.starts_with("address sizes"))
            .ok_or("The 'address sizes' field is not found in the /proc/cpuinfo file.")?;

        let address_sizes = address_sizes
            .split(':')
            .nth(1)
            .ok_or("The 'address sizes' field is not found in the /proc/cpuinfo file.")?;

        let address_sizes = address_sizes
            .trim()
            .split(',')
            .find(|part| part.contains("virtual"))
            .ok_or("The 'virtual' part is not found in the 'address sizes' field.")?;

        let address_sizes = address_sizes
            .split_whitespace()
            .find(|part| part.parse::<u8>().is_ok())
            .ok_or("The number of bits is not found in the 'address sizes' field.")?;

        address_sizes
            .parse::<u8>()
            .map_err(|_| "Couldn't extract the virtual address size value.")
    }

    /// Returns the number of bits that are **unused** in the virtual
    /// memory addressing of the current CPU architecture this program
    /// is running on. The function runs at runtime in the runtime
    /// environment and reads the CPU capabilities at runtime.
    pub fn get_actual_unused_virtual_address_size() -> Result<Self, &'static str> {
        const POINTER_SIZE: usize = std::mem::size_of::<usize>() * 8;
        let actual_address_size = Self::get_actual_virtual_address_size()?;

        Ok(Self::new(
            (POINTER_SIZE - actual_address_size as usize) as u8,
        ))
    }

    /// Returns the maximum number of bits that are unused in the
    /// virtual memory addressing determined at compile-time.
    pub const fn get_actual_unused_virtual_address_size_at_compile_time() -> Self {
        Self(ACTUAL_MAXIMUM_UNUSED_BITS_COUNTS_AT_COMPILE_TIME)
    }
}

/// Defines a type that can be used as a pointer tag.
pub trait AbstractPointerTag {
    /// The number of bits the tag occupies. Due to the fact that the
    /// tag is stored in the highest bits of the pointer, the number of
    /// bits is limited to the size of a pointer (physically), but
    /// logically maximum to 16 bits only, as in the 64-bit systems
    /// there are only 48 bits available for virtual addressing, and on
    /// some systems and architectures even less. See
    /// [`VirtualMemoryUnusedBitsCount`] for more information.
    const BIT_LENGTH: VirtualMemoryUnusedBitsCount;

    /// The number of bits in the [`usize`] type.
    const USIZE_BITS_COUNT: usize = std::mem::size_of::<usize>() * 8;

    /// Returns the type tag from the given byte.
    fn from_bytes(bytes: u16) -> Option<Self>
    where
        Self: Sized;

    /// Returns the byte representation of the tag. A tag may consist of
    /// maximum two bytes on a 64-bit system (as the pointer is 8 bytes
    /// and the maximum number of bits that can be used for the tag is
    /// 16). The first byte is the highest byte of the tag,
    fn as_bytes(&self) -> u16;

    /// Returns the extended type tag up to the size of a [usize];
    fn as_usize(&self) -> usize {
        self.as_bytes() as usize
    }

    /// Returns the tag from the given pointer.
    fn from_pointer<T>(pointer: *mut T) -> Option<Self>
    where
        Self: Sized,
    {
        let bit_length = Self::BIT_LENGTH.get_count_usize();

        // Convert the pointer to a usize to perform bitwise operations
        let ptr_value = pointer as usize;

        let mask = generate_bit_mask_with_ones(bit_length);

        // Extract the highest two bits and shift them to the lowest two bits position
        let tag_bytes = (ptr_value >> (Self::USIZE_BITS_COUNT - bit_length)) & mask;

        // Self::from_bytes((tag_bytes as u16) << (16 - bit_length))
        Self::from_bytes(tag_bytes as u16)
    }

    /// Tags the passed pointer with the value of this tag.
    fn tag_pointer<T>(&self, pointer: *mut T) -> *mut T
    where
        Self: Sized,
    {
        tag_pointer(pointer, self)
    }
}

/// The tag which a pointer can have to store the information regarding
/// its allocation: whether it needs to be deallocated or not.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum AllocationPointerTag {
    /// Means the pointer is owned and should be deallocated.
    Owned,
    /// Means the pointer is borrowed and should not be deallocated.
    Borrowed,
}

impl AbstractPointerTag for AllocationPointerTag {
    /// The number of bits the allocation tag occupies.
    const BIT_LENGTH: VirtualMemoryUnusedBitsCount = VirtualMemoryUnusedBitsCount::ONE;

    fn from_bytes(bytes: u16) -> Option<Self> {
        match bytes {
            0 => Some(Self::Owned),
            0b0000_0000_0000_0001 => Some(Self::Borrowed),
            _ => None,
        }
    }

    fn as_bytes(&self) -> u16 {
        match self {
            Self::Owned => 0,
            Self::Borrowed => 0b0000_0000_0000_0001,
        }
    }
}

fn set_higher_bit<T, Tag>(ptr: *mut T, tag: &Tag) -> *mut T
where
    Tag: AbstractPointerTag,
{
    let bits = tag.as_bytes();

    set_higher_bits(ptr, bits as usize, 1)
}

/// Generates a bit mask with the given number of bits set to one.
///
/// # Arguments
///
/// * `bit_length` - The number of bits to set to one.
///
/// # Returns
///
/// A bit mask with the given number of bits set to one.
///
/// # Panics
///
/// Panics if the `bit_length` is greater than the number of bits in a
/// `usize`.
///
/// # Example
///
/// ```
/// use listpack_redis::compression::generate_bit_mask_with_ones;
///
/// let mask = generate_bit_mask_with_ones(4);
/// assert_eq!(mask, 0b00001111);
/// ```
pub fn generate_bit_mask_with_ones(bit_length: usize) -> usize {
    (1 << bit_length) - 1
}

/// Sets the higher bits of the pointer to the given bits provided in
/// the argument. The number of bits to set is determined by the
/// `bit_length` argument.
///
/// # Arguments
///
/// * `ptr` - The pointer to set the higher bits.
/// * `bits` - The bits to set (the lower bits are taken).
/// * `bit_length` - The number of bits to set.
///
/// # Returns
///
/// The pointer with the higher bits set.
///
/// # Example
///
/// ```
/// use listpack_redis::compression::set_higher_bits;
///
/// let ptr = 0x1234 as *mut u8;
///
/// let new_ptr = set_higher_bits(ptr, 0b101, 3);
///
/// assert_eq!(new_ptr as usize, 0x1234 | 0b101 << (std::mem::size_of::<usize>() * 8 - 3));
/// ```
pub fn set_higher_bits<T>(ptr: *mut T, bits: usize, bit_length: usize) -> *mut T {
    if bit_length == 0 {
        return ptr;
    }

    let mask = generate_bit_mask_with_ones(bit_length);

    // Ensure the bits have only the allowed range of values.
    let bits = bits & mask;

    // Get the pointer value as a usize
    let ptr_value = ptr as *const u8 as usize;

    // Get the number of bits in a usize
    const USIZE_BITS_COUNT: usize = std::mem::size_of::<usize>() * 8;

    // Create a mask to zero out the required bits
    let zero_mask = !(mask << (USIZE_BITS_COUNT - bit_length));

    // Clear the highest two bits of the pointer value
    let cleared_ptr_value = ptr_value & zero_mask;

    // Set the highest two bits using the provided `as_byte` value
    let new_ptr_value = cleared_ptr_value | (bits << (USIZE_BITS_COUNT - bit_length));

    // Convert back to a pointer and return
    new_ptr_value as *mut T
}

/// Sets the tag ([`AbstractPointerTag`]) to the pointer.
pub fn tag_pointer<T, Tag>(pointer: *mut T, tag: &Tag) -> *mut T
where
    Tag: AbstractPointerTag,
{
    set_higher_bits(pointer, tag.as_usize(), Tag::BIT_LENGTH.get_count_usize())
}

/// Set the highest bits to zeroes. The number of the highest bits to
/// set to zero is determined by the target type's tag's
/// [`AbstractPointerTag::BIT_LENGTH`] value.
pub fn untag_pointer<T, Tag>(pointer: *mut T) -> *mut T
where
    Tag: AbstractPointerTag,
{
    set_higher_bits(pointer, 0, Tag::BIT_LENGTH.get_count_usize())
}

/// Returns the tag of the pointer.
pub fn get_pointer_tag<T, Tag>(pointer: *mut T) -> Option<Tag>
where
    Tag: AbstractPointerTag,
{
    Tag::from_pointer(pointer)
}

/// A trait for the types which can be tagged with a tag.
pub trait Taggable<Tag> {
    /// Tags the value with the given tag and returns the tagged value.
    fn tag(&self, tag: Tag) -> Self;

    /// Tags the value in place.
    fn tag_in_place(&mut self, tag: Tag);

    /// Returns the type tag of the value. It may return [`None`] in
    /// case the type tag is not stored.
    fn get_tag(&self) -> Option<Tag>;

    /// Returns the value with the type tag removed.
    fn remove_tag(&self) -> Self;

    /// Removes the type tag in place.
    fn remove_tag_in_place(&mut self);
}

impl<T, Tag> Taggable<Tag> for *mut T
where
    Tag: AbstractPointerTag,
{
    fn tag(&self, tag: Tag) -> Self {
        tag_pointer(*self, &tag)
    }

    fn tag_in_place(&mut self, tag: Tag) {
        *self = tag_pointer(*self, &tag);
    }

    fn get_tag(&self) -> Option<Tag> {
        get_pointer_tag(*self)
    }

    fn remove_tag(&self) -> Self {
        untag_pointer::<T, Tag>(*self)
    }

    fn remove_tag_in_place(&mut self) {
        *self = untag_pointer::<T, Tag>(*self);
    }
}

impl<T, Tag> Taggable<Tag> for NonNull<T>
where
    Tag: AbstractPointerTag,
{
    fn tag(&self, tag: Tag) -> Self {
        NonNull::new(tag_pointer(self.as_ptr(), &tag)).unwrap()
    }

    fn tag_in_place(&mut self, tag: Tag) {
        *self = NonNull::new(tag_pointer(self.as_ptr(), &tag)).unwrap();
    }

    fn get_tag(&self) -> Option<Tag> {
        get_pointer_tag(self.as_ptr())
    }

    fn remove_tag(&self) -> Self {
        NonNull::new(untag_pointer::<T, Tag>(self.as_ptr())).unwrap()
    }

    fn remove_tag_in_place(&mut self) {
        *self = NonNull::new(untag_pointer::<T, Tag>(self.as_ptr())).unwrap();
    }
}

/// Allows to convert the implementing type into a seven-bit variable
/// length integer.
pub trait AsSevenBitVariableLengthInteger {
    /// Converts the object into a seven-bit variable length integer.
    fn as_seven_bit_variable_length_integer(&self) -> SevenBitVariableLengthInteger;
}

/// Allows to convert the implementing type into a seven-bit variable
/// length integer in the reversed format (from right-to-left).
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
    /// Creates a new instance of the seven-bit variable-length integer
    /// (reversed) encoding from a pointer to a byte sequence.
    ///
    /// The pointer is read from right to left.
    ///
    /// # Safety
    ///
    /// The pointer must point to a valid byte sequence that is
    /// correctly encoded as a seven-bit variable-length integer.
    pub unsafe fn from_ptr(ptr: *const u8) -> Self {
        let mut bytes = Vec::new();
        let mut ptr = ptr;

        loop {
            let byte = unsafe { *ptr };

            bytes.insert(0, byte);

            // If the highest bit is not set, then this is the last
            // byte.
            if byte & 0x80 == 0 {
                break;
            }

            ptr = unsafe { ptr.sub(1) };
        }

        Self(bytes)
    }

    /// Returns a slice of bytes of the encoded value.
    pub fn get_byte_slice(&self) -> &[u8] {
        &self.0
    }

    /// Returns a vector of bytes of the encoded value.
    pub fn get_bytes(&self) -> Vec<u8> {
        self.0.clone()
    }

    /// The maximum number allowed by the variable length integer. As
    /// this is the maximum value, it is always possible to get it back
    /// from the encoded byte sequence.
    pub fn get_u128(&self) -> u128 {
        let mut value = 0u128;
        let mut shift = 0;

        // We walk in the reversed order, since the value is stored in
        // the reversed order.
        for byte in self.get_byte_slice().iter().rev() {
            value |= ((byte & 0x7F) as u128) << shift;
            shift += 7;
        }

        value
    }

    /// Attempts to return a `usize` value from the encoded bytes.
    pub fn try_get_usize(&self) -> Option<usize> {
        let value = self.get_u128();

        if value > usize::MAX as u128 {
            return None;
        }

        Some(value as usize)
    }

    /// Attempts to return a `u64` value from the encoded bytes.
    pub fn try_get_u64(&self) -> Option<u64> {
        let value = self.get_u128();

        if value > u64::MAX as u128 {
            return None;
        }

        Some(value as u64)
    }

    /// Attempts to return a `u32` value from the encoded bytes.
    pub fn try_get_u32(&self) -> Option<u32> {
        let value = self.get_u128();

        if value > u32::MAX as u128 {
            return None;
        }

        Some(value as u32)
    }

    /// Attempts to return a `u16` value from the encoded bytes.
    pub fn try_get_u16(&self) -> Option<u16> {
        let value = self.get_u128();

        if value > u16::MAX as u128 {
            return None;
        }

        Some(value as u16)
    }

    /// Attempts to return a `u8` value from the encoded bytes.
    pub fn try_get_u8(&self) -> Option<u8> {
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
/// The value is stored in the left-to-right order.
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
    /// Creates a new instance of the seven-bit variable-length integer
    /// encoding from a pointer to a byte sequence.
    ///
    /// # Safety
    ///
    /// The pointer must point to a valid byte sequence that is
    /// correctly encoded as a seven-bit variable-length integer.
    pub unsafe fn from_ptr(ptr: *const u8) -> Self {
        let mut bytes = Vec::new();
        let mut ptr = ptr;

        loop {
            let byte = unsafe { *ptr };

            bytes.push(byte);

            // If the higher bit is not set, then it is the last byte.
            if byte & 0x80 == 0 {
                break;
            }

            ptr = unsafe { ptr.add(1) };
        }

        Self(bytes)
    }

    /// Returns `true` if it was possible to replace the value in `self`
    /// with the new value without reallocation. If the new value
    /// requires more bytes than the current value, then it is not
    /// possible to replace the value without reallocation, and `false`
    /// is returned.
    pub fn try_set_new_value_without_reallocation<T: Into<Self>>(&mut self, value: T) -> bool {
        let new_value = value.into();

        if new_value.len() > self.len() {
            return false;
        }

        self.0.copy_from_slice(new_value.get_bytes_slice());

        true
    }

    /// A thread-unsafe version of the
    /// [`Self::try_set_new_value_without_reallocation`] method. The
    /// main difference is the absence of the mutable reference to
    /// `self`. This method is useful when the runtime context of the
    /// method is already thread-safe.
    ///
    /// # Safety
    ///
    /// This method is unsafe because it can lead to a data race in
    /// a thread-unsafe context.
    pub unsafe fn try_set_new_value_without_reallocation_thread_unsafe<T: Into<Self>>(
        &self,
        value: T,
    ) -> bool {
        let new_value = value.into();

        if new_value.len() > self.len() {
            return false;
        }

        let ptr = self.0.as_ptr().cast_mut();
        let new_ptr = new_value.0.as_ptr();

        unsafe {
            std::ptr::copy_nonoverlapping(new_ptr, ptr, new_value.len());
        }

        true
    }

    /// Writes the encoded value to the given pointer.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the pointer is valid and points to
    /// a memory location that is at least `self.len()` bytes long.
    pub unsafe fn write_to_ptr(&self, ptr: *mut u8) {
        let mut ptr = ptr;

        for byte in self.get_bytes_slice() {
            unsafe {
                *ptr = *byte;
                ptr = ptr.add(1);
            }
        }
    }

    /// Returns a slice of bytes of the encoded value.
    pub fn get_bytes_slice(&self) -> &[u8] {
        &self.0
    }

    /// Returns a vector of bytes of the encoded value.
    pub fn get_bytes(&self) -> Vec<u8> {
        self.0.clone()
    }

    /// The maximum number allowed by the variable length integer. As
    /// this is the maximum value, it is always possible to get it back
    /// from the encoded byte sequence.
    pub fn get_u128(&self) -> u128 {
        let mut value = 0u128;
        let mut shift = 0;

        for byte in self.get_bytes_slice() {
            value |= ((byte & 0x7F) as u128) << shift;
            shift += 7;
        }

        value
    }

    /// Attempts to return a `usize` value from the encoded bytes.
    pub fn try_get_usize(&self) -> Option<usize> {
        let value = self.get_u128();

        if value > usize::MAX as u128 {
            return None;
        }

        Some(value as usize)
    }

    /// Attempts to return a `u64` value from the encoded bytes.
    pub fn try_get_u64(&self) -> Option<u64> {
        let value = self.get_u128();

        if value > u64::MAX as u128 {
            return None;
        }

        Some(value as u64)
    }

    /// Attempts to return a `u32` value from the encoded bytes.
    pub fn try_get_u32(&self) -> Option<u32> {
        let value = self.get_u128();

        if value > u32::MAX as u128 {
            return None;
        }

        Some(value as u32)
    }

    /// Attempts to return a `u16` value from the encoded bytes.
    pub fn try_get_u16(&self) -> Option<u16> {
        let value = self.get_u128();

        if value > u16::MAX as u128 {
            return None;
        }

        Some(value as u16)
    }

    /// Attempts to return a `u8` value from the encoded bytes.
    pub fn try_get_u8(&self) -> Option<u8> {
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

// TODO: many of the methods can be sometimes be done in-place, instead
// of creating new objects (and allocating those). This might be a good
// optimization to do in the future.
/// Implements the Rust primitive integer traits.
macro_rules! impl_primitive_traits {
    ($($type:ty),*) => {
        $(
        impl<T> Add<T> for $type
        where
            T: Into<$type>,
        {
            type Output = Self;

            fn add(self, other: T) -> Self::Output {
                Self::from(self.get_u128() + other.into().get_u128())
            }
        }

        impl<T> AddAssign<T> for $type
        where
            T: Into<Self>,
        {
            fn add_assign(&mut self, other: T) {
                *self = self.clone().add(other);
            }
        }

        impl<T> BitAnd<T> for $type
        where
            T: Into<Self>,
        {
            type Output = Self;

            fn bitand(self, other: T) -> Self::Output {
                Self::from(self.get_u128() & other.into().get_u128())
            }
        }

        impl<T> BitAndAssign<T> for $type
        where
            T: Into<Self>,
        {
            fn bitand_assign(&mut self, other: T) {
                *self = self.clone().bitand(other);
            }
        }

        impl<T> BitOr<T> for $type
        where
            T: Into<Self>,
        {
            type Output = Self;

            fn bitor(self, other: T) -> Self::Output {
                Self::from(self.get_u128() | other.into().get_u128())
            }
        }

        impl<T> BitOrAssign<T> for $type
        where
            T: Into<Self>,
        {
            fn bitor_assign(&mut self, other: T) {
                *self = self.clone().bitor(other);
            }
        }

        impl<T> BitXor<T> for $type
        where
            T: Into<Self>,
        {
            type Output = Self;

            fn bitxor(self, other: T) -> Self::Output {
                Self::from(self.get_u128() ^ other.into().get_u128())
            }
        }

        impl<T> BitXorAssign<T> for $type
        where
            T: Into<Self>,
        {
            fn bitxor_assign(&mut self, other: T) {
                *self = self.clone().bitxor(other);
            }
        }

        impl<T> Div<T> for $type
        where
            T: Into<Self>,
        {
            type Output = Self;

            fn div(self, other: T) -> Self::Output {
                Self::from(self.get_u128() / other.into().get_u128())
            }
        }

        impl<T> DivAssign<T> for $type
        where
            T: Into<Self>,
        {
            fn div_assign(&mut self, other: T) {
                *self = self.clone().div(other);
            }
        }

        impl<T> Mul<T> for $type
        where
            T: Into<Self>,
        {
            type Output = Self;

            fn mul(self, other: T) -> Self::Output {
                Self::from(self.get_u128() * other.into().get_u128())
            }
        }

        impl<T> MulAssign<T> for $type
        where
            T: Into<Self>,
        {
            fn mul_assign(&mut self, other: T) {
                *self = self.clone().mul(other);
            }
        }

        impl<T> Sub<T> for $type
        where
            T: Into<Self>,
        {
            type Output = Self;

            fn sub(self, other: T) -> Self::Output {
                Self::from(self.get_u128() - other.into().get_u128())
            }
        }

        impl<T> SubAssign<T> for $type
        where
            T: Into<Self>,
        {
            fn sub_assign(&mut self, other: T) {
                *self = self.clone().sub(other);
            }
        }

        impl Not for $type {
            type Output = Self;

            fn not(self) -> Self::Output {
                Self::from(!self.get_u128())
            }
        }

        impl<T> Product<T> for $type
        where
            T: Into<Self>,
        {
            fn product<I>(iter: I) -> Self
            where
                I: Iterator<Item = T>,
            {
                let mut product = 1u128;

                for item in iter {
                    product *= item.into().get_u128();
                }

                Self::from(product)
            }
        }

        impl<T> Rem<T> for $type
        where
            T: Into<Self>,
        {
            type Output = Self;

            fn rem(self, other: T) -> Self::Output {
                Self::from(self.get_u128() % other.into().get_u128())
            }
        }

        impl<T> RemAssign<T> for $type
        where
            T: Into<Self>,
        {
            fn rem_assign(&mut self, other: T) {
                *self = self.clone().rem(other);
            }
        }
        )*
    };
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

impl_primitive_traits!(
    SevenBitVariableLengthInteger,
    SevenBitVariableLengthIntegerReversed
);
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
                0u8.as_seven_bit_variable_length_integer().get_bytes_slice(),
                vec![0]
            );
        }

        #[test]
        fn encode_small_number() {
            assert_eq!(
                127u8
                    .as_seven_bit_variable_length_integer()
                    .get_bytes_slice(),
                vec![127]
            );
        }

        #[test]
        fn encode_medium_number() {
            assert_eq!(
                128u8
                    .as_seven_bit_variable_length_integer()
                    .get_bytes_slice(),
                vec![0x80, 1]
            );
        }

        #[test]
        fn encode_large_number() {
            assert_eq!(
                16383u16
                    .as_seven_bit_variable_length_integer()
                    .get_bytes_slice(),
                vec![0xFF, 0x7F]
            );
        }

        #[test]
        fn encode_very_large_number() {
            assert_eq!(
                2097151u32
                    .as_seven_bit_variable_length_integer()
                    .get_bytes_slice(),
                vec![0xFF, 0xFF, 0x7F]
            );
        }

        #[test]
        fn encode_huge_number() {
            assert_eq!(
                268435455u64
                    .as_seven_bit_variable_length_integer()
                    .get_bytes_slice(),
                vec![0xFF, 0xFF, 0xFF, 0x7F]
            );
        }

        #[test]
        fn encode_extremely_large_number() {
            assert_eq!(
                34359738367u64
                    .as_seven_bit_variable_length_integer()
                    .get_bytes_slice(),
                vec![0xFF, 0xFF, 0xFF, 0xFF, 0x7F]
            );
        }

        #[test]
        fn read_from_ptr() {
            let bytes = vec![0x80, 1];
            let ptr = bytes.as_ptr();

            let encoded = unsafe { SevenBitVariableLengthInteger::from_ptr(ptr) };
            assert_eq!(encoded.get_bytes_slice(), bytes);
            assert_eq!(encoded.get_u128(), 128);

            let bytes = vec![1];
            let ptr = bytes.as_ptr();

            let encoded = unsafe { SevenBitVariableLengthInteger::from_ptr(ptr) };
            assert_eq!(encoded.get_bytes_slice(), bytes);
            assert_eq!(encoded.get_u128(), 1);
        }

        #[test]
        fn add() {
            let value = 127u8.as_seven_bit_variable_length_integer();
            let other = 1u8.as_seven_bit_variable_length_integer();
            let sum = value + other;
            assert_eq!(sum.get_u128(), 128);

            let value = 16383u16.as_seven_bit_variable_length_integer();
            let other = 1u8;

            let sum = value + other;
            assert_eq!(sum.get_u128(), 16384);
        }

        #[test]
        fn add_assign() {
            let mut value = 127u8.as_seven_bit_variable_length_integer();
            let other = 1u8.as_seven_bit_variable_length_integer();
            value += other;
            assert_eq!(value.get_u128(), 128);

            let mut value = 16383u16.as_seven_bit_variable_length_integer();
            let other = 1u8;

            value += other;
            assert_eq!(value.get_u128(), 16384);
        }

        #[test]
        fn bit_and() {
            let value = 0u8.as_seven_bit_variable_length_integer();
            let other = 1u8.as_seven_bit_variable_length_integer();
            let result = value & other;
            assert_eq!(result.get_u128(), 0);

            let value = 16383u16.as_seven_bit_variable_length_integer();
            let other = 1u8;

            let result = value & other;
            assert_eq!(result.get_u128(), 1);
        }

        #[test]
        fn bit_and_assign() {
            let mut value = 0u8.as_seven_bit_variable_length_integer();
            let other = 1u8;
            value &= other;
            assert_eq!(value.get_u128(), 0);

            let mut value = 16383u16.as_seven_bit_variable_length_integer();
            let other = 1u8;

            value &= other;
            assert_eq!(value.get_u128(), 1);
        }

        #[test]
        fn bit_or() {
            let value = 0u8.as_seven_bit_variable_length_integer();
            let other = 1u8;
            let result = value | other;
            assert_eq!(result.get_u128(), 1);

            let value = 16383u16.as_seven_bit_variable_length_integer();
            let other = 1u8;

            let result = value | other;
            assert_eq!(result.get_u128(), 16383);
        }

        #[test]
        fn bit_or_assign() {
            let mut value = 0u8.as_seven_bit_variable_length_integer();
            let other = 1u8;
            value |= other;
            assert_eq!(value.get_u128(), 1);

            let mut value = 16383u16.as_seven_bit_variable_length_integer();
            let other = 1u8;

            value |= other;
            assert_eq!(value.get_u128(), 16383);
        }

        #[test]
        fn bit_xor() {
            let value = 0u8.as_seven_bit_variable_length_integer();
            let other = 1u8;
            let result = value ^ other;
            assert_eq!(result.get_u128(), 1);

            let value = 16383u16.as_seven_bit_variable_length_integer();
            let other = 1u8;

            let result = value ^ other;
            assert_eq!(result.get_u128(), 16382);
        }

        #[test]
        fn bit_xor_assign() {
            let mut value = 0u8.as_seven_bit_variable_length_integer();
            let other = 1u8;
            value ^= other;
            assert_eq!(value.get_u128(), 1);

            let mut value = 16383u16.as_seven_bit_variable_length_integer();
            let other = 1u8;

            value ^= other;
            assert_eq!(value.get_u128(), 16382);
        }

        #[test]
        fn div() {
            let value = 128u8.as_seven_bit_variable_length_integer();
            let other = 2u8;
            let result = value / other;
            assert_eq!(result.get_u128(), 64);

            let value = 16384u16.as_seven_bit_variable_length_integer();
            let other = 2u8;

            let result = value / other;
            assert_eq!(result.get_u128(), 8192);
        }

        #[test]
        fn div_assign() {
            let mut value = 128u8.as_seven_bit_variable_length_integer();
            let other = 2u8;
            value /= other;
            assert_eq!(value.get_u128(), 64);

            let mut value = 16384u16.as_seven_bit_variable_length_integer();
            let other = 2u8;

            value /= other;
            assert_eq!(value.get_u128(), 8192);
        }

        #[test]
        fn mul() {
            let value = 128u8.as_seven_bit_variable_length_integer();
            let other = 2u8;
            let result = value * other;
            assert_eq!(result.get_u128(), 256);

            let value = 16384u16.as_seven_bit_variable_length_integer();
            let other = 2u8;

            let result = value * other;
            assert_eq!(result.get_u128(), 32768);
        }

        #[test]
        fn mul_assign() {
            let mut value = 128u8.as_seven_bit_variable_length_integer();
            let other = 2u8;
            value *= other;
            assert_eq!(value.get_u128(), 256);

            let mut value = 16384u16.as_seven_bit_variable_length_integer();
            let other = 2u8;

            value *= other;
            assert_eq!(value.get_u128(), 32768);
        }

        #[test]
        fn sub() {
            let value = 128u8.as_seven_bit_variable_length_integer();
            let other = 1u8;
            let result = value - other;
            assert_eq!(result.get_u128(), 127);

            let value = 16384u16.as_seven_bit_variable_length_integer();
            let other = 1u8;

            let result = value - other;
            assert_eq!(result.get_u128(), 16383);
        }

        #[test]
        fn sub_assign() {
            let mut value = 128u8.as_seven_bit_variable_length_integer();
            let other = 1u8;
            value -= other;
            assert_eq!(value.get_u128(), 127);

            let mut value = 16384u16.as_seven_bit_variable_length_integer();
            let other = 1u8;

            value -= other;
            assert_eq!(value.get_u128(), 16383);
        }

        #[test]
        fn not() {
            let value = 128u8.as_seven_bit_variable_length_integer();
            let result = !value;
            assert_eq!(result.get_u128(), !128);

            let value = 16384u16.as_seven_bit_variable_length_integer();
            let result = !value;
            assert_eq!(result.get_u128(), !16384);
        }

        #[test]
        fn product() {
            let values = vec![128u8, 2u8, 4u8];

            let product = SevenBitVariableLengthInteger::product(values.into_iter());
            assert_eq!(product.get_u128(), 128 * 2 * 4);
        }

        #[test]
        fn rem() {
            let value = 128u8.as_seven_bit_variable_length_integer();
            let other = 2u8;
            let result = value % other;
            assert_eq!(result.get_u128(), 128 % 2);

            let value = 16384u16.as_seven_bit_variable_length_integer();
            let other = 2u8;

            let result = value % other;
            assert_eq!(result.get_u128(), 16384 % 2);
        }

        #[test]
        fn rem_assign() {
            let mut value = 128u8.as_seven_bit_variable_length_integer();
            let other = 2u8;
            value %= other;
            assert_eq!(value.get_u128(), 128 % 2);

            let mut value = 16384u16.as_seven_bit_variable_length_integer();
            let other = 2u8;

            value %= other;
            assert_eq!(value.get_u128(), 16384 % 2);
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

        #[test]
        fn read_from_ptr() {
            let bytes = vec![1, 0x80];
            let ptr = unsafe { bytes.as_ptr().add(1) };

            let encoded = unsafe { SevenBitVariableLengthIntegerReversed::from_ptr(ptr) };
            assert_eq!(encoded.get_bytes(), bytes);
            assert_eq!(encoded.get_u128(), 128);

            let bytes = vec![1];
            let ptr = bytes.as_ptr();

            let encoded = unsafe { SevenBitVariableLengthIntegerReversed::from_ptr(ptr) };
            assert_eq!(encoded.get_bytes(), bytes);
            assert_eq!(encoded.get_u128(), 1);
        }

        #[test]
        fn add() {
            let value = 127u8.as_seven_bit_variable_length_integer();
            let other = 1u8.as_seven_bit_variable_length_integer();
            let sum = value + other;
            assert_eq!(sum.get_u128(), 128);

            let value = 16383u16.as_seven_bit_variable_length_integer();
            let other = 1u8;

            let sum = value + other;
            assert_eq!(sum.get_u128(), 16384);
        }

        #[test]
        fn add_assign() {
            let mut value = 127u8.as_seven_bit_variable_length_integer();
            let other = 1u8.as_seven_bit_variable_length_integer();
            value += other;
            assert_eq!(value.get_u128(), 128);

            let mut value = 16383u16.as_seven_bit_variable_length_integer();
            let other = 1u8;

            value += other;
            assert_eq!(value.get_u128(), 16384);
        }

        #[test]
        fn bit_and() {
            let value = 0u8.as_seven_bit_variable_length_integer();
            let other = 1u8.as_seven_bit_variable_length_integer();
            let result = value & other;
            assert_eq!(result.get_u128(), 0);

            let value = 16383u16.as_seven_bit_variable_length_integer();
            let other = 1u8;

            let result = value & other;
            assert_eq!(result.get_u128(), 1);
        }

        #[test]
        fn bit_and_assign() {
            let mut value = 0u8.as_seven_bit_variable_length_integer();
            let other = 1u8;
            value &= other;
            assert_eq!(value.get_u128(), 0);

            let mut value = 16383u16.as_seven_bit_variable_length_integer();
            let other = 1u8;

            value &= other;
            assert_eq!(value.get_u128(), 1);
        }

        #[test]
        fn bit_or() {
            let value = 0u8.as_seven_bit_variable_length_integer();
            let other = 1u8;
            let result = value | other;
            assert_eq!(result.get_u128(), 1);

            let value = 16383u16.as_seven_bit_variable_length_integer();
            let other = 1u8;

            let result = value | other;
            assert_eq!(result.get_u128(), 16383);
        }

        #[test]
        fn bit_or_assign() {
            let mut value = 0u8.as_seven_bit_variable_length_integer();
            let other = 1u8;
            value |= other;
            assert_eq!(value.get_u128(), 1);

            let mut value = 16383u16.as_seven_bit_variable_length_integer();
            let other = 1u8;

            value |= other;
            assert_eq!(value.get_u128(), 16383);
        }

        #[test]
        fn bit_xor() {
            let value = 0u8.as_seven_bit_variable_length_integer();
            let other = 1u8;
            let result = value ^ other;
            assert_eq!(result.get_u128(), 1);

            let value = 16383u16.as_seven_bit_variable_length_integer();
            let other = 1u8;

            let result = value ^ other;
            assert_eq!(result.get_u128(), 16382);
        }

        #[test]
        fn bit_xor_assign() {
            let mut value = 0u8.as_seven_bit_variable_length_integer();
            let other = 1u8;
            value ^= other;
            assert_eq!(value.get_u128(), 1);

            let mut value = 16383u16.as_seven_bit_variable_length_integer();
            let other = 1u8;

            value ^= other;
            assert_eq!(value.get_u128(), 16382);
        }

        #[test]
        fn div() {
            let value = 128u8.as_seven_bit_variable_length_integer();
            let other = 2u8;
            let result = value / other;
            assert_eq!(result.get_u128(), 64);

            let value = 16384u16.as_seven_bit_variable_length_integer();
            let other = 2u8;

            let result = value / other;
            assert_eq!(result.get_u128(), 8192);
        }

        #[test]
        fn div_assign() {
            let mut value = 128u8.as_seven_bit_variable_length_integer();
            let other = 2u8;
            value /= other;
            assert_eq!(value.get_u128(), 64);

            let mut value = 16384u16.as_seven_bit_variable_length_integer();
            let other = 2u8;

            value /= other;
            assert_eq!(value.get_u128(), 8192);
        }

        #[test]
        fn mul() {
            let value = 128u8.as_seven_bit_variable_length_integer();
            let other = 2u8;
            let result = value * other;
            assert_eq!(result.get_u128(), 256);

            let value = 16384u16.as_seven_bit_variable_length_integer();
            let other = 2u8;

            let result = value * other;
            assert_eq!(result.get_u128(), 32768);
        }

        #[test]
        fn mul_assign() {
            let mut value = 128u8.as_seven_bit_variable_length_integer();
            let other = 2u8;
            value *= other;
            assert_eq!(value.get_u128(), 256);

            let mut value = 16384u16.as_seven_bit_variable_length_integer();
            let other = 2u8;

            value *= other;
            assert_eq!(value.get_u128(), 32768);
        }

        #[test]
        fn sub() {
            let value = 128u8.as_seven_bit_variable_length_integer();
            let other = 1u8;
            let result = value - other;
            assert_eq!(result.get_u128(), 127);

            let value = 16384u16.as_seven_bit_variable_length_integer();
            let other = 1u8;

            let result = value - other;
            assert_eq!(result.get_u128(), 16383);
        }

        #[test]
        fn sub_assign() {
            let mut value = 128u8.as_seven_bit_variable_length_integer();
            let other = 1u8;
            value -= other;
            assert_eq!(value.get_u128(), 127);

            let mut value = 16384u16.as_seven_bit_variable_length_integer();
            let other = 1u8;

            value -= other;
            assert_eq!(value.get_u128(), 16383);
        }

        #[test]
        fn not() {
            let value = 128u8.as_seven_bit_variable_length_integer();
            let result = !value;
            assert_eq!(result.get_u128(), !128);

            let value = 16384u16.as_seven_bit_variable_length_integer();
            let result = !value;
            assert_eq!(result.get_u128(), !16384);
        }

        #[test]
        fn product() {
            let values = vec![128u8, 2u8, 4u8];

            let product = SevenBitVariableLengthInteger::product(values.into_iter());
            assert_eq!(product.get_u128(), 128 * 2 * 4);
        }

        #[test]
        fn rem() {
            let value = 128u8.as_seven_bit_variable_length_integer();
            let other = 2u8;
            let result = value % other;
            assert_eq!(result.get_u128(), 128 % 2);

            let value = 16384u16.as_seven_bit_variable_length_integer();
            let other = 2u8;

            let result = value % other;
            assert_eq!(result.get_u128(), 16384 % 2);
        }

        #[test]
        fn rem_assign() {
            let mut value = 128u8.as_seven_bit_variable_length_integer();
            let other = 2u8;
            value %= other;
            assert_eq!(value.get_u128(), 128 % 2);

            let mut value = 16384u16.as_seven_bit_variable_length_integer();
            let other = 2u8;

            value %= other;
            assert_eq!(value.get_u128(), 16384 % 2);
        }
    }

    mod tags {
        use super::*;

        #[test]
        fn set_higher_bits() {
            let pointer = 0x00000001 as *mut u8;

            // One bit
            let bits = -1isize as usize;
            let tagged = super::set_higher_bits(pointer, bits, 1usize);
            assert_eq!(
                tagged,
                0b1000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0001
                    as *mut u8
            );

            // Two bits
            let tagged = super::set_higher_bits(pointer, 0b1111111111, 2usize);
            assert_eq!(
                tagged,
                0b1100_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0001
                    as *mut u8
            );

            // Three bits
            let tagged = super::set_higher_bits(pointer, 0b0000_0000_0000_0101usize, 3usize);
            assert_eq!(
                tagged,
                0b1010_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0001
                    as *mut u8
            );

            let untagged_ptr = super::set_higher_bits(tagged, 0, 3usize);
            assert_eq!(untagged_ptr, pointer);
        }

        #[test]
        fn tag_raw_pointer_through_tag_impl() {
            let pointer = 0x00000001 as *mut u8;

            let parsed = AllocationPointerTag::from_pointer(pointer);
            assert_eq!(parsed, Some(AllocationPointerTag::Owned));

            let tagged_ptr = AllocationPointerTag::Borrowed.tag_pointer(pointer);
            assert_eq!(
                tagged_ptr,
                0b1000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0001
                    as *mut u8
            );

            let untagged_ptr = <*mut u8 as Taggable<AllocationPointerTag>>::remove_tag(&tagged_ptr);
            assert_eq!(untagged_ptr, pointer);
        }

        #[test]
        fn tag_raw_pointer_through_tag_interface() {
            let pointer = 0x00000001 as *mut u8;

            let parsed = pointer.get_tag();
            assert_eq!(parsed, Some(AllocationPointerTag::Owned));

            let tagged_ptr = pointer.tag(AllocationPointerTag::Borrowed);
            assert_eq!(
                tagged_ptr,
                0b1000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0001
                    as *mut u8
            );

            let untagged_ptr = <*mut u8 as Taggable<AllocationPointerTag>>::remove_tag(&tagged_ptr);
            assert_eq!(untagged_ptr, pointer);
        }

        #[test]
        fn tag_nonnull_pointer_through_impl() {
            let pointer = NonNull::new(0x00000001 as *mut u8).unwrap();

            let parsed = AllocationPointerTag::from_pointer(pointer.as_ptr());
            assert_eq!(parsed, Some(AllocationPointerTag::Owned));

            let tagged_ptr = pointer.tag(AllocationPointerTag::Borrowed);
            assert_eq!(
                tagged_ptr.as_ptr(),
                0b1000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0001
                    as *mut u8
            );

            let untagged_ptr =
                <std::ptr::NonNull<u8> as Taggable<AllocationPointerTag>>::remove_tag(&tagged_ptr);
            assert_eq!(untagged_ptr, pointer);
        }

        #[test]
        fn tag_nonnull_pointer_through_interface() {
            let pointer = NonNull::new(0x00000001 as *mut u8).unwrap();

            let parsed = pointer.get_tag();
            assert_eq!(parsed, Some(AllocationPointerTag::Owned));

            let tagged_ptr = pointer.tag(AllocationPointerTag::Borrowed);
            assert_eq!(
                tagged_ptr.as_ptr(),
                0b1000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0001
                    as *mut u8
            );

            let untagged_ptr =
                <std::ptr::NonNull<u8> as Taggable<AllocationPointerTag>>::remove_tag(&tagged_ptr);
            assert_eq!(untagged_ptr, pointer);
        }

        #[test]
        fn tag_nonnull_array_pointer() {
            let pointer = NonNull::new(0x00000001 as *mut [u8; 1]).unwrap();

            let parsed = AllocationPointerTag::from_pointer(pointer.as_ptr());
            assert_eq!(parsed, Some(AllocationPointerTag::Owned));

            let tagged_ptr = pointer.tag(AllocationPointerTag::Borrowed);
            assert_eq!(
                tagged_ptr.as_ptr().cast::<u8>(),
                0b1000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0001
                    as *mut u8
            );

            let untagged_ptr =
                <std::ptr::NonNull<[u8; 1]> as Taggable<AllocationPointerTag>>::remove_tag(
                    &tagged_ptr,
                );
            assert_eq!(untagged_ptr, pointer);
        }
    }

    #[cfg(target_arch = "x86_64")]
    #[test]
    fn get_actual_virtual_address_size() {
        assert_eq!(
            VirtualMemoryUnusedBitsCount::get_actual_unused_virtual_address_size()
                .unwrap()
                .get_count(),
            16,
        );

        assert_eq!(
            VirtualMemoryUnusedBitsCount::get_actual_virtual_address_size().unwrap(),
            48,
        );
    }
}
