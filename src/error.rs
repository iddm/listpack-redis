//! The error module contains the error type and result type for the

use std::str::Utf8Error;

/// An error happening during the insertion into listpack.
#[derive(Debug, Copy, Clone)]
pub enum InsertionError {
    /// An empty string is provided to be inserted into the listpack.
    StringIsEmpty,
    /// The object which is too long to be inserted into the listpack.
    ListpackIsFull {
        /// The current byte length of the object causing the error
        /// during the insertion.
        current_length: usize,
        /// The available amount of bytes available in the listpack.
        available_listpack_length: usize,
    },
    /// An insertion error indicating that the index is out of bounds.
    IndexOutOfBounds {
        /// The index that caused the error.
        index: usize,
        /// The length of the listpack.
        length: usize,
    },
}

/// An error happening during the deletion from listpack.
#[derive(Debug, Copy, Clone)]
pub enum DeletionError {
    /// An error indicating that the index is out of bounds.
    IndexOutOfBounds {
        /// The start index that caused the error.
        start_index: usize,
        /// The number of elements to delete.
        delete_count: usize,
        /// The length of the listpack.
        length: usize,
    },
}

impl std::fmt::Display for DeletionError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::IndexOutOfBounds {
                start_index,
                delete_count,
                length,
            } => {
                write!(
                    f,
                    "Index out of bounds: {start_index} + {delete_count} > {length}"
                )
            }
        }
    }
}

impl std::error::Error for DeletionError {}

impl std::fmt::Display for InsertionError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::StringIsEmpty => write!(f, "Provided string is empty."),
            Self::ListpackIsFull {
                current_length,
                available_listpack_length,
            } => write!(
                f,
                "Object is too long: {current_length} > {available_listpack_length}"
            ),
            Self::IndexOutOfBounds { index, length } => {
                write!(f, "Index out of bounds: {index} > {length}")
            }
        }
    }
}

impl std::error::Error for InsertionError {}

/// An error happening during the allocation of a listpack or its values.
#[derive(Debug, Copy, Clone)]
pub enum AllocationError {
    /// An attempt to allocate a listpack with a size bigger than the
    /// header can hold (all in bytes).
    ListpackIsTooBig {
        /// The size of the listpack that caused the error.
        size: usize,
        /// The maximum size of the listpack.
        max_size: usize,
    },
    /// An error indicating that the listpack failed to grow in size.
    FailedToGrow {
        /// The size to which the listpack had to grow.
        size: usize,
    },
    /// An error indicating that the listpack failed to shrink in size.
    FailedToShrink {
        /// The size to which the listpack had to shrink.
        size: usize,
    },
}

impl std::fmt::Display for AllocationError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::ListpackIsTooBig { size, max_size } => {
                write!(f, "Listpack is too big: {size} > {max_size}")
            }
            Self::FailedToShrink { size } => {
                write!(f, "Failed to shrink to size: {size}")
            }
            Self::FailedToGrow { size } => write!(f, "Failed to grow to size: {size}"),
        }
    }
}

impl std::error::Error for AllocationError {}

/// An error happening during the conversion of the listpack elements
/// (entries) to another type.
#[derive(Debug, Copy, Clone)]
pub enum TypeConversionError {
    /// An error indicating that the types are not compatible.
    WrongTypes {
        /// The name of the type that was attempted to convert to.
        target_type: &'static str,
        /// The type that was in the listpack.
        encoding_type: crate::ListpackEntryEncodingType,
    },
}

impl TypeConversionError {
    /// Creates a new type conversion error with the provided types.
    pub fn wrong_types<ToType>(encoding_type: crate::ListpackEntryEncodingType) -> Self {
        Self::WrongTypes {
            target_type: std::any::type_name::<ToType>(),
            encoding_type,
        }
    }
}

impl std::fmt::Display for TypeConversionError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::WrongTypes {
                target_type,
                encoding_type,
            } => {
                write!(
                    f,
                    "Wrong types: couldn't convert {encoding_type:?} to {target_type}."
                )
            }
        }
    }
}

impl std::error::Error for TypeConversionError {}

/// The error type for the listpack crate.
#[derive(Debug, Copy, Clone)]
pub enum Error {
    /// The subencoding of the listpack's entry is unknown.
    UnknownEncodingType {
        /// The encoding byte that caused the error.
        encoding_byte: u8,
    },
    /// Indicates an unsupported number data type. The bit width of the
    /// provided number which caused this error is provided in the
    /// [`Self::UnsupportedNumberDataTypeBitWidth::bit_width`] field.
    UnsupportedNumberDataTypeBitWidth {
        /// The bit width of the number that caused the error.
        bit_width: u8,
    },
    /// An error indicating that the object is too big to be encoded.
    ObjectIsTooBigForEncoding {
        /// The size of the object that caused the error.
        size: usize,
        /// The maximum size of the object that can be encoded.
        max_size: usize,
    },
    /// An error indicating that the listpack's entry is missing a data
    /// block.
    MissingDataBlock,
    /// An error indicating that the listpack's entry contains an
    /// invalid string inside the data block.
    InvalidStringEncodingInsideDataBlock(Utf8Error),
    /// When the end marker is missing from the listpack.
    MissingEndMarker,
    /// When the end marker is met earlier than expected.
    UnexpectedEndMarker,
    /// An error related to the allocation of memory.
    Allocation(AllocationError),
    /// An error related to the insertion into the listpack.
    Insertion(InsertionError),
    /// An error related to the deletion from the listpack.
    Deletion(DeletionError),
    /// An error related to the type conversion.
    TypeConversion(TypeConversionError),
}

impl From<AllocationError> for Error {
    fn from(e: AllocationError) -> Self {
        Error::Allocation(e)
    }
}

impl From<InsertionError> for Error {
    fn from(e: InsertionError) -> Self {
        Error::Insertion(e)
    }
}

impl From<DeletionError> for Error {
    fn from(e: DeletionError) -> Self {
        Error::Deletion(e)
    }
}

impl From<TypeConversionError> for Error {
    fn from(e: TypeConversionError) -> Self {
        Error::TypeConversion(e)
    }
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::UnknownEncodingType { encoding_byte } => {
                write!(f, "Unknown encoding byte: {encoding_byte:b}")
            }
            Self::UnsupportedNumberDataTypeBitWidth { bit_width } => {
                write!(f, "Unsupported number data type bit width: {bit_width}")
            }
            Self::ObjectIsTooBigForEncoding { size, max_size } => {
                write!(f, "Object is too big for encoding: {size} > {max_size}")
            }
            Self::MissingDataBlock => write!(f, "Missing data block"),
            Self::InvalidStringEncodingInsideDataBlock(e) => {
                write!(f, "Invalid string inside data block: {e}")
            }
            Self::UnexpectedEndMarker => write!(f, "Unexpected end marker"),
            Self::MissingEndMarker => write!(f, "Missing end marker"),
            Self::Allocation(e) => write!(f, "Allocation error: {e}"),
            Self::Insertion(e) => write!(f, "Insertion error: {e}"),
            Self::Deletion(e) => write!(f, "Deletion error: {e}"),
            Self::TypeConversion(e) => write!(f, "Type conversion error: {e}"),
        }
    }
}

impl std::error::Error for Error {}

/// The result type for the listpack crate.
pub type Result<T = (), E = Error> = std::result::Result<T, E>;
