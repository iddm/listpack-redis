//! The default allocator of the listpack.

use redis_custom_allocator::CustomAllocator;

/// The default [`crate::listpack::Listpack`] allocator.
#[derive(Default, Debug, Copy, Clone)]
pub struct DefaultAllocator;

impl CustomAllocator for DefaultAllocator {
    type Error = String;

    fn allocate(&self, layout: std::alloc::Layout) -> Result<std::ptr::NonNull<[u8]>, Self::Error> {
        let ptr = unsafe { std::alloc::alloc(layout) };
        if ptr.is_null() {
            Err("Failed to allocate memory".to_string())
        } else {
            Ok(unsafe {
                std::ptr::NonNull::new_unchecked(std::slice::from_raw_parts_mut(ptr, layout.size()))
            })
        }
    }

    unsafe fn deallocate(&self, ptr: std::ptr::NonNull<u8>, layout: std::alloc::Layout) {
        std::alloc::dealloc(ptr.as_ptr(), layout)
    }

    fn allocate_zeroed(
        &self,
        layout: std::alloc::Layout,
    ) -> Result<std::ptr::NonNull<[u8]>, Self::Error> {
        let ptr = unsafe { std::alloc::alloc_zeroed(layout) };
        if ptr.is_null() {
            Err("Failed to allocate memory".to_string())
        } else {
            Ok(unsafe {
                std::ptr::NonNull::new_unchecked(std::slice::from_raw_parts_mut(ptr, layout.size()))
            })
        }
    }
}
