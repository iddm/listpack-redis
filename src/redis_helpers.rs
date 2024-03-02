//! These are the Redis helper functions, which are required for the
//! listpack C library to work. The functions are implemented in Rust
//! and are used by the listpack C library.

use std::ffi::CStr;

// void _serverAssert(const char *estr, const char *file, int line);
#[no_mangle]
pub extern "C" fn _serverAssert(
    estr: *const std::ffi::c_char,
    file: *const std::ffi::c_char,
    line: std::ffi::c_int,
) {
    let estr = unsafe { CStr::from_ptr(estr) };
    let file = unsafe { CStr::from_ptr(file) };
    panic!(
        "assertion failed: {} in file {} at line {}",
        estr.to_str().unwrap(),
        file.to_str().unwrap(),
        line
    );
}

// void _serverPanic(const char *file, int line, const char *msg, ...);
#[no_mangle]
pub extern "C" fn _serverPanic(
    file: *const std::ffi::c_char,
    line: std::ffi::c_int,
    msg: *const std::ffi::c_char,
) {
    let file = unsafe { CStr::from_ptr(file) };
    let msg = unsafe { CStr::from_ptr(msg) };
    server_panic_fmt(file.to_str().unwrap(), line as u32, msg.to_str().unwrap());
}

fn server_panic_fmt(file: &str, line: u32, msg: &str) {
    panic!("panic in file {} at line {}: {}", file, line, msg);
}

// #[no_mangle]
// pub extern "C" fn zmalloc(size: usize) -> *mut std::ffi::c_void {
//     let ptr = unsafe { libc::malloc(size) };
//     if ptr.is_null() {
//         server_panic_fmt(file!(), line!(), "zmalloc: Out of memory");
//     }
//     ptr
// }

// #[no_mangle]
// pub extern "C" fn zfree(ptr: *mut std::ffi::c_void) {
//     unsafe { libc::free(ptr) };
// }

// #[no_mangle]
// pub extern "C" fn zrealloc(ptr: *mut std::ffi::c_void, size: usize) -> *mut std::ffi::c_void {
//     let ptr = unsafe { libc::realloc(ptr, size) };
//     if ptr.is_null() {
//         server_panic_fmt(file!(), line!(), "zrealloc: Out of memory");
//     }
//     ptr
// }

// #[no_mangle]
// pub extern "C" fn zcalloc(size: usize) -> *mut std::ffi::c_void {
//     let ptr = unsafe { libc::calloc(1, size) };
//     if ptr.is_null() {
//         server_panic_fmt(file!(), line!(), "zcalloc: Out of memory");
//     }
//     ptr
// }
