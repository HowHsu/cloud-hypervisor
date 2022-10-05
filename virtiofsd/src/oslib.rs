use std::ffi::CString;
use std::io::{Error, Result};
use std::os::unix::io::RawFd;

// A helper function that check the return value of a C function call
// and wraps it in a `Result` type, returning the `errno` code as `Err`.
fn check_retval<T: From<i32> + PartialEq>(t: T) -> Result<T> {
    if t == T::from(-1_i32) {
        Err(Error::last_os_error())
    } else {
        Ok(t)
    }
}

/// Safe wrapper for `mount(2)`
///
/// # Errors
///
/// Will return `Err(errno)` if `mount(2)` fails.
/// Each filesystem type may have its own special errors and its own special behavior,
/// see `mount(2)` and the linux source kernel for details.
///
/// # Panics
///
/// This function panics if the strings `source`, `target` or `fstype` contain an internal 0 byte.
pub fn mount(source: Option<&str>, target: &str, fstype: Option<&str>, flags: u64) -> Result<()> {
    let source = CString::new(source.unwrap_or("")).unwrap();
    let source = source.as_ptr();

    let target = CString::new(target).unwrap();
    let target = target.as_ptr();

    let fstype = CString::new(fstype.unwrap_or("")).unwrap();
    let fstype = fstype.as_ptr();

    // Safety: `source`, `target` or `fstype` are a valid C string pointers
    check_retval(unsafe { libc::mount(source, target, fstype, flags, std::ptr::null()) })?;
    Ok(())
}

/// Safe wrapper for `umount2(2)`
///
/// # Errors
///
/// Will return `Err(errno)` if `umount2(2)` fails.
/// Each filesystem type may have its own special errors and its own special behavior,
/// see `umount2(2)` and the linux source kernel for details.
///
/// # Panics
///
/// This function panics if the strings `target` contains an internal 0 byte.
pub fn umount2(target: &str, flags: i32) -> Result<()> {
    let target = CString::new(target).unwrap();
    let target = target.as_ptr();

    // Safety: `target` is a valid C string pointer
    check_retval(unsafe { libc::umount2(target, flags) })?;
    Ok(())
}

/// Safe wrapper for `fchdir(2)`
///
/// # Errors
///
/// Will return `Err(errno)` if `fchdir(2)` fails.
/// Each filesystem type may have its own special errors, see `fchdir(2)` for details.
pub fn fchdir(fd: RawFd) -> Result<()> {
    check_retval(unsafe { libc::fchdir(fd) })?;
    Ok(())
}
