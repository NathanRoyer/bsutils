//! Vec<Box<str>> equivalent (thin pointer)

use core::{
    fmt, str::from_utf8, ptr, mem::{size_of, align_of},
    slice::{from_raw_parts, from_raw_parts_mut}
};
use alloc::{alloc::{Layout, alloc as alloc_fn, realloc, dealloc}};

const SIZE_OF_USIZE: usize = size_of::<usize>();

/// Vec<Box<str>> equivalent
///
/// Internally, this is a thin pointer to a structure which
/// looks like this: `{ count: usize, [len: usize], [byte: u8] }`
#[derive(Clone, PartialEq, Eq)]
#[repr(transparent)]
pub struct StringList(*mut usize);

fn layout(bytes: usize) -> Layout {
    Layout::from_size_align(bytes, align_of::<usize>()).unwrap()
}

impl StringList {
    /// Create an empty list (doesn't allocate)
    pub const fn new() -> Self {
        Self(ptr::null_mut())
    }

    /// Get the number of strings
    pub fn len(&self) -> usize {
        match self.0.is_null() {
            true => 0,
            false => unsafe { self.0.read() },
        }
    }

    #[inline(always)]
    fn lengths(&self) -> &[usize] {
        match self.0.is_null() {
            true => &[],
            false => unsafe { from_raw_parts(self.0.add(1), self.0.read()) },
        }
    }

    #[inline(always)]
    fn range(&self, index: usize) -> (usize, usize) {
        let lengths = self.lengths();
        (lengths[..index].iter().fold(0, |acc, len| acc + len), lengths[index])
    }

    #[inline(always)]
    fn bytes_count(&self) -> usize {
        if let Some(index) = self.len().checked_sub(1) {
            let (l_offset, l_len) = self.range(index);
            l_offset + l_len
        } else {
            0
        }
    }

    /// Get a specific string
    pub fn get(&self, index: usize) -> Option<&str> {
        let count = self.len();
        if index < count {
            let (offset, len) = self.range(index);
            let bytes = unsafe { self.0.add(1 + count) as *mut u8 };
            let slice = unsafe { from_raw_parts(bytes.add(offset), len) };

            Some(from_utf8(slice).unwrap())
        } else {
            None
        }
    }

    /// Add a string to the list
    pub fn push(&mut self, key: &str) {
        let key_len = key.len();
        let old_count = self.len();
        let new_count = old_count + 1;
        let old_bytes = self.bytes_count();

        if self.0.is_null() {
            let bytes = SIZE_OF_USIZE + SIZE_OF_USIZE + key_len;
            self.0 = unsafe { alloc_fn(layout(bytes)) as _ };
        } else {
            let old_size = SIZE_OF_USIZE + (SIZE_OF_USIZE * old_count) + old_bytes;
            let new_size = SIZE_OF_USIZE + (SIZE_OF_USIZE * new_count) + old_bytes + key_len;
            self.0 = unsafe { realloc(self.0 as _, layout(old_size), new_size) as _ };
        }

        let end_of_old_lengths = unsafe { self.0.add(1 + old_count) };
        let slice = unsafe { from_raw_parts_mut(end_of_old_lengths as *mut u8, SIZE_OF_USIZE + old_bytes + key_len) };
        let key_spot = SIZE_OF_USIZE + old_bytes;

        slice.copy_within(0..old_bytes, SIZE_OF_USIZE);
        slice[key_spot..].copy_from_slice(key.as_bytes());
        unsafe { end_of_old_lengths.write(key_len) };

        unsafe { self.0.write(new_count) };
    }

    /// Iterate on the strings
    pub fn iter(&self) -> impl Iterator<Item = &str> {
        (0..self.len()).map(|i| self.get(i).unwrap())
    }
}

impl Drop for StringList {
    #[inline]
    fn drop(&mut self) {
        let count = self.len();
        if count > 0 {
            let bytes = SIZE_OF_USIZE + (SIZE_OF_USIZE * count) + self.bytes_count();
            unsafe { dealloc(self.0 as _, layout(bytes)) };
        }
    }
}

impl fmt::Debug for StringList {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}