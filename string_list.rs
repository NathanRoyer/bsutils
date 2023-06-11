use core::{iter::from_fn, fmt, str::from_utf8, ptr, mem::{size_of, align_of}};
use alloc::{alloc::{Layout, alloc as alloc_fn, realloc, dealloc}};

/// All Keys stored in one allocation.
#[derive(Clone, PartialEq, Eq)]
#[repr(transparent)]
pub struct StringList(*mut usize);

fn layout(slice_len: usize) -> Layout {
    Layout::from_size_align(size_of::<usize>() + slice_len, align_of::<usize>()).unwrap()
}

impl StringList {
    pub fn new() -> Self {
        Self(ptr::null_mut())
    }

    pub fn iter(&self) -> impl Iterator<Item = &str> {
        unsafe {
            let mut i = 0;
            from_fn(move || {
                if self.0.is_null() {
                    None
                } else {
                    let slice_len = self.0.read();
                    let slice = self.0.offset(1) as *mut u8;
                    let slice = core::slice::from_raw_parts(slice, slice_len);
                    if i < slice_len {
                        let start = i;
                        while slice[i] != 0 {
                            i += 1;
                        }

                        let key = &slice[start..i];
                        i += 1;

                        Some(from_utf8(key).unwrap())
                    } else {
                        None
                    }
                }
            })
        }
    }

    pub fn push(&mut self, key: &str) {
        let key_len = key.len() + 1;
        let dst = unsafe {
            let (old_len, new_len) = if self.0.is_null() {
                self.0 = alloc_fn(layout(key_len)) as _;
                (0, key_len)
            } else {
                let old_len = self.0.read();
                let new_len = old_len + key_len;
                let new_size = size_of::<usize>() + new_len;
                self.0 = realloc(self.0 as _, layout(old_len), new_size) as _;
                (old_len, new_len)
            };

            self.0.write(new_len);

            let slice = self.0.offset(1) as *mut u8;
            let slice = core::slice::from_raw_parts_mut(slice, new_len);
            let zero_i = new_len - 1;
            slice[zero_i] = 0;

            &mut slice[old_len..zero_i]
        };
        dst.copy_from_slice(key.as_bytes())
    }
}

impl Drop for StringList {
    #[inline]
    fn drop(&mut self) {
        unsafe {
            if !self.0.is_null() {
                let slice_len = self.0.read();
                dealloc(self.0 as _, layout(slice_len));
            }
        }
    }
}

impl fmt::Debug for StringList {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}