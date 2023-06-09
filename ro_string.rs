//! Read-only strings, either const or stored in heap (and ref-counted)

use core::{fmt, ops::{Deref, Range}, hash::Hash, cmp::Ordering, str::from_utf8};
use alloc::{rc::Rc, sync::Arc};

/// [`Rc`]-backed [`RoString`]
pub mod rc {
    use super::Rc;

    /// [`Rc`]-backed [`RoString`]
    pub type RoString = super::RoString<Rc<[u8]>>;
}

/// [`Arc`]-backed [`RoString`]
pub mod arc {
    use super::Arc;

    /// [`Arc`]-backed [`RoString`]
    pub type RoString = super::RoString<Arc<[u8]>>;
}

/// A read-only string slice, stored either in a const data region or in the heap.
#[derive(Clone)]
pub enum RoString<T: FromIterator<u8> + AsRef<[u8]>> {
    String(T),
    Static(&'static str),
}

impl<T: FromIterator<u8> + AsRef<[u8]>> Deref for RoString<T> {
    type Target = str;

    fn deref(&self) -> &str {
        match self {
            Self::String(s) => from_utf8(s.as_ref()).unwrap(),
            Self::Static(s) => s,
        }
    }
}

impl<T: FromIterator<u8> + AsRef<[u8]>> fmt::Debug for RoString<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.deref())
    }
}

impl<T: FromIterator<u8> + AsRef<[u8]>> Hash for RoString<T> {
    fn hash<H: ::core::hash::Hasher>(&self, state: &mut H) {
        self.deref().hash(state);
    }
}

impl<T: FromIterator<u8> + AsRef<[u8]>> PartialEq for RoString<T> {
    fn eq(&self, other: &Self) -> bool {
        self.deref() == other.deref()
    }
}

impl<T: FromIterator<u8> + AsRef<[u8]>> Eq for RoString <T>{}

impl<T: FromIterator<u8> + AsRef<[u8]>> PartialOrd for RoString<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<T: FromIterator<u8> + AsRef<[u8]>> Ord for RoString<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.deref().cmp(&other.deref())
    }
}

impl<T: FromIterator<u8> + AsRef<[u8]>> RoString<T> {
    pub fn new(string: &str) -> Self {
        Self::from_iter(string.as_bytes().iter().map(|b| *b))
    }

    pub fn from_iter<I: IntoIterator<Item = u8>>(iter: I) -> Self {
        Self::String(T::from_iter(iter))
    }

    pub fn partial(self, range: Range<usize>) -> PartialRoString<T> {
        PartialRoString {
            string: self,
            range,
        }
    }
}

impl<T: FromIterator<u8> + AsRef<[u8]>> From<&'static str> for RoString<T> {
    fn from(string: &'static str) -> Self {
        RoString::Static(string)
    }
}

impl<T: FromIterator<u8> + AsRef<[u8]>> fmt::Display for RoString<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.deref())
    }
}

/// Get a [`RoString`] from a static string slice
pub const fn ro_string<T: FromIterator<u8> + AsRef<[u8]>>(s: &'static str) -> RoString<T> {
    RoString::Static(s)
}

/// Subslice of a [`RoString`]; create with [`RoString::partial`]
#[derive(Clone, Debug)]
pub struct PartialRoString<T: FromIterator<u8> + AsRef<[u8]>> {
    string: RoString<T>,
    range: Range<usize>,
}

impl<T: FromIterator<u8> + AsRef<[u8]>> Deref for PartialRoString<T> {
    type Target = str;

    fn deref(&self) -> &str {
        &self.string.deref()[self.range.clone()]
    }
}

impl<T: FromIterator<u8> + AsRef<[u8]>> fmt::Display for PartialRoString<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.deref())
    }
}

impl<T: FromIterator<u8> + AsRef<[u8]>> Hash for PartialRoString<T> {
    fn hash<H: ::core::hash::Hasher>(&self, state: &mut H) {
        self.deref().hash(state);
    }
}

impl<T: FromIterator<u8> + AsRef<[u8]>> PartialEq for PartialRoString<T> {
    fn eq(&self, other: &Self) -> bool {
        self.deref() == other.deref()
    }
}

impl<T: FromIterator<u8> + AsRef<[u8]>> Eq for PartialRoString<T> {}

impl<T: FromIterator<u8> + AsRef<[u8]>> PartialOrd for PartialRoString<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<T: FromIterator<u8> + AsRef<[u8]>> Ord for PartialRoString<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.deref().cmp(&other.deref())
    }
}
