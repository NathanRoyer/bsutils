//! Compact & garbage-collected JSON Storage, with (de)serialization

use core::{
    hash::{Hash, Hasher, BuildHasher}, ops::Index,
    slice::SliceIndex, fmt, str::from_utf8,
};

use alloc::boxed::Box;
use super::{ArcStr, LiteMap, ThinVec};
use ahash::AHasher;
use strpool::{Pool, PoolStr};

pub type ParsingError = &'static str;

/// One step in a JSON state path
#[derive(Debug, Clone, Hash)]
pub enum PathStep<'a> {
    Key(&'a str),
    Index(usize),
}

impl<'a> From<&'a str> for PathStep<'a> {
    fn from(string: &'a str) -> PathStep<'a> {
        Self::Key(string)
    }
}

impl<'a> From<usize> for PathStep<'a> {
    fn from(index: usize) -> PathStep<'a> {
        Self::Index(index)
    }
}

pub type ArrayLength = usize;

/// Standalone JSON Value (16 bytes)
#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Array(ArrayLength),
    Object(ThinVec<PoolStr>),
    String(ArcStr),
    Number(f64),
    Boolean(bool),
    Null,
}

// Assert that the size of Value is 16 bytes
#[cfg(target_pointer_width = "64")]
const _: usize = [0][(!(core::mem::size_of::<Value>() == 16)) as usize];

/// The Path to a JSON Value, in a [`JsonFile`]
#[derive(Debug, Clone)]
pub struct Path(AHasher);

impl Path {
    pub fn new() -> Self {
        Self(super::GEN.build_hasher())
    }

    pub fn index_str(&mut self, key: &str) -> &mut Self {
        PathStep::Key(&key).hash(&mut self.0);
        self
    }

    pub fn index_num(&mut self, index: usize) -> &mut Self {
        PathStep::Index(index).hash(&mut self.0);
        self
    }

    /// Appends sequential indexes from an iterator
    pub fn append<'a, I: Into<PathStep<'a>>, T: IntoIterator<Item = I>>(
        &mut self,
        steps: T,
    ) -> &mut Self {
        for step in steps.into_iter() {
            step.into().hash(&mut self.0);
        }

        self
    }
}

/// Parse a string as a list of path steps
pub fn parse_path<'a>(path: &'a str) -> impl Iterator<Item = PathStep<'a>> {
    path.split('.').filter(|k| !k.is_empty()).map(|key| match key.parse::<usize>() {
        Ok(index) => index.into(),
        Err(_) => key.into(),
    })
}

impl<'a, I: Into<PathStep<'a>>, T: IntoIterator<Item = I>> From<T> for Path {
    fn from(steps: T) -> Self {
        Self::new().append(steps).clone()
    }
}

/// A JSON File, stored in a "self-recursive" Map<u64, Value>
///
/// Note: If values are changed at some point, make sure that
/// [`Self::remove_null`] is called after the changes have been
/// done: when a nested structure is removed, all contained
/// values are changed to Null; calling [`Self::remove_null`] is
/// actually equivalent to a garbage collection process, in this
/// context.
///
/// Note: Object keys are stored in a [`Pool`], which makes this
/// well suited for parsing large arrays of objects with similar
/// layouts.
pub struct JsonFile {
    map: LiteMap<u64, Value>,
    keys: Pool,
}

impl JsonFile {
    /// Creates a new JSON file (optionally from a JSON string)
    pub fn new(json: Option<&str>) -> Result<Self, ParsingError> {
        Self::with_key_pool(json, Pool::new())
    }

    /// Creates a new JSON file using an existing key string pool (optionally from a JSON string)
    pub fn with_key_pool(json: Option<&str>, keys: Pool) -> Result<Self, ParsingError> {
        let this = Self {
            map: LiteMap::new(),
            keys,
        };

        match json {
            Some(json) => this.parse(json),
            None => Ok(this),
        }
    }

    fn parse(mut self, json: &str) -> Result<Self, ParsingError> {
        let rem = parse_value(Str(json.as_bytes()), &mut self, &Path::new())?;
        match skip_ws(rem) {
            Err(_) => Ok(self),
            Ok(_) => Err("unexpected token (5)"),
        }
    }

    pub fn get(&self, path: &Path) -> &Value {
        self.map.get(&path.0.finish()).unwrap_or(&Value::Null)
    }

    /// Efficiently removes all Null values from the file.
    ///
    /// Note: if a Null value was inserted in an array or
    /// an object, the key/index will persist, but the actual
    /// value will be removed.
    pub fn remove_null(&mut self) {
        self.map.retain(|_k, v| !matches!(v, Value::Null))
    }

    /// Removes a value and all its eventual content.
    pub fn remove(&mut self, path: &Path) {
        self.insert_gc(path, Value::Null);
    }

    fn insert_gc(&mut self, path: &Path, value: Value) {
        let old_value = self.map.insert(path.0.finish(), value);
        match old_value {
            Some(Value::Array(num)) => {
                for i in 0..num {
                    let mut path = path.clone();
                    path.index_num(i);
                    self.insert_gc(&path, Value::Null);
                }
            },
            Some(Value::Object(keys)) => {
                for key in keys.iter() {
                    let mut path = path.clone();
                    path.index_str(key);
                    self.insert_gc(&path, Value::Null);
                }
            },
            _ => (),
        }
    }

    /// Create an array in the JSON file
    pub fn set_array(&mut self, path: &Path) {
        self.insert_gc(path, Value::Array(0));
    }

    /// Create an object in the JSON file
    pub fn set_object(&mut self, path: &Path) {
        self.insert_gc(path, Value::Object(ThinVec::new()));
    }

    /// Insert a number in the JSON file
    pub fn set_number(&mut self, path: &Path, value: f64) {
        self.insert_gc(path, Value::Number(value));
    }

    /// Insert a string in the JSON file
    pub fn set_string(&mut self, path: &Path, value: ArcStr) {
        self.insert_gc(path, Value::String(value));
    }

    /// Insert a boolean in the JSON file
    pub fn set_boolean(&mut self, path: &Path, value: bool) {
        self.insert_gc(path, Value::Boolean(value));
    }

    /// Add an item to an array from the JSON file
    ///
    /// The returned [`Path`] leads to the new item.
    ///
    /// Caution: this panics if the specified path leads to
    /// a value which isn't a [`Value::Array`]
    pub fn push(&mut self, path: &Path) -> Path {
        let val = self.map.get_mut(&path.0.finish());
        let mut path = path.clone();

        if let Some(Value::Array(num)) = val {
            path.index_num(*num);
            *num += 1;
        } else {
            panic!("Value at `path` is not an array");
        }

        path
    }

    /// Iterates on the items in an array
    ///
    /// Yields zero item if the value at `base_path`
    /// is not an array.
    pub fn iter_array(&self, base_path: &Path) -> ArrayIter {
        let value = self.map.get(&base_path.0.finish());
        let base_path = base_path.clone();
        if let Some(Value::Array(len)) = value {
            ArrayIter {
                state: self,
                base_path,
                next: 0,
                len: *len,
            }
        } else {
            ArrayIter {
                state: self,
                base_path,
                next: 0,
                len: 0,
            }
        }
    }

    /// Add a property to an object from the JSON file
    ///
    /// The returned [`Path`] leads to the new property.
    /// Has no effect no the file if the property already exists.
    ///
    /// Caution: this panics if the specified path leads to
    /// a value which isn't a [`Value::Object`]
    pub fn prop(&mut self, path: &Path, key: &str) -> Path {
        let val = self.map.get_mut(&path.0.finish());
        let mut path = path.clone();

        if let Some(Value::Object(keys)) = val {
            path.index_str(key);
            let interned = self.keys.intern(key);
            if !keys.contains(&interned) {
                keys.push(interned);
            }
        } else {
            panic!("Value at `path` is not an object");
        }

        path
    }

    /// Writes some part of this JSON file to a [`fmt::Write`] implementor
    pub fn dump_to<T: fmt::Write>(&self, f: &mut T, path: &Path) -> fmt::Result {
        match self.get(path) {
            Value::Array(num) => {
                write!(f, "[ ")?;
                for i in 0..*num {
                    let mut path = path.clone();
                    path.index_num(i);

                    if self.get(&path) != &Value::Null {
                        self.dump_to(f, &path)?;

                        if (i + 1) != *num {
                            write!(f, ", ")?;
                        }
                    }
                }
                write!(f, " ]")
            },
            Value::Object(keys) => {
                write!(f, "{{ ")?;
                let mut iter = keys.iter();
                let mut value = iter.next();
                while let Some(key) = value {
                    let mut path = path.clone();
                    path.index_str(key);
                    let is_null = self.get(&path) == &Value::Null;

                    if !is_null {
                        write!(f, "{:?}: ", key)?;
                        self.dump_to(f, &path)?;
                    }

                    value = iter.next();
                    if value.is_some() && !is_null {
                        write!(f, ", ")?;
                    }
                }
                write!(f, " }}")
            },
            Value::String(string) => write!(f, "{:?}", string),
            Value::Number(num) => write!(f, "{}", num),
            Value::Boolean(b) => write!(f, "{:?}", b),
            Value::Null => write!(f, "null"),
        }
    }

    /// Writes some part of this JSON file to a [`ArcStr`]
    pub fn dump(&self, path: &Path) -> Result<ArcStr, fmt::Error> {
        let mut string = alloc::string::String::new();
        self.dump_to(&mut string, path)?;
        Ok(string.into())
    }
}

/// Dumps the whole JSON File
impl fmt::Display for JsonFile {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.dump_to(f, &Path::new())
    }
}

impl Index<&Path> for JsonFile {
    type Output = Value;
    fn index(&self, path: &Path) -> &Self::Output {
        self.get(path)
    }
}

impl Index<&mut Path> for JsonFile {
    type Output = Value;
    fn index(&self, path: &mut Path) -> &Self::Output {
        self.get(path)
    }
}

impl Index<Path> for JsonFile {
    type Output = Value;
    fn index(&self, path: Path) -> &Self::Output {
        self.get(&path)
    }
}

impl<'a, I: Into<PathStep<'a>>, T: IntoIterator<Item = I>> Index<T> for JsonFile {
    type Output = Value;
    fn index(&self, iter: T) -> &Self::Output {
        self.get(&iter.into())
    }
}

// PARSING

struct Str<'a>(&'a [u8]);

impl<'a> Str<'a> {
    fn get<I: SliceIndex<[u8]>>(&self, i: I) -> Result<&'a I::Output, ParsingError> {
        match self.0.get(i) {
            Some(v) => Ok(v),
            None => Err("json input looks truncated"),
        }
    }
}

fn skip_ws<'a>(json: Str<'a>) -> Result<Str<'a>, ParsingError> {
    match json.get(0)? {
        b'\t' |
        b'\n' |
        b'\r' |
        b' ' => skip_ws(Str(&json.get(1..)?)),
        _ => Ok(json),
    }
}

fn parse_string_for_real<'a>(mut string: Str<'a>, char_count: usize) -> Result<ArcStr, ParsingError> {
    let mut pending: Option<(usize, usize, [u8; 4])> = None;

    // todo: impl TryFrom<Box<[u8]>> for ArcStr
    let bytes = Box::from_iter((0..char_count).map(|_| {
        if let Some((i, num, bytes)) = &mut pending {
            let byte = bytes[*i];
            *i += 1;

            if *i == *num {
                pending = None;
            }

            byte
        } else {
            let (byte, skip) = match string.0[0] {
                b'\"' => unreachable!(),
                b'\\' => match string.0[1] {
                    b'\"' => (b'\"', 2),
                    b'\\' => (b'\\', 2),
                    b'/' => (b'/', 2),
                    b'b' => (b'\x08', 2),
                    b'f' => (b'\x0c', 2),
                    b'n' => (b'\n', 2),
                    b'r' => (b'\r', 2),
                    b't' => (b'\t', 2),
                    b'u' => {
                        type U = usize;
                        let (a, b, c, d) = (string.0[2], string.0[3], string.0[4], string.0[5]);
                        let (a, b, c, d) = (HEX[a as U], HEX[b as U], HEX[c as U], HEX[d as U]);

                        let cp = ((a as u32) << 12) | ((b as u32) << 8) | ((c as u32) << 4) | ((d as u32) << 0);
                        let character = char::from_u32(cp).unwrap();
                        let num = character.len_utf8();
                        let mut buf = [0; 4];
                        character.encode_utf8(&mut buf);

                        if num > 1 {
                            pending = Some((1, num, buf));
                        }

                        (buf[0], 6)
                    },
                    _ => unreachable!(),
                },
                byte => (byte, 1),
            };

            string = Str(&string.0[skip..]);

            byte
        }
    }));

    match from_utf8(&bytes) {
        Ok(string) => Ok(string.into()),
        Err(_) => Err("invalid UTF-8 sequence"),
    }
}

fn parse_string<'a>(backup: Str<'a>) -> Result<(ArcStr, Str<'a>), ParsingError> {
    let mut string = Str(backup.0);
    let mut char_count = 0;

    let ro_heap_string = loop {
        let (add, skip) = match string.get(0)? {
            b'\"' => break parse_string_for_real(Str(backup.0), char_count)?,
            b'\\' => match string.get(1)? {
                b'\"' | b'\\' | b'/' | b'b' |
                b'f' | b'n' | b'r' | b't' => (1, 2),
                b'u' => {
                    type U = usize;
                    string.get(2..6)?;
                    let (a, b, c, d) = (string.0[2], string.0[3], string.0[4], string.0[5]);
                    let (a, b, c, d) = (HEX[a as U], HEX[b as U], HEX[c as U], HEX[d as U]);

                    if [a, b, c, d].iter().find(|v| **v > 15).is_some() {
                        return Err("invalid hex digit in escaped codepoint");
                    }

                    let cp = ((a as u32) << 12) | ((b as u32) << 8) | ((c as u32) << 4) | ((d as u32) << 0);
                    match char::from_u32(cp) {
                        Some(c) => (c.len_utf8(), 6),
                        None => return Err("invalid codepoint"),
                    }
                },
                _ => return Err("invalid escape character"),
            },
            _ => (1, 1),
        };

        char_count += add;
        let next = string.get(skip..)?;
        string = Str(next);
    };

    let offset = backup.0.len() - (string.0.len() - 1);
    return Ok((ro_heap_string, Str(backup.get(offset..)?)));
}

fn parse_number<'a>(value: Str<'a>) -> Result<(f64, Str<'a>), ParsingError> {
    let mut len = 0;
    for character in value.0 {
        match character {
            b',' |
            b']' |
            b'}' |
            b' ' |
            b'\t' |
            b'\n' |
            b'\r' => break,
            _ => len += 1,
        }
    }

    let (number, next) = value.0.split_at(len);
    match from_utf8(number) {
        Ok(string) => match string.parse() {
            Ok(float) => Ok((float, Str(next))),
            Err(_) => Err("invalid number"),
        },
        Err(_) => Err("invalid number"),
    }
}

fn parse_value<'a>(value: Str<'a>, file: &mut JsonFile, path: &Path) -> Result<Str<'a>, ParsingError> {
    let value = skip_ws(value)?;
    match value.get(0)? {
        b'{' => {
            file.set_object(path);
            let mut object_body = skip_ws(Str(value.get(1..)?))?;
            let mut first = true;

            loop {
                object_body = match (object_body.get(0)?, first) {
                    (b'}', true) => return Ok(Str(object_body.get(1..)?)),
                    (b'}', false) => return Err("missing value"),
                    (b'\"', _) => skip_ws(Str(object_body.get(1..)?))?,
                    _ => return Err("unexpected token (1)"),
                };

                let (key, next) = parse_string(object_body)?;
                object_body = skip_ws(next)?;

                if *object_body.get(0)? != b':' {
                    return Err("missing colon after object key");
                }

                object_body = skip_ws(Str(object_body.get(1..)?))?;

                let path = file.prop(path, &key);
                let next = parse_value(object_body, file, &path)?;
                object_body = skip_ws(next)?;

                first = false;
                object_body = match *object_body.get(0)? {
                    b'}' => return Ok(Str(object_body.get(1..)?)),
                    b',' => skip_ws(Str(object_body.get(1..)?))?,
                    _ => return Err("unexpected token (2)"),
                };
            }
        },
        b'[' => {
            file.set_array(path);
            let mut array_body = skip_ws(Str(value.get(1..)?))?;

            if *array_body.get(0)? == b']' {
                return Ok(Str(array_body.get(1..)?));
            }

            loop {
                let path = file.push(path);
                let next = parse_value(array_body, file, &path)?;
                array_body = skip_ws(next)?;

                array_body = match *array_body.get(0)? {
                    b']' => return Ok(Str(array_body.get(1..)?)),
                    b',' => skip_ws(Str(array_body.get(1..)?))?,
                    _ => return Err("unexpected token (3)"),
                };
            }
        },
        b'\"' => {
            let (string, next) = parse_string(Str(value.get(1..)?))?;
            file.set_string(path, string);
            Ok(next)
        },
        b'0'..=b'9' | b'-' => {
            let (number, next) = parse_number(value)?;
            file.set_number(path, number);
            Ok(next)
        },
        b't' if value.get(1..4)? == "rue".as_bytes() => {
            file.set_boolean(path, true);
            Ok(Str(value.get(4..)?))
        },
        b'f' if value.get(1..5)? == "alse".as_bytes() => {
            file.set_boolean(path, true);
            Ok(Str(value.get(5..)?))
        },
        b'n' if value.get(1..4)? == "ull".as_bytes() => Ok(Str(value.get(4..)?)),
        _ => Err("unexpected token (4)")
    }
}

/// Cloning this is cheap
pub struct ArrayIter<'a> {
    state: &'a JsonFile,
    base_path: Path,
    next: usize,
    len: usize,
}

impl<'a> Iterator for ArrayIter<'a> {
    type Item = (usize, &'a JsonFile, Path);
    fn next(&mut self) -> Option<Self::Item> {
        if self.next < self.len {
            let mut path = self.base_path.clone();
            let index = self.next;
            path.index_num(index);
            self.next += 1;
            Some((index, self.state, path))
        } else {
            None
        }
    }
}

impl<'a> Clone for ArrayIter<'a> {
    fn clone(&self) -> Self {
        Self {
            state: self.state,
            base_path: self.base_path.clone(),
            next: self.next,
            len: self.len,
        }
    }
}

static HEX: [u8; 256] = {
    const __: u8 = 255; // not a hex digit
    [
        //   1   2   3   4   5   6   7   8   9   A   B   C   D   E   F
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // 0
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // 1
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // 2
        00, 01, 02, 03, 04, 05, 06, 07, 08, 09, __, __, __, __, __, __, // 3
        __, 10, 11, 12, 13, 14, 15, __, __, __, __, __, __, __, __, __, // 4
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // 5
        __, 10, 11, 12, 13, 14, 15, __, __, __, __, __, __, __, __, __, // 6
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // 7
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // 8
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // 9
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // A
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // B
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // C
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // D
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // E
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // F
    ]
};

#[test]
fn quick_test() {
    let text = "{ \"name\": \"Default Theme\", \"version\": 0, \"styles\": { \"default\": { \"background\": \"222F\", \"foreground\": \"EEEF\", \"outline\": \"999F\" } } }";
    let json = JsonFile::new(Some(text)).unwrap();
    assert_eq!(text, &*json.dump(&Path::new()).unwrap());
    core::mem::drop(json);

    assert_eq!(Err("json input looks truncated"), JsonFile::new(Some("\"\\u\"")).map(|_| ()));
}
