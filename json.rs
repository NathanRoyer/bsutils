//! Compact JSON Storage, with (de)serialization

use core::{slice::SliceIndex, iter::from_fn, fmt, str::from_utf8, mem::swap, hash::{Hash, Hasher, BuildHasher}};
use super::{ro_string::rc::RoString, LiteMap};
use alloc::{vec::Vec, boxed::Box};
use ahash::AHasher;

pub type JsonParsingError = &'static str;

/// One step in a JSON state path
#[derive(Debug, Clone, Hash)]
enum StatePathStep<'a> {
    Key(&'a str),
    Index(usize),
}

pub type ArrayLength = usize;

/// Standalone JSON Value
pub enum JsonValue {
    Array(ArrayLength),
    Object(ObjectKeys),
    String(RoString),
    Number(f64),
}

/// All Keys stored in one allocation.
pub struct ObjectKeys(Box<[u8]>);

impl ObjectKeys {
    pub fn iter(&self) -> impl Iterator<Item = &str> {
        let mut i = 0;
        from_fn(move || {
            if i < self.0.len() {
                let start = i;

                while self.0[i] != 0 {
                    i += 1;
                }

                let slice = &self.0[start..i];
                i += 1;

                Some(from_utf8(slice).unwrap())
            } else {
                None
            }
        })
    }

    pub fn push(&mut self, key: &RoString) {
        let mut tmp = Vec::new().into_boxed_slice();
        swap(&mut tmp, &mut self.0);
        let mut vec = tmp.into_vec();
        vec.extend_from_slice(key.as_bytes());
        vec.push(0);
        self.0 = vec.into_boxed_slice();
    }
}

impl From<Vec<u8>> for ObjectKeys {
    fn from(vec: Vec<u8>) -> Self {
        Self(vec.into_boxed_slice())
    }
}

#[derive(Clone)]
pub struct JsonPath(AHasher);

impl JsonPath {
    pub fn new() -> Self {
        Self(super::GEN.build_hasher())
    }

    pub fn index_str(&mut self, key: &str) {
        StatePathStep::Key(&key).hash(&mut self.0);
    }

    pub fn index_num(&mut self, index: usize) {
        StatePathStep::Index(index).hash(&mut self.0);
    }

    /// Parse a string as a list of path steps
    pub fn parse(path: &str) -> Self {
        let mut out_path = Self::new();

        for step in path.split('.') {
            match step.parse::<usize>() {
                Ok(index) => out_path.index_num(index),
                Err(_) => out_path.index_str(step),
            }
        }

        out_path
    }
}

pub struct JsonFile(LiteMap<u64, JsonValue>);

impl JsonFile {
    pub fn parse(json: &str) -> Result<Self, JsonParsingError> {
        let mut file = Self(LiteMap::new());
        let rem = parse_value(Str(json.as_bytes()), &mut file, &JsonPath::new())?;
        match skip_ws(rem) {
            Err(_) => Ok(file),
            Ok(_) => Err("unexpected token (5)"),
        }
    }

    pub fn get(&self, path: &JsonPath) -> Option<&JsonValue> {
        self.0.get(&path.0.finish())
    }

    pub fn set_array(&mut self, path: &JsonPath) {
        self.0.insert(path.0.finish(), JsonValue::Array(0));
    }

    pub fn set_object(&mut self, path: &JsonPath) {
        self.0.insert(path.0.finish(), JsonValue::Object(Vec::new().into()));
    }

    pub fn set_number(&mut self, path: &JsonPath, value: f64) {
        self.0.insert(path.0.finish(), JsonValue::Number(value));
    }

    pub fn set_string(&mut self, path: &JsonPath, value: RoString) {
        self.0.insert(path.0.finish(), JsonValue::String(value));
    }

    pub fn push(&mut self, path: &JsonPath) -> JsonPath {
        let val = self.0.get_mut(&path.0.finish());
        let mut path = path.clone();

        if let Some(JsonValue::Array(num)) = val {
            path.index_num(*num);
            *num += 1;
        } else {
            panic!("JsonValue at `path` is not an array");
        }

        path
    }

    pub fn prop(&mut self, path: &JsonPath, key: RoString) -> JsonPath {
        let val = self.0.get_mut(&path.0.finish());
        let mut path = path.clone();

        if let Some(JsonValue::Object(keys)) = val {
            path.index_str(&key);
            keys.push(&key);
        } else {
            panic!("JsonValue at `path` is not an object");
        }

        path
    }

    fn write_fmt(&self, f: &mut fmt::Formatter<'_>, path: &JsonPath) -> fmt::Result {
        match self.get(path).unwrap() {
            JsonValue::Array(num) => {
                write!(f, "[ ")?;
                for i in 0..*num {
                    let mut path = path.clone();
                    path.index_num(i);
                    self.write_fmt(f, &path)?;

                    if (i + 1) != *num {
                        write!(f, ", ")?;
                    }
                }
                write!(f, " ]")
            },
            JsonValue::Object(keys) => {
                write!(f, "{{ ")?;
                let mut iter = keys.iter();
                let mut value = iter.next();
                while let Some(key) = value {
                    write!(f, "{:?}: ", key)?;

                    let mut path = path.clone();
                    path.index_str(key);
                    self.write_fmt(f, &path)?;

                    value = iter.next();
                    if value.is_some() {
                        write!(f, ", ")?;
                    }
                }
                write!(f, " }}")
            },
            JsonValue::String(string) => write!(f, "{:?}", string),
            JsonValue::Number(num) => write!(f, "{}", num),
        }
    }
}

/// Dumps the JSON text to a Formatter
impl fmt::Display for JsonFile {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.write_fmt(f, &JsonPath::new())
    }
}

// PARSING

struct Str<'a>(&'a [u8]);

impl<'a> Str<'a> {
    fn get<I: SliceIndex<[u8]>>(&self, i: I) -> Result<&'a I::Output, JsonParsingError> {
        match self.0.get(i) {
            Some(v) => Ok(v),
            None => Err("json input looks truncated"),
        }
    }
}

fn skip_ws<'a>(json: Str<'a>) -> Result<Str<'a>, JsonParsingError> {
    match json.get(0)? {
        b'\t' |
        b'\n' |
        b'\r' |
        b' ' => skip_ws(Str(&json.get(1..)?)),
        _ => Ok(json),
    }
}

fn parse_string_for_real<'a>(mut string: Str<'a>, char_count: usize) -> RoString {
    let mut pending: Option<(usize, usize, [u8; 4])> = None;
    RoString::from_iter((0..char_count).map(|_| {
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
    }))
}

fn parse_string<'a>(backup: Str<'a>) -> Result<(RoString, Str<'a>), JsonParsingError> {
    let mut string = Str(backup.0);
    let mut char_count = 0;

    let ro_string = loop {
        let (add, skip) = match string.get(0)? {
            b'\"' => break parse_string_for_real(Str(backup.0), char_count),
            b'\\' => match string.get(1)? {
                b'\"' |
                b'\\' |
                b'/' |
                b'b' |
                b'f' |
                b'n' |
                b'r' |
                b't' => (1, 2),
                b'u' => {
                    type U = usize;
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
    return Ok((ro_string, Str(backup.get(offset..)?)));
}

fn parse_number<'a>(value: Str<'a>) -> Result<(f64, Str<'a>), JsonParsingError> {
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

fn parse_value<'a>(value: Str<'a>, file: &mut JsonFile, path: &JsonPath) -> Result<Str<'a>, JsonParsingError> {
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

                let path = file.prop(path, key);
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
            let (number, next) = parse_number(Str(value.get(1..)?))?;
            file.set_number(path, number);
            Ok(next)
        },
        _ => Err("unexpected token (4)")
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
