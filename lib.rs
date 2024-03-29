//! Low Memory Footprint Utilities

#![no_std]

extern crate alloc;

#[cfg(any(feature = "hashmap", feature = "json"))]
use ahash::RandomState;

static SEED: &'static [u8] = include_bytes!(concat!(env!("OUT_DIR"), "/seed.dat"));

macro_rules! seed {
    ($i:literal) => ( [
        SEED[$i + 0], SEED[$i + 1], SEED[$i + 2], SEED[$i + 3],
        SEED[$i + 4], SEED[$i + 5], SEED[$i + 6], SEED[$i + 7],
    ] )
}

#[cfg(any(feature = "hashmap", feature = "json"))]
pub(crate) static GEN: RandomState = RandomState::with_seeds(
    u64::from_ne_bytes(seed!( 0)), u64::from_ne_bytes(seed!( 8)),
    u64::from_ne_bytes(seed!(16)), u64::from_ne_bytes(seed!(24)),
);

#[cfg(feature = "hashmap")]
pub mod hash_map;

#[cfg(feature = "json")]
pub mod json;

#[cfg(feature = "strpool")]
pub use strpool;

#[cfg(feature = "litemap")]
pub use litemap;

#[cfg(feature = "litemap")]
/// From the awesome [litemap](https://docs.rs/litemap) crate:
pub use litemap::LiteMap;

#[cfg(feature = "litemap")]
pub type LiteSet<T> = LiteMap<T, ()>;

#[cfg(feature = "arcstr")]
pub use arcstr;

#[cfg(feature = "arcstr")]
/// From the awesome [arcstr](https://docs.rs/arcstr) crate:
pub use arcstr::ArcStr;

#[cfg(feature = "hashmap")]
#[doc(inline)]
pub use hash_map::HashMap;

#[cfg(feature = "hashmap")]
pub type HashSet<T> = HashMap<T, ()>;

#[cfg(feature = "arrayvec")]
pub use arrayvec;

#[cfg(feature = "arrayvec")]
/// From the awesome [arrayvec](https://docs.rs/arrayvec) crate:
pub use arrayvec::ArrayVec;

#[cfg(feature = "thinvec")]
mod thin_vec;

#[cfg(feature = "thinvec")]
/// From the awesome [thin-vec](https://docs.rs/thin-vec/0.2.12) crate:
pub use thin_vec::ThinVec;
