//! Low Memory Footprint Utilities

#![no_std]

extern crate alloc;

#[cfg(any(feature = "hashmap", feature = "json"))]
use ahash::RandomState;

static SEED: &'static [u8] = include_bytes!(concat!(env!("OUT_DIR"), "/seed.dat"));

macro_rules! seed {
    ($i:literal) => ( [
        SEED[$i + 0],
        SEED[$i + 1],
        SEED[$i + 2],
        SEED[$i + 3],
        SEED[$i + 4],
        SEED[$i + 5],
        SEED[$i + 6],
        SEED[$i + 7],
    ] )
}

#[cfg(any(feature = "hashmap", feature = "json"))]
pub(crate) static GEN: RandomState = RandomState::with_seeds(
    u64::from_ne_bytes(seed!( 0)),
    u64::from_ne_bytes(seed!( 8)),
    u64::from_ne_bytes(seed!(16)),
    u64::from_ne_bytes(seed!(24)),
);

#[cfg(feature = "hashmap")]
pub mod hash_map;

#[cfg(feature = "rostring")]
pub mod ro_string;

#[cfg(feature = "json")]
pub mod json;

#[cfg(feature = "litemap")]
/// From the awesome [litemap](https://docs.rs/litemap) crate:
pub use litemap::LiteMap;

#[cfg(feature = "hashmap")]
pub use hash_map::HashMap;
