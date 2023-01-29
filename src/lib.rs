#[cfg(feature = "rv64i")]
pub type Uxlen = u64;
#[cfg(feature = "rv64i")]
pub type Ixlen = i64;
#[cfg(feature = "rv32i")]
pub type Uxlen = u32;
#[cfg(feature = "rv32i")]
pub type Ixlen = i32;

mod decode;
pub mod execute;
pub mod platform;
