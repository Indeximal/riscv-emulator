pub type Uxlen = u64;
pub type Ixlen = i64;

mod decode;
pub mod execute;
pub mod platform;

/// Table 3.2 in priviledged ISA spec
///
/// Z extensions are not present in this register.
#[allow(dead_code)]
mod isa_flags {
    use crate::Uxlen;

    pub const A: Uxlen = 1 << 0; // Atomic extension
    pub const B: Uxlen = 1 << 1; // Tentatively reserved for Bit-Manipulation extension
    pub const C: Uxlen = 1 << 2; // Compressed extension
    pub const D: Uxlen = 1 << 3; // Double-precision floating-point extension
    pub const E: Uxlen = 1 << 4; // RV32E base ISA
    pub const F: Uxlen = 1 << 5; // Single-precision floating-point extension
    pub const H: Uxlen = 1 << 7; // Hypervisor extension
    pub const I: Uxlen = 1 << 8; // RV32I/64I/128I base ISA
    pub const J: Uxlen = 1 << 9; // Tentatively reserved for Dynamically Translated Languages extension
    pub const M: Uxlen = 1 << 12; // Integer Multiply/Divide extension
    pub const N: Uxlen = 1 << 13; // Tentatively reserved for User-Level Interrupts extension
    pub const P: Uxlen = 1 << 15; // Tentatively reserved for Packed-SIMD extension
    pub const Q: Uxlen = 1 << 16; // Quad-precision floating-point extension
    pub const S: Uxlen = 1 << 18; // Supervisor mode implemented
    pub const U: Uxlen = 1 << 20; // User mode implemented
    pub const V: Uxlen = 1 << 21; // Tentatively reserved for Vector extension
    pub const X: Uxlen = 1 << 23; // Non-standard extensions present
}
