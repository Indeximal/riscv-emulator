use crate::Uxlen;

use self::exception::Exception;

pub mod exception {
    /// An exception causes a trap which is either run in a more priviledged mode
    /// (vertical trap) or at the same priviledge mode (horizontal trap).
    #[derive(Debug)]
    pub enum Exception {
        AccessFault,
        IllegalInstruction(IllegalInstrCause),
    }

    // TODO: Do I need this for ISA support or just debugging?
    #[derive(Debug)]
    pub enum IllegalInstrCause {
        CSRNotWritable,
        CSRNotReadable,
        CSRNotDefined,
    }
}

/// 64 bit byte addressable circular address space.
///
/// Portions might be either vacant, main memory or i/o devices.
/// Inaccessable accesses cause an exception.
///
/// Defines byte (1B), halfword(2B), word(4B) or quadword(8B)
///
/// Little endian by design, such that instruction fetches (always LE)
/// and word fetches work the same.
pub struct AddressSpace<'a> {
    /// Maps to 0x100_0000 - 0x1ff_ffff, 16 MB memory
    main_memory: &'a mut [u8; 0x100_0000],
}

impl<'a> AddressSpace<'a> {
    const MEM_SIZE: Uxlen = 1 << 24;

    /// This might need optimizations, e.g. Const generics for width
    fn address(&self, addr: Uxlen, width: usize) -> Result<usize, Exception> {
        if addr & !(Self::MEM_SIZE - 1) == Self::MEM_SIZE
            && (addr + width as Uxlen - 1) & !(Self::MEM_SIZE - 1) == Self::MEM_SIZE
        {
            Ok((addr & (Self::MEM_SIZE - 1)) as usize)
        } else {
            Err(Exception::AccessFault)
        }
    }

    pub fn read_word(&self, addr: Uxlen) -> Result<u32, Exception> {
        let lsb_index = self.address(addr, 4)?;
        Ok(u32::from_le_bytes(
            self.main_memory[lsb_index..lsb_index + 4]
                .try_into()
                .unwrap(),
        ))
    }

    pub fn read_halfword(&self, addr: Uxlen) -> Result<u16, Exception> {
        let lsb_index = self.address(addr, 2)?;
        Ok(u16::from_le_bytes(
            self.main_memory[lsb_index..lsb_index + 2]
                .try_into()
                .unwrap(),
        ))
    }

    pub fn read_byte(&self, addr: Uxlen) -> Result<u8, Exception> {
        let lsb_index = self.address(addr, 1)?;
        Ok(self.main_memory[lsb_index])
    }

    pub fn write_word(&mut self, addr: Uxlen, val: u32) -> Result<(), Exception> {
        let lsb_index = self.address(addr, 4)?;
        self.main_memory[lsb_index..lsb_index + 4].copy_from_slice(&val.to_le_bytes());

        Ok(())
    }

    pub fn write_halfword(&mut self, addr: Uxlen, val: u16) -> Result<(), Exception> {
        let lsb_index = self.address(addr, 2)?;
        self.main_memory[lsb_index..lsb_index + 2].copy_from_slice(&val.to_le_bytes());

        Ok(())
    }

    pub fn write_byte(&mut self, addr: Uxlen, val: u8) -> Result<(), Exception> {
        let lsb_index = self.address(addr, 2)?;
        self.main_memory[lsb_index] = val;

        Ok(())
    }
}

#[test]
fn mem_test() {
    let mut mem = vec![0u8; 0x100_0000];
    let mut address_space = AddressSpace {
        main_memory: mem.as_mut_slice().try_into().expect("Wrong memory size"),
    };

    address_space
        .write_word(AddressSpace::MEM_SIZE, 0x12_34_56_78)
        .expect("Write bound check failed");
    assert_eq!(address_space.main_memory[0..4], [0x78, 0x56, 0x34, 0x12]);
    assert_eq!(
        address_space
            .read_word(AddressSpace::MEM_SIZE)
            .expect("Read bounds check failed"),
        0x12_34_56_78
    );
}

pub enum PriviledgeMode {
    Machine,
}

/// Table 3.2 in priviledged ISA
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

pub struct Csr {
    /// Hart Id. Zero in single core system. Keep low, but unique.
    mhartid: Uxlen,
    /// This WARL register is constant in this implementation. 0 if not implemented.
    misa: Uxlen,
    /// In this simulation, the cycle, time and instret counter are all the same value.
    tick_count: u64,
}

impl Default for Csr {
    /// The reset state
    fn default() -> Self {
        Self {
            mhartid: 0,
            // FIXME: dynamic 64 bit
            misa: (1 << 30) | isa_flags::I,
            tick_count: 0,
        }
    }
}

impl Csr {
    /// The lower 12 bits of `addr` encode the CSR specifier.
    /// Section 2.2 of the priviledged Spec
    ///
    /// The result is zero extended to `Uxlen`.
    pub fn read(&mut self, addr: u16) -> Result<Uxlen, Exception> {
        use exception::IllegalInstrCause;
        match addr {
            0xC00 => Ok(self.tick_count as Uxlen),         // Cycle
            0xC01 => Ok(self.tick_count as Uxlen),         // Time
            0xC02 => Ok(self.tick_count as Uxlen),         // Instruction retired
            0xC80 => Ok((self.tick_count >> 32) as Uxlen), // Cycle high
            0xC81 => Ok((self.tick_count >> 32) as Uxlen), // Time high
            0xC82 => Ok((self.tick_count >> 32) as Uxlen), // Instruction retired high
            // Other performance counter (0xC00..=0xC9F) are not implemented
            0x301 => Ok(self.misa),     // Machine ISA
            0xF11 => Ok(0),             // Vendor id. Zero since this is not commercial
            0xF12 => Ok(0),             // Architecture id. Zero since this is not registered
            0xF13 => Ok(0x13_09_B9_5C), // Implementation id. Randomly chosen
            0xF14 => Ok(self.mhartid),  // Hart id
            _ => Err(Exception::IllegalInstruction(
                IllegalInstrCause::CSRNotDefined,
            )),
        }
    }

    /// The lower 12 bits of `addr` encode the CSR specifier.
    /// TODO: use Read-Modify-Write?
    pub fn write(&mut self, addr: u16, _value: Uxlen) -> Result<(), Exception> {
        use exception::IllegalInstrCause;
        match addr {
            // Performance Counters (read only)
            0xC00..=0xC9F => Err(Exception::IllegalInstruction(
                IllegalInstrCause::CSRNotWritable,
            )),
            0x301 => Ok(()), // Ignore WARL Machine ISA Write
            // Machine ids (read only)
            0xF11..=0xF14 => Err(Exception::IllegalInstruction(
                IllegalInstrCause::CSRNotWritable,
            )),
            _ => Err(Exception::IllegalInstruction(
                IllegalInstrCause::CSRNotDefined,
            )),
        }
    }

    pub fn increment_tick(&mut self) {
        self.tick_count += 1;
    }
}
