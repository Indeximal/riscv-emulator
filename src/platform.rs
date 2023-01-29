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

pub struct Csr {
    /// In this simulation, the cycle, time and instret counter are all the same value.
    tick_count: u64,
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
            _ => Err(Exception::IllegalInstruction(
                IllegalInstrCause::CSRNotDefined,
            )),
        }
    }

    pub fn increment_tick(&mut self) {
        self.tick_count += 1;
    }
}
