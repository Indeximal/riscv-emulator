use crate::Uxlen;

use self::exception::Exception;

pub mod exception {
    #[derive(Debug)]
    pub enum Exception {
        AccessFault,
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
