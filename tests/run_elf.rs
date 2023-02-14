//!
//! These tests are from https://github.com/riscv-software-src/riscv-tests
//!
//! Included tests:
//! rv64ui-p-*
//! rv64mi-p-*
//!

use riscv_emulator::execute::Hart;
use riscv_emulator::platform::exception::SynchronousCause;
use riscv_emulator::platform::{AddressSpace, PlatformState};
use riscv_emulator::Uxlen;

use object::{Object, ObjectSection};
use std::error::Error;
use std::fs;
use std::path::PathBuf;

struct ElfTestAddressSpace {
    /// Maps to 0x8000_0000 - 0x8000_2fff, 16 KiB memory
    main_memory: Box<[u8; 0x4000]>,

    tohost: u32,
}

impl ElfTestAddressSpace {
    const MEM_MASK: Uxlen = !0x0000_0000_0000_2fff;
    const MEM_PATTERN: Uxlen = 0x0000_0000_8000_0000;

    fn address<const WIDTH: usize>(&self, addr: Uxlen) -> Result<usize, ()> {
        let end_addr = addr + WIDTH as Uxlen - 1;
        if addr & Self::MEM_MASK == Self::MEM_PATTERN
            && end_addr & Self::MEM_MASK == Self::MEM_PATTERN
        {
            Ok((addr & !Self::MEM_MASK) as usize)
        } else {
            Err(())
        }
    }

    /// Create a new address space with the main memory on the heap.
    fn new() -> Self {
        // Cannot use `Box::new([0u8; 0x4000])` as this creates the data on the stack first.
        let mem = vec![0u8; 0x4000].into_boxed_slice();
        ElfTestAddressSpace {
            // FIXME: compile time garantee?
            main_memory: mem.try_into().expect("Wrong memory size"),
            tohost: 0,
        }
    }
}

impl AddressSpace for ElfTestAddressSpace {
    fn read_doubleword(&self, addr: Uxlen) -> Result<u64, SynchronousCause> {
        let lsb_index = self
            .address::<8>(addr)
            .map_err(|_| SynchronousCause::LoadAccessFault)?;
        Ok(u64::from_le_bytes(
            self.main_memory[lsb_index..lsb_index + 8]
                .try_into()
                .unwrap(),
        ))
    }

    fn read_word(&self, addr: Uxlen) -> Result<u32, SynchronousCause> {
        let lsb_index = self
            .address::<4>(addr)
            .map_err(|_| SynchronousCause::LoadAccessFault)?;
        Ok(u32::from_le_bytes(
            self.main_memory[lsb_index..lsb_index + 4]
                .try_into()
                .unwrap(),
        ))
    }

    fn read_halfword(&self, addr: Uxlen) -> Result<u16, SynchronousCause> {
        let lsb_index = self
            .address::<2>(addr)
            .map_err(|_| SynchronousCause::LoadAccessFault)?;
        Ok(u16::from_le_bytes(
            self.main_memory[lsb_index..lsb_index + 2]
                .try_into()
                .unwrap(),
        ))
    }

    fn read_byte(&self, addr: Uxlen) -> Result<u8, SynchronousCause> {
        let lsb_index = self
            .address::<1>(addr)
            .map_err(|_| SynchronousCause::LoadAccessFault)?;
        Ok(self.main_memory[lsb_index])
    }

    fn write_doubleword(&mut self, addr: Uxlen, val: u64) -> Result<(), SynchronousCause> {
        let lsb_index = self
            .address::<8>(addr)
            .map_err(|_| SynchronousCause::StoreAMOAccessFault)?;
        self.main_memory[lsb_index..lsb_index + 8].copy_from_slice(&val.to_le_bytes());

        Ok(())
    }

    fn write_word(&mut self, addr: Uxlen, val: u32) -> Result<(), SynchronousCause> {
        if addr == 0x8000_1000 {
            self.tohost = val;
            return Err(SynchronousCause::Breakpoint);
        }

        let lsb_index = self
            .address::<4>(addr)
            .map_err(|_| SynchronousCause::StoreAMOAccessFault)?;
        self.main_memory[lsb_index..lsb_index + 4].copy_from_slice(&val.to_le_bytes());

        Ok(())
    }

    fn write_halfword(&mut self, addr: Uxlen, val: u16) -> Result<(), SynchronousCause> {
        let lsb_index = self
            .address::<2>(addr)
            .map_err(|_| SynchronousCause::StoreAMOAccessFault)?;
        self.main_memory[lsb_index..lsb_index + 2].copy_from_slice(&val.to_le_bytes());

        Ok(())
    }

    fn write_byte(&mut self, addr: Uxlen, val: u8) -> Result<(), SynchronousCause> {
        let lsb_index = self
            .address::<1>(addr)
            .map_err(|_| SynchronousCause::StoreAMOAccessFault)?;
        self.main_memory[lsb_index] = val;

        Ok(())
    }
}

#[test]
fn mem_test() {
    let mut address_space = ElfTestAddressSpace::new();

    address_space
        .write_word(0x8000_0000, 0x12_34_56_78)
        .expect("Write bound check failed");
    assert_eq!(address_space.main_memory[0..4], [0x78, 0x56, 0x34, 0x12]);
    assert_eq!(
        address_space
            .read_word(0x8000_0000)
            .expect("Read bounds check failed"),
        0x12_34_56_78
    );
}

fn parse_text_init<'a>(bin_data: &'a Vec<u8>) -> &'a [u8] {
    let obj_file = object::File::parse(bin_data.as_slice()).expect("parsing failed");

    let section = obj_file
        .section_by_name(".text.init")
        .expect("init text section not found");
    section.data().expect("section data not readable")
}

// Some tests have a .data section that is loaded at offset 0x2000
fn parse_data<'a>(bin_data: &'a Vec<u8>) -> Option<&'a [u8]> {
    let obj_file = object::File::parse(bin_data.as_slice()).expect("parsing failed");
    // Those test have a .data section:
    // Tests rv32ui-p-fence_i, rv32ui-p-lb, rv32ui-p-lbu, rv32ui-p-lh, rv32ui-p-lhu,
    //       rv32ui-p-lw, rv32ui-p-sb, rv32ui-p-sh, rv32ui-p-sw

    obj_file
        .section_by_name(".data")
        .map(|section| section.data().expect("section data not readable"))
}

#[test]
fn parsing() -> Result<(), Box<dyn Error>> {
    let binary = fs::read("./tests/binaries/rv32ui-p-add")?;
    let data_ref = parse_text_init(&binary);

    assert_eq!(data_ref[0], 0x6f);

    Ok(())
}

fn run_unittest_binary(name: &str, allowed_breakpoints: usize) {
    let mut address_space = ElfTestAddressSpace::new();

    let mut binary_path = PathBuf::from("./tests/binaries/");
    binary_path.push(name);
    let binary = fs::read(binary_path).expect("File read failed");
    let text_ref = parse_text_init(&binary);
    let data_ref = parse_data(&binary);
    // Copy .text to start of main memory
    address_space.main_memory[..text_ref.len()].copy_from_slice(text_ref);
    // Copy .data at an offset
    if let Some(data_ref) = data_ref {
        address_space.main_memory[0x2000..data_ref.len() + 0x2000].copy_from_slice(data_ref);
    }

    let mut hart = Hart {
        address_space,
        execution_env: PlatformState::default(),
        reg_pc: 0x8000_0000,
        regs: [0; 32],
    };

    use riscv_emulator::execute::StopReason::*;
    for _ in 0..allowed_breakpoints {
        match hart.run(10000) {
            MaxInstrReached => panic!("The hart didn't write to host before the step limit!"),
            BreakpointHit => {}
            UnrecoverableError => unreachable!("Not implemented in the simulator"),
        }
    }
    assert_eq!(
        hart.address_space.tohost, 1,
        "tohost wrote an non success value"
    )
}

macro_rules! binary_test {
    ($name:ident) => {
        binary_test! { $name, 1 }
    };
    ($name:ident, $breakp:expr) => {
        #[test]
        fn $name() {
            let _ = env_logger::Builder::from_env(
                env_logger::Env::default().default_filter_or("trace"),
            )
            .format_timestamp(None)
            .is_test(true)
            .try_init();
            run_unittest_binary(stringify!($name), $breakp);
        }
    };
}

// Machine mode tests

// FIXME: mtval
binary_test! { rv64mi_p_illegal }

// FIXME: fails since mcounteren is not implemented
binary_test! { rv64mi_p_csr }

// FIXME: user mode counter registers
binary_test! { rv64mi_p_zicntr }

// Needs Debug Mode
// binary_test! { rv64mi_p_breakpoint }

// Needs compressed instructions
// binary_test! { rv64mi_p_ma_fetch }

binary_test! { rv64mi_p_access }
binary_test! { rv64mi_p_ld_misaligned }
binary_test! { rv64mi_p_lh_misaligned }
binary_test! { rv64mi_p_lw_misaligned }
binary_test! { rv64mi_p_ma_addr }
binary_test! { rv64mi_p_mcsr }
binary_test! { rv64mi_p_ebreak, 2 }
binary_test! { rv64mi_p_ecall }
binary_test! { rv64mi_p_sd_misaligned }
binary_test! { rv64mi_p_sh_misaligned }
binary_test! { rv64mi_p_sw_misaligned }

// Usermode base extension tests
binary_test! { rv64ui_p_add }
binary_test! { rv64ui_p_addi }
binary_test! { rv64ui_p_addiw }
binary_test! { rv64ui_p_addw }
binary_test! { rv64ui_p_and }
binary_test! { rv64ui_p_andi }
binary_test! { rv64ui_p_auipc }
binary_test! { rv64ui_p_beq }
binary_test! { rv64ui_p_bge }
binary_test! { rv64ui_p_bgeu }
binary_test! { rv64ui_p_blt }
binary_test! { rv64ui_p_bltu }
binary_test! { rv64ui_p_bne }
binary_test! { rv64ui_p_fence_i }
binary_test! { rv64ui_p_jal }
binary_test! { rv64ui_p_jalr }
binary_test! { rv64ui_p_lb }
binary_test! { rv64ui_p_lbu }
binary_test! { rv64ui_p_ld }
binary_test! { rv64ui_p_lh }
binary_test! { rv64ui_p_lhu }
binary_test! { rv64ui_p_lui }
binary_test! { rv64ui_p_lw }
binary_test! { rv64ui_p_lwu }
// This is the only test where .tohost is not a 0x1000. I won't bother.
//binary_test! { rv64ui_p_ma_data }
binary_test! { rv64ui_p_or }
binary_test! { rv64ui_p_ori }
binary_test! { rv64ui_p_sb }
binary_test! { rv64ui_p_sd }
binary_test! { rv64ui_p_sh }
binary_test! { rv64ui_p_simple }
binary_test! { rv64ui_p_sll }
binary_test! { rv64ui_p_slli }
binary_test! { rv64ui_p_slliw }
binary_test! { rv64ui_p_sllw }
binary_test! { rv64ui_p_slt }
binary_test! { rv64ui_p_slti }
binary_test! { rv64ui_p_sltiu }
binary_test! { rv64ui_p_sltu }
binary_test! { rv64ui_p_sra }
binary_test! { rv64ui_p_srai }
binary_test! { rv64ui_p_sraiw }
binary_test! { rv64ui_p_sraw }
binary_test! { rv64ui_p_srl }
binary_test! { rv64ui_p_srli }
binary_test! { rv64ui_p_srliw }
binary_test! { rv64ui_p_srlw }
binary_test! { rv64ui_p_sub }
binary_test! { rv64ui_p_subw }
binary_test! { rv64ui_p_sw }
binary_test! { rv64ui_p_xor }
binary_test! { rv64ui_p_xori }
