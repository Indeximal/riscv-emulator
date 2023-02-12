//!
//! These tests are from https://github.com/riscv-software-src/riscv-tests
//!
//! Included tests:
//! rv32ui-p-*
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
}

impl ElfTestAddressSpace {
    const MEM_MASK: Uxlen = 0xffff_c000;
    const MEM_PATTERN: Uxlen = 0x8000_0000;

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
        }
    }
}

impl AddressSpace for ElfTestAddressSpace {
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

    fn write_word(&mut self, addr: Uxlen, val: u32) -> Result<(), SynchronousCause> {
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

fn run_unittest_binary(name: &str, num_step_batches: usize) {
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

    // Watchdog
    for _ in 0..num_step_batches {
        hart.run(100);
        // Lowest byte of `tohost`
        if hart.address_space.main_memory[0x1000] != 0 {
            assert_eq!(hart.address_space.main_memory[0x1000], 1);
            return;
        }
    }

    panic!("The hart didn't write to host before the step limit!")
}

#[test]
fn test_rv32ui_p_add() {
    run_unittest_binary("rv32ui-p-add", 100);
}
#[test]
fn test_rv32ui_p_addi() {
    run_unittest_binary("rv32ui-p-addi", 100);
}
#[test]
fn test_rv32ui_p_and() {
    run_unittest_binary("rv32ui-p-and", 100);
}
#[test]
fn test_rv32ui_p_andi() {
    run_unittest_binary("rv32ui-p-andi", 100);
}
#[test]
fn test_rv32ui_p_auipc() {
    run_unittest_binary("rv32ui-p-auipc", 100);
}
#[test]
fn test_rv32ui_p_beq() {
    run_unittest_binary("rv32ui-p-beq", 100);
}
#[test]
fn test_rv32ui_p_bge() {
    run_unittest_binary("rv32ui-p-bge", 100);
}
#[test]
fn test_rv32ui_p_bgeu() {
    run_unittest_binary("rv32ui-p-bgeu", 100);
}
#[test]
fn test_rv32ui_p_blt() {
    run_unittest_binary("rv32ui-p-blt", 100);
}
#[test]
fn test_rv32ui_p_bltu() {
    run_unittest_binary("rv32ui-p-bltu", 100);
}
#[test]
fn test_rv32ui_p_bne() {
    run_unittest_binary("rv32ui-p-bne", 100);
}
#[test]
fn test_rv32ui_p_fence_i() {
    run_unittest_binary("rv32ui-p-fence_i", 100);
}
#[test]
fn test_rv32ui_p_jal() {
    run_unittest_binary("rv32ui-p-jal", 100);
}
#[test]
fn test_rv32ui_p_jalr() {
    run_unittest_binary("rv32ui-p-jalr", 100);
}
#[test]
fn test_rv32ui_p_lb() {
    run_unittest_binary("rv32ui-p-lb", 100);
}
#[test]
fn test_rv32ui_p_lbu() {
    run_unittest_binary("rv32ui-p-lbu", 100);
}
#[test]
fn test_rv32ui_p_lh() {
    run_unittest_binary("rv32ui-p-lh", 100);
}
#[test]
fn test_rv32ui_p_lhu() {
    run_unittest_binary("rv32ui-p-lhu", 100);
}
#[test]
fn test_rv32ui_p_lui() {
    run_unittest_binary("rv32ui-p-lui", 100);
}
#[test]
fn test_rv32ui_p_lw() {
    run_unittest_binary("rv32ui-p-lw", 100);
}
#[test]
fn test_rv32ui_p_or() {
    run_unittest_binary("rv32ui-p-or", 100);
}
#[test]
fn test_rv32ui_p_ori() {
    run_unittest_binary("rv32ui-p-ori", 100);
}
#[test]
fn test_rv32ui_p_sb() {
    run_unittest_binary("rv32ui-p-sb", 100);
}
#[test]
fn test_rv32ui_p_sh() {
    run_unittest_binary("rv32ui-p-sh", 100);
}
#[test]
fn test_rv32ui_p_simple() {
    run_unittest_binary("rv32ui-p-simple", 100);
}
#[test]
fn test_rv32ui_p_sll() {
    run_unittest_binary("rv32ui-p-sll", 100);
}
#[test]
fn test_rv32ui_p_slli() {
    run_unittest_binary("rv32ui-p-slli", 100);
}
#[test]
fn test_rv32ui_p_slt() {
    run_unittest_binary("rv32ui-p-slt", 100);
}
#[test]
fn test_rv32ui_p_slti() {
    run_unittest_binary("rv32ui-p-slti", 100);
}
#[test]
fn test_rv32ui_p_sltiu() {
    run_unittest_binary("rv32ui-p-sltiu", 100);
}
#[test]
fn test_rv32ui_p_sltu() {
    run_unittest_binary("rv32ui-p-sltu", 100);
}
#[test]
fn test_rv32ui_p_sra() {
    run_unittest_binary("rv32ui-p-sra", 100);
}
#[test]
fn test_rv32ui_p_srai() {
    run_unittest_binary("rv32ui-p-srai", 100);
}
#[test]
fn test_rv32ui_p_srl() {
    run_unittest_binary("rv32ui-p-srl", 100);
}
#[test]
fn test_rv32ui_p_srli() {
    run_unittest_binary("rv32ui-p-srli", 100);
}
#[test]
fn test_rv32ui_p_sub() {
    run_unittest_binary("rv32ui-p-sub", 100);
}
#[test]
fn test_rv32ui_p_sw() {
    run_unittest_binary("rv32ui-p-sw", 100);
}
#[test]
fn test_rv32ui_p_xor() {
    run_unittest_binary("rv32ui-p-xor", 100);
}
#[test]
fn test_rv32ui_p_xori() {
    run_unittest_binary("rv32ui-p-xori", 100);
}
