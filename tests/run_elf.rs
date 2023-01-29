use object::{Object, ObjectSection};
use riscv_emulator::execute::Hart;
use riscv_emulator::platform::{AddressSpace, PlatformState};
use std::error::Error;
use std::fs;

fn parse_text_init<'a>(bin_data: &'a Vec<u8>) -> &'a [u8] {
    let obj_file = object::File::parse(bin_data.as_slice()).expect("parsing failed");
    let section = obj_file
        .section_by_name(".text.init")
        .expect("init text section not found");
    section.data().expect("section data not readable")
}

#[test]
fn parsing() -> Result<(), Box<dyn Error>> {
    let binary = fs::read("./tests/binaries/rv32ui-p-add")?;
    let data_ref = parse_text_init(&binary);

    assert_eq!(data_ref[0], 0x6f);

    Ok(())
}

#[test]
fn load_elf_add() {
    let mut mem = vec![0u8; 0x100_0000];
    let address_space = AddressSpace {
        main_memory: mem.as_mut_slice().try_into().expect("Wrong memory size"),
    };

    let binary = fs::read("./tests/binaries/rv32ui-p-add").expect("File read failed");
    let data_ref = parse_text_init(&binary);
    // Copy to start of main memory
    address_space.main_memory[..data_ref.len()].copy_from_slice(data_ref);

    let mut hart = Hart {
        address_space,
        execution_env: PlatformState::default(),
        reg_pc: 0x100_0000,
        regs: [0; 32],
    };

    assert!(hart.step_instruction().is_ok());
    assert_eq!(hart.reg_pc, 0x100_0048, "Jump failed");

    // Execute for at most 100 batches
    for _ in 0..100 {
        hart.run(100);
        // lowest byte of `tohost`
        if hart.address_space.main_memory[0x1000] != 0 {
            assert_eq!(hart.address_space.main_memory[0x1000], 1);
            return;
        }
    }

    panic!("The hart didn't write to host before the step limit!")
}
