//! https://riscv.org/technical/specifications/
//!
//! # TODO
//! * Exceptions
//! * Tests
//!

use std::ops::IndexMut;

use decode::{BType, IType, JType, RType, SType, UType};
use exception::Exception;

pub type Uxlen = u32;
pub type Ixlen = i32;

mod decode;

mod exception {
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
    /// Maps to 0x10000 - 0x1000000, 16 MB memory
    main_memory: &'a mut [u8; 0xfe_ff_ff],
}

impl<'a> AddressSpace<'a> {
    const MEM_START: Uxlen = 0x1_0000;
    const MEM_END: Uxlen = 0x100_0000;

    /// `addr` (should, not quite sure) be the lowest memory byte.
    /// msB add addr+NUMBYTES.
    ///
    /// Return &value[0] is the LSB.
    ///
    /// This is slightly overengineered, especially for u8, but should optimize out
    fn address<const NUMBYTES: usize>(
        &mut self,
        addr: Uxlen,
    ) -> Result<&mut [u8; NUMBYTES], Exception> {
        if addr >= Self::MEM_START && addr < Self::MEM_END - NUMBYTES as Uxlen {
            let subslice = self.main_memory.index_mut(
                ((addr - Self::MEM_START) as usize)
                    ..(addr as usize - Self::MEM_START as usize + NUMBYTES),
            );
            Ok(subslice
                .try_into()
                .expect("Slice range indexing didn't return length NUMBYTES!"))
        } else {
            Err(Exception::AccessFault)
        }
    }

    // FIXME: mutable access ?
    pub fn read_word(&mut self, addr: Uxlen) -> Result<u32, Exception> {
        let &mut val = self.address(addr)?;
        Ok(u32::from_le_bytes(val))
    }

    pub fn read_halfword(&mut self, addr: Uxlen) -> Result<u16, Exception> {
        let &mut val = self.address(addr)?;
        Ok(u16::from_le_bytes(val))
    }

    pub fn read_byte(&mut self, addr: Uxlen) -> Result<u8, Exception> {
        let &mut val = self.address(addr)?;
        Ok(u8::from_le_bytes(val))
    }

    pub fn write_word(&mut self, addr: Uxlen, val: u32) -> Result<(), Exception> {
        let &mut mut bytes = self.address::<4>(addr)?;
        bytes.copy_from_slice(val.to_le_bytes().as_slice());
        Ok(())
    }
}

#[test]
fn mem_test() {
    let mut mem = vec![0u8; 0xfe_ff_ff];
    let mut address_space = AddressSpace {
        main_memory: mem.as_mut_slice().try_into().expect("Wrong memory size"),
    };

    // FIXME: writing doesn't work

    address_space
        .write_word(AddressSpace::MEM_START, 0x12_34_56_78)
        .expect("Bound check failed");
    assert_eq!(address_space.main_memory[0..4], [0x78, 0x56, 0x34, 0x12]);
    assert_eq!(
        address_space
            .read_word(AddressSpace::MEM_START)
            .expect("Bounds check failed"),
        0x12_34_56_78
    );
}

/// Hardware Thread
///
pub struct Hart<'a> {
    address_space: AddressSpace<'a>,

    reg_pc: Uxlen,
    /// x0 is always zero
    /// x1 is usually the return address
    /// x2 is usually the stack pointer
    /// # INVARIANT
    /// regs[0] is always zero!
    regs: [Uxlen; 32],
}

impl<'a> Hart<'a> {
    /// Fetches, decodes, executes one instruction and increments the PC.
    ///
    /// Backed by `execute_xxx` functions that take the decoded instruction and
    /// apply it to the architectural state. They assume proper decoding,
    /// e.g. the destination register is never 0!
    /// Advancing the PC is done in this function, but some functions might touch
    /// the PC as part of their functionality.
    ///
    /// FIXME: Exception handling, i.e. is PC incremented or not??
    ///  
    pub fn execute_instruction(&mut self) -> Result<(), Exception> {
        let instruction = self.address_space.read_word(self.reg_pc)?;

        match decode::get_opcode(instruction) {
            decode::opcode::OP_IMM => 'instr_exec: {
                let instr: IType = instruction.into();
                if instr.rd == 0 {
                    self.hint(instruction);
                    break 'instr_exec;
                }
                match instr.funct3 {
                    0b000 => self.execute_addi(instr.rs1, instr.imm, instr.rd),
                    0b010 => self.execute_slti(instr.rs1, instr.imm, instr.rd),
                    0b011 => self.execute_sltiu(instr.rs1, instr.imm as Uxlen, instr.rd),
                    0b100 => self.execute_xori(instr.rs1, instr.imm as Uxlen, instr.rd),
                    0b110 => self.execute_ori(instr.rs1, instr.imm as Uxlen, instr.rd),
                    0b111 => self.execute_andi(instr.rs1, instr.imm as Uxlen, instr.rd),
                    0b001 => self.execute_slli(instr.rs1, instr.imm as Uxlen, instr.rd),
                    0b101 => {
                        // FIXME: Warning on illegal funct7
                        if instr.imm & 0b0100_0000_0000 == 0 {
                            self.execute_srli(instr.rs1, instr.imm as Uxlen, instr.rd)
                        } else {
                            self.execute_srai(instr.rs1, instr.imm as Uxlen, instr.rd)
                        }
                    }
                    _ => unreachable!("funct3 should only be 3 bits"),
                }
                self.reg_pc += 4;
            }
            decode::opcode::LUI => 'instr_exec: {
                let instr: UType = instruction.into();
                if instr.rd == 0 {
                    self.hint(instruction);
                    break 'instr_exec;
                }
                self.execute_lui(instr.imm, instr.rd);
                self.reg_pc += 4;
            }
            decode::opcode::AUIPC => 'instr_exec: {
                let instr: UType = instruction.into();
                if instr.rd == 0 {
                    self.hint(instruction);
                    break 'instr_exec;
                }
                self.execute_auipc(instr.imm, instr.rd);
                self.reg_pc += 4;
            }
            decode::opcode::OP => 'instr_exec: {
                let instr: RType = instruction.into();
                if instr.rd == 0 {
                    self.hint(instruction);
                    break 'instr_exec;
                }
                // FIXME: Warning on illegal funct7
                match instr.funct3 {
                    0b000 => {
                        if instr.funct7 == 0b010_000 {
                            self.execute_sub(instr.rs1, instr.rs2, instr.rd);
                        } else {
                            self.execute_add(instr.rs1, instr.rs2, instr.rd);
                        }
                    }
                    0b010 => self.execute_slt(instr.rs1, instr.rs2, instr.rd),
                    0b011 => self.execute_sltu(instr.rs1, instr.rs2, instr.rd),
                    0b100 => self.execute_xor(instr.rs1, instr.rs2, instr.rd),
                    0b110 => self.execute_or(instr.rs1, instr.rs2, instr.rd),
                    0b111 => self.execute_and(instr.rs1, instr.rs2, instr.rd),
                    0b001 => self.execute_sll(instr.rs1, instr.rs2, instr.rd),
                    0b101 => {
                        if instr.funct7 == 0b010_000 {
                            self.execute_sra(instr.rs1, instr.rs2, instr.rd);
                        } else {
                            self.execute_srl(instr.rs1, instr.rs2, instr.rd);
                        }
                    }
                    _ => unreachable!("funct3 should only be 3 bits"),
                }
                self.reg_pc += 4;
            }
            decode::opcode::JAL => {
                let instr: JType = instruction.into();
                if instr.rd == 0 {
                    // Jump
                    self.execute_j(instr.imm);
                } else {
                    self.execute_jal(instr.imm, instr.rd);
                }
                // No PC increment needed
            }
            decode::opcode::JALR => {
                let instr: IType = instruction.into();
                if instr.rd == 0 {
                    self.execute_jr(instr.imm, instr.rs1);
                } else {
                    self.execute_jalr(instr.imm, instr.rs1, instr.rd);
                }
                // No PC increment needed
            }
            decode::opcode::BRANCH => {
                let instr: BType = instruction.into();
                match instr.funct3 {
                    0b000 => self.execute_beq(instr.rs1, instr.rs2, instr.imm),
                    0b001 => self.execute_bne(instr.rs1, instr.rs2, instr.imm),
                    0b100 => self.execute_blt(instr.rs1, instr.rs2, instr.imm),
                    0b110 => self.execute_bltu(instr.rs1, instr.rs2, instr.imm),
                    0b101 => self.execute_bge(instr.rs1, instr.rs2, instr.imm),
                    0b111 => self.execute_bgeu(instr.rs1, instr.rs2, instr.imm),
                    _ => log::error!("Unsupported branch type!"),
                }
                // Unconditionally increment PC. If branch was taken, 4 was subtracted from the PC.
                self.reg_pc += 4;
            }
            decode::opcode::LOAD => {
                let instr: IType = instruction.into();
                match instr.funct3 {
                    0b000 => self.execute_lb(instr.rs1, instr.imm, instr.rd)?,
                    0b100 => self.execute_lbu(instr.rs1, instr.imm, instr.rd)?,
                    0b001 => self.execute_lh(instr.rs1, instr.imm, instr.rd)?,
                    0b101 => self.execute_lhu(instr.rs1, instr.imm, instr.rd)?,
                    0b010 => self.execute_lw(instr.rs1, instr.imm, instr.rd)?,
                    _ => log::error!("Unsupported load width!"),
                }
                self.reg_pc += 4;
            }
            decode::opcode::STORE => {
                let instr: SType = instruction.into();
                match instr.funct3 {
                    0b000 => self.execute_sb(instr.rs1, instr.imm, instr.rs2)?,
                    0b001 => self.execute_sh(instr.rs1, instr.imm, instr.rs2)?,
                    0b010 => self.execute_sw(instr.rs1, instr.imm, instr.rs2)?,
                    _ => log::error!("Unsupported store width!"),
                }
                self.reg_pc += 4;
            }
            _ => {
                if ((instruction & 0b11) != 0b11) || ((instruction & 0b11100) == 0b11100) {
                    log::error!("Non 32 bit instruction encoding not supported!");
                } else {
                    log::error!("Unsupported opcode!")
                }
                // Ignore for now, maybe not smart
                self.reg_pc += 4;
            }
        };

        Ok(())
    }

    /// This function will be called for Integer Computational Instructions
    /// with `rd` = 0.
    /// Note: continue execution after calling this without executing
    /// the underlying integer instruction, to garantee `regs[0]` is
    /// never written to!
    ///
    /// `ADDI x0, x0, 0` is considered the canonical NOP.
    ///
    /// See Section 2.9: Hint instruction
    fn hint(&mut self, instr: u32) {
        if instr == decode::opcode::OP_IMM as u32 {
            // NOP encoded as `ADDI x0, x0, 0`
            return;
        }

        log::warn!("Ignored hint instruction!");
    }

    // Immediate operations
    fn execute_addi(&mut self, src: u8, imm: Ixlen, dest: u8) {
        // FIXME: Overflow/Underflow is ignored by specification, but not by rust?
        self.regs[dest as usize] = self.regs[src as usize] + imm as Uxlen;
    }

    fn execute_slti(&mut self, src: u8, imm: Ixlen, dest: u8) {
        self.regs[dest as usize] = if (self.regs[src as usize] as Ixlen) < imm {
            1
        } else {
            0
        };
    }

    fn execute_sltiu(&mut self, src: u8, imm: Uxlen, dest: u8) {
        self.regs[dest as usize] = if self.regs[src as usize] < imm { 1 } else { 0 };
    }

    fn execute_xori(&mut self, src: u8, imm: Uxlen, dest: u8) {
        self.regs[dest as usize] = self.regs[src as usize] ^ imm;
    }

    fn execute_ori(&mut self, src: u8, imm: Uxlen, dest: u8) {
        self.regs[dest as usize] = self.regs[src as usize] | imm;
    }

    fn execute_andi(&mut self, src: u8, imm: Uxlen, dest: u8) {
        self.regs[dest as usize] = self.regs[src as usize] & imm;
    }

    fn execute_slli(&mut self, src: u8, imm: Uxlen, dest: u8) {
        // FIXME: 64 bit?
        self.regs[dest as usize] = self.regs[src as usize] << (imm & 0b1_1111);
    }

    fn execute_srli(&mut self, src: u8, imm: Uxlen, dest: u8) {
        // FIXME: 64 bit?
        self.regs[dest as usize] = self.regs[src as usize] >> (imm & 0b1_1111);
    }

    fn execute_srai(&mut self, src: u8, imm: Uxlen, dest: u8) {
        // FIXME: 64 bit?
        self.regs[dest as usize] =
            ((self.regs[src as usize] as Ixlen) >> (imm & 0b1_1111)) as Uxlen;
    }

    fn execute_lui(&mut self, imm: Uxlen, dest: u8) {
        self.regs[dest as usize] = imm;
    }

    /// This instruction depends on the PC, it needs to be set to the AUIPC address.
    fn execute_auipc(&mut self, imm: Uxlen, dest: u8) {
        // FIXME: 64 bit?
        self.regs[dest as usize] = self.reg_pc + imm;
    }

    // Register operations
    fn execute_add(&mut self, src1: u8, src2: u8, dest: u8) {
        // FIXME: Overflow/Underflow is ignored by specification, but not by rust?
        self.regs[dest as usize] = self.regs[src1 as usize] + self.regs[src2 as usize];
    }

    fn execute_sub(&mut self, src1: u8, src2: u8, dest: u8) {
        // FIXME: Overflow/Underflow is ignored by specification, but not by rust?
        self.regs[dest as usize] = self.regs[src1 as usize] - self.regs[src2 as usize];
    }

    fn execute_slt(&mut self, src1: u8, src2: u8, dest: u8) {
        let lessthan = (self.regs[src1 as usize] as Ixlen) < (self.regs[src2 as usize] as Ixlen);
        self.regs[dest as usize] = if lessthan { 1 } else { 0 };
    }

    fn execute_sltu(&mut self, src1: u8, src2: u8, dest: u8) {
        let lessthan = self.regs[src1 as usize] < self.regs[src2 as usize];
        self.regs[dest as usize] = if lessthan { 1 } else { 0 };
    }

    fn execute_xor(&mut self, src1: u8, src2: u8, dest: u8) {
        self.regs[dest as usize] = self.regs[src1 as usize] ^ self.regs[src2 as usize];
    }

    fn execute_or(&mut self, src1: u8, src2: u8, dest: u8) {
        self.regs[dest as usize] = self.regs[src1 as usize] | self.regs[src2 as usize];
    }

    fn execute_and(&mut self, src1: u8, src2: u8, dest: u8) {
        self.regs[dest as usize] = self.regs[src1 as usize] & self.regs[src2 as usize];
    }

    fn execute_sll(&mut self, src1: u8, src2: u8, dest: u8) {
        // FIXME: 64 bit?
        self.regs[dest as usize] =
            self.regs[src1 as usize] << (self.regs[src2 as usize] & 0b1_1111);
    }

    fn execute_srl(&mut self, src1: u8, src2: u8, dest: u8) {
        // FIXME: 64 bit?
        self.regs[dest as usize] =
            self.regs[src1 as usize] >> (self.regs[src2 as usize] & 0b1_1111);
    }

    fn execute_sra(&mut self, src1: u8, src2: u8, dest: u8) {
        // FIXME: 64 bit?
        self.regs[dest as usize] =
            ((self.regs[src1 as usize] as Ixlen) >> (self.regs[src2 as usize] & 0b1_1111)) as Uxlen;
    }

    /// FIXME: throw instruction-address-misaligned exception instead of truncting to two parcels.
    /// Spec demands setting lsb to zero, but not bit 1.
    /// Same issue in JR, JAL, JALR & Branch instructions
    fn execute_j(&mut self, offset: Ixlen) {
        self.reg_pc = (self.reg_pc as Ixlen + offset) as Uxlen;
    }

    fn execute_jal(&mut self, offset: Ixlen, dest: u8) {
        self.regs[dest as usize] = self.reg_pc + 4;
        self.reg_pc = (self.reg_pc as Ixlen + offset) as Uxlen;
    }

    /// Maybe non standard terminology
    fn execute_jr(&mut self, offset: Ixlen, base: u8) {
        self.reg_pc = (self.regs[base as usize] as Ixlen + offset) as Uxlen & !0b11;
    }

    fn execute_jalr(&mut self, offset: Ixlen, base: u8, dest: u8) {
        let next = self.reg_pc + 4;
        self.reg_pc = (self.regs[base as usize] as Ixlen + offset) as Uxlen & !0b11;
        // Prevent bug when base = dest
        self.regs[dest as usize] = next;
    }

    // Branches
    // The -4 is not specified behaviour, but negated by unconditional
    // PC increment.
    fn execute_beq(&mut self, src1: u8, src2: u8, offset: Ixlen) {
        if self.regs[src1 as usize] == self.regs[src2 as usize] {
            self.reg_pc = (self.reg_pc as Ixlen + offset - 4) as Uxlen;
        }
    }

    fn execute_bne(&mut self, src1: u8, src2: u8, offset: Ixlen) {
        if self.regs[src1 as usize] != self.regs[src2 as usize] {
            self.reg_pc = (self.reg_pc as Ixlen + offset - 4) as Uxlen;
        }
    }

    fn execute_blt(&mut self, src1: u8, src2: u8, offset: Ixlen) {
        if (self.regs[src1 as usize] as Ixlen) < (self.regs[src2 as usize] as Ixlen) {
            self.reg_pc = (self.reg_pc as Ixlen + offset - 4) as Uxlen;
        }
    }

    fn execute_bltu(&mut self, src1: u8, src2: u8, offset: Ixlen) {
        if (self.regs[src1 as usize] as Uxlen) < (self.regs[src2 as usize] as Uxlen) {
            self.reg_pc = (self.reg_pc as Ixlen + offset - 4) as Uxlen;
        }
    }

    fn execute_bge(&mut self, src1: u8, src2: u8, offset: Ixlen) {
        if (self.regs[src1 as usize] as Ixlen) >= (self.regs[src2 as usize] as Ixlen) {
            self.reg_pc = (self.reg_pc as Ixlen + offset - 4) as Uxlen;
        }
    }

    fn execute_bgeu(&mut self, src1: u8, src2: u8, offset: Ixlen) {
        if (self.regs[src1 as usize] as Uxlen) >= (self.regs[src2 as usize] as Uxlen) {
            self.reg_pc = (self.reg_pc as Ixlen + offset - 4) as Uxlen;
        }
    }

    // Load/Store
    fn execute_lw(&mut self, base: u8, offset: i32, dest: u8) -> Result<(), Exception> {
        let addr = (self.regs[base as usize] as Ixlen + offset) as Uxlen;
        self.regs[dest as usize] = self.address_space.read_word(addr)?;
        Ok(())
    }
    fn execute_lh(&mut self, base: u8, offset: i32, dest: u8) -> Result<(), Exception> {
        let addr = (self.regs[base as usize] as Ixlen + offset) as Uxlen;
        self.regs[dest as usize] = self.address_space.read_halfword(addr)? as i16 as Ixlen as Uxlen;
        Ok(())
    }
    fn execute_lhu(&mut self, base: u8, offset: i32, dest: u8) -> Result<(), Exception> {
        let addr = (self.regs[base as usize] as Ixlen + offset) as Uxlen;
        self.regs[dest as usize] = self.address_space.read_word(addr)?;
        Ok(())
    }
    fn execute_lb(&mut self, base: u8, offset: i32, dest: u8) -> Result<(), Exception> {
        let addr = (self.regs[base as usize] as Ixlen + offset) as Uxlen;
        self.regs[dest as usize] = self.address_space.read_word(addr)? as i8 as Ixlen as Uxlen;
        Ok(())
    }
    fn execute_lbu(&mut self, base: u8, offset: i32, dest: u8) -> Result<(), Exception> {
        let addr = (self.regs[base as usize] as Ixlen + offset) as Uxlen;
        self.regs[dest as usize] = self.address_space.read_word(addr)?;
        Ok(())
    }

    fn execute_sw(&mut self, base: u8, offset: i32, src: u8) -> Result<(), Exception> {
        let addr = (self.regs[base as usize] as Ixlen + offset) as Uxlen;
        todo!()
    }

    fn execute_sh(&mut self, base: u8, offset: i32, src: u8) -> Result<(), Exception> {
        let addr = (self.regs[base as usize] as Ixlen + offset) as Uxlen;
        todo!()
    }

    fn execute_sb(&mut self, base: u8, offset: i32, src: u8) -> Result<(), Exception> {
        let addr = (self.regs[base as usize] as Ixlen + offset) as Uxlen;
        todo!()
    }
}
