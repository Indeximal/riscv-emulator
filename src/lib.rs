//! https://riscv.org/technical/specifications/
//!
//! # TODO
//! * Exceptions
//! * Tests
//!

use decode::{BType, IType, JType, RType, UType};

pub type Uxlen = u32;
pub type Ixlen = i32;

mod decode;

/// 64 bit byte addressable circular address space.
///
/// Portions might be either vacant, main memory or i/o devices.
/// Inaccessable accesses cause an exception.
///
/// Defines byte (1B), halfword(2B), word(4B) or quadword(8B)
pub struct AddressSpace;

/// Hardware Thread
///
pub struct Hart {
    address_space: AddressSpace,

    reg_pc: Uxlen,
    /// x0 is always zero
    /// x1 is usually the return address
    /// x2 is usually the stack pointer
    /// # INVARIANT
    /// regs[0] is always zero!
    regs: [Uxlen; 32],
}

impl AddressSpace {
    pub fn read_implicit_word(&self, _addr: Uxlen) -> u32 {
        0
    }
}

impl Hart {
    /// Fetches, decodes, executes one instruction and increments the PC.
    ///
    /// Backed by `execute_xxx` functions that take the decoded instruction and
    /// apply it to the architectural state. They assume proper decoding,
    /// e.g. the destination register is never 0!
    /// Advancing the PC is done in this function, but some functions might touch
    /// the PC as part of their functionality.
    ///  
    pub fn execute_instruction(&mut self) {
        let instruction = self.address_space.read_implicit_word(self.reg_pc);

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
            _ => {
                if ((instruction & 0b11) != 0b11) || ((instruction & 0b11100) == 0b11100) {
                    log::error!("Non 32 bit instruction encoding not supported!");
                } else {
                    log::error!("Unsupported opcode!")
                }
                // Ignore for now, maybe not smart
                self.reg_pc += 4;
            }
        }
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
}
