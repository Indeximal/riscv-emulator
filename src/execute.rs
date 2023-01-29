use crate::decode::{get_opcode, opcode, BType, IType, JType, RType, SType, UType};
use crate::platform::exception::{SynchronousCause, TrapCause};
use crate::platform::{AddressSpace, PlatformState};
use crate::{Ixlen, Uxlen};

/// Hardware Thread
pub struct Hart<'a> {
    address_space: AddressSpace<'a>,
    execution_env: PlatformState,

    /// The program counter. I.e. the address (aligned) to the next
    /// instruction to be executed.
    reg_pc: Uxlen,
    /// x0 is always zero
    /// x1 is usually the return address
    /// x2 is usually the stack pointer
    /// # INVARIANT
    /// regs[0] is always zero!
    regs: [Uxlen; 32],
}

type InstrExecResult = Result<(), SynchronousCause>;

impl<'a> Hart<'a> {
    /// Advances the hart until a breakpoint or until `max_instr` dynamic instruction
    /// have been executed.
    pub fn run(&mut self, max_instr: usize) {
        for _ in 0..max_instr {
            if let Err(except) = self.step_instruction() {
                log::info!("Encountered exception {:?}", except);
                self.reg_pc = self
                    .execution_env
                    .trap(self.reg_pc, TrapCause::Exception(except));

                if matches!(except, SynchronousCause::Breakpoint) {
                    return;
                }
            } else {
                self.execution_env.increment_tick();
            }
        }
    }

    /// Fetches, decodes, executes one instruction and increments the PC.
    ///
    /// Backed by `execute_xxx` functions that take the decoded instruction and
    /// apply it to the architectural state. They assume proper decoding,
    /// e.g. the destination register is never 0 for Integer Computation Instructions.
    /// Advancing the PC is done in this function, but some functions might touch
    /// the PC as part of their functionality.
    ///
    /// Returns a [`SynchronousCause`] if the instruction couldn't execute due to
    /// an exception or requested a environment call.
    pub fn step_instruction(&mut self) -> InstrExecResult {
        let instruction = self
            .address_space
            .read_word(self.reg_pc)
            .map_err(|_| SynchronousCause::InstructionAccessFault)?;

        match get_opcode(instruction) {
            opcode::OP_IMM => 'instr_exec: {
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
            opcode::LUI => 'instr_exec: {
                let instr: UType = instruction.into();
                if instr.rd == 0 {
                    self.hint(instruction);
                    break 'instr_exec;
                }
                self.execute_lui(instr.imm, instr.rd);
                self.reg_pc += 4;
            }
            opcode::AUIPC => 'instr_exec: {
                let instr: UType = instruction.into();
                if instr.rd == 0 {
                    self.hint(instruction);
                    break 'instr_exec;
                }
                self.execute_auipc(instr.imm, instr.rd);
                self.reg_pc += 4;
            }
            opcode::OP => 'instr_exec: {
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
            opcode::JAL => {
                let instr: JType = instruction.into();
                if instr.rd == 0 {
                    // Jump
                    self.execute_j(instr.imm);
                } else {
                    self.execute_jal(instr.imm, instr.rd);
                }
                // No PC increment needed
            }
            opcode::JALR => {
                let instr: IType = instruction.into();
                if instr.rd == 0 {
                    self.execute_jr(instr.imm, instr.rs1);
                } else {
                    self.execute_jalr(instr.imm, instr.rs1, instr.rd);
                }
                // No PC increment needed
            }
            opcode::BRANCH => {
                let instr: BType = instruction.into();
                match instr.funct3 {
                    0b000 => self.execute_beq(instr.rs1, instr.rs2, instr.imm),
                    0b001 => self.execute_bne(instr.rs1, instr.rs2, instr.imm),
                    0b100 => self.execute_blt(instr.rs1, instr.rs2, instr.imm),
                    0b110 => self.execute_bltu(instr.rs1, instr.rs2, instr.imm),
                    0b101 => self.execute_bge(instr.rs1, instr.rs2, instr.imm),
                    0b111 => self.execute_bgeu(instr.rs1, instr.rs2, instr.imm),
                    _ => {
                        log::error!("Unsupported branch type!");
                        return Err(SynchronousCause::IllegalInstruction);
                    }
                }
                // Unconditionally increment PC. If branch was taken, 4 was subtracted from the PC.
                self.reg_pc += 4;
            }
            opcode::LOAD => {
                let instr: IType = instruction.into();
                match instr.funct3 {
                    0b000 => self.execute_lb(instr.rs1, instr.imm, instr.rd)?,
                    0b100 => self.execute_lbu(instr.rs1, instr.imm, instr.rd)?,
                    0b001 => self.execute_lh(instr.rs1, instr.imm, instr.rd)?,
                    0b101 => self.execute_lhu(instr.rs1, instr.imm, instr.rd)?,
                    0b010 => self.execute_lw(instr.rs1, instr.imm, instr.rd)?,
                    _ => {
                        log::error!("Unsupported load width!");
                        return Err(SynchronousCause::IllegalInstruction);
                    }
                }
                self.reg_pc += 4;
            }
            opcode::STORE => {
                let instr: SType = instruction.into();
                match instr.funct3 {
                    0b000 => self.execute_sb(instr.rs1, instr.imm, instr.rs2)?,
                    0b001 => self.execute_sh(instr.rs1, instr.imm, instr.rs2)?,
                    0b010 => self.execute_sw(instr.rs1, instr.imm, instr.rs2)?,
                    _ => {
                        log::error!("Unsupported store width!");
                        return Err(SynchronousCause::IllegalInstruction);
                    }
                }
                self.reg_pc += 4;
            }
            opcode::MISC_MEM => {
                let instr: IType = instruction.into();
                match instr.funct3 {
                    0b000 => {} // Ignore FENCE instruction
                    0b001 => {} // Ignore FENCE.I instruction
                    _ => {
                        log::error!("Unsupported misc mem instruction!");
                        return Err(SynchronousCause::IllegalInstruction);
                    }
                }
                self.reg_pc += 4;
            }
            opcode::SYSTEM => {
                let instr: IType = instruction.into();
                // The CSR Address space needs the zero extension
                match instr.funct3 {
                    0b001 => self.execute_csrrw(instr.imm as u16 & 0xfff, instr.rs1, instr.rd)?,
                    0b010 => self.execute_csrrs(instr.imm as u16 & 0xfff, instr.rs1, instr.rd)?,
                    0b011 => self.execute_csrrc(instr.imm as u16 & 0xfff, instr.rs1, instr.rd)?,
                    0b101 => self.execute_csrrwi(instr.imm as u16 & 0xfff, instr.rs1, instr.rd)?,
                    0b110 => self.execute_csrrsi(instr.imm as u16 & 0xfff, instr.rs1, instr.rd)?,
                    0b111 => self.execute_csrrci(instr.imm as u16 & 0xfff, instr.rs1, instr.rd)?,
                    0b000 => return Err(self.execute_system_priv(instr)),
                    _ => {
                        log::error!("Unsupported system function!");
                        return Err(SynchronousCause::IllegalInstruction);
                    }
                }
                self.reg_pc += 4;
            }
            _ => {
                if ((instruction & 0b11) != 0b11) || ((instruction & 0b11100) == 0b11100) {
                    log::error!("Non 32 bit instruction encoding not supported!");
                } else {
                    log::error!("Unsupported opcode!")
                }
                return Err(SynchronousCause::IllegalInstruction);
            }
        };

        Ok(())
    }

    fn execute_system_priv(&mut self, instr: IType) -> SynchronousCause {
        // TODO
        match instr.imm {
            0 => {}               // TODO: ECALL
            1 => {}               // TODO: EBREAK
            0b0001000_00010 => {} // TODO: SRET
            0b0011000_00010 => {} // TODO: MRET
            _ => {
                log::error!("Unsupported system function!");
                return SynchronousCause::IllegalInstruction;
            }
        }

        match self.execution_env.priviledge() {
            crate::platform::PriviledgeMode::Machine => SynchronousCause::EnvironmentCallFromMmode,
            crate::platform::PriviledgeMode::User => SynchronousCause::EnvironmentCallFromUmode,
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
        if instr == opcode::OP_IMM as u32 {
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
    fn execute_lw(&mut self, base: u8, offset: Ixlen, dest: u8) -> InstrExecResult {
        let addr = (self.regs[base as usize] as Ixlen + offset) as Uxlen;
        self.regs[dest as usize] = self.address_space.read_word(addr)?;
        Ok(())
    }
    fn execute_lh(&mut self, base: u8, offset: Ixlen, dest: u8) -> InstrExecResult {
        let addr = (self.regs[base as usize] as Ixlen + offset) as Uxlen;
        // Sign extend output
        self.regs[dest as usize] = self.address_space.read_halfword(addr)? as i16 as Ixlen as Uxlen;
        Ok(())
    }
    fn execute_lhu(&mut self, base: u8, offset: Ixlen, dest: u8) -> InstrExecResult {
        let addr = (self.regs[base as usize] as Ixlen + offset) as Uxlen;
        self.regs[dest as usize] = self.address_space.read_word(addr)?;
        Ok(())
    }
    fn execute_lb(&mut self, base: u8, offset: Ixlen, dest: u8) -> InstrExecResult {
        let addr = (self.regs[base as usize] as Ixlen + offset) as Uxlen;
        self.regs[dest as usize] = self.address_space.read_word(addr)? as i8 as Ixlen as Uxlen;
        Ok(())
    }
    fn execute_lbu(&mut self, base: u8, offset: Ixlen, dest: u8) -> InstrExecResult {
        let addr = (self.regs[base as usize] as Ixlen + offset) as Uxlen;
        self.regs[dest as usize] = self.address_space.read_word(addr)?;
        Ok(())
    }

    fn execute_sw(&mut self, base: u8, offset: Ixlen, src: u8) -> InstrExecResult {
        let addr = (self.regs[base as usize] as Ixlen + offset) as Uxlen;
        self.address_space
            .write_word(addr, self.regs[src as usize] as u32)
    }

    fn execute_sh(&mut self, base: u8, offset: Ixlen, src: u8) -> InstrExecResult {
        let addr = (self.regs[base as usize] as Ixlen + offset) as Uxlen;
        self.address_space
            .write_halfword(addr, self.regs[src as usize] as u16)
    }

    fn execute_sb(&mut self, base: u8, offset: Ixlen, src: u8) -> InstrExecResult {
        let addr = (self.regs[base as usize] as Ixlen + offset) as Uxlen;
        self.address_space
            .write_byte(addr, self.regs[src as usize] as u8)
    }

    // Zicsr: Control Status Register support.
    // FIXME: asure atomicity of those instructions
    /// CSR Read & Write
    fn execute_csrrw(&mut self, addr: u16, src: u8, dest: u8) -> InstrExecResult {
        if dest == 0 {
            // Don't read the CSR if the value is discared
            self.execution_env
                .write_csr(addr, self.regs[dest as usize])?;
        } else {
            let prev = self.execution_env.read_csr(addr)?;
            self.execution_env
                .write_csr(addr, self.regs[src as usize])?;
            self.regs[dest as usize] = prev;
        }
        Ok(())
    }

    /// CSR Read & Set
    fn execute_csrrs(&mut self, addr: u16, src: u8, dest: u8) -> InstrExecResult {
        let prev = self.execution_env.read_csr(addr)?;
        if src != 0 {
            // Don't write the CSR if nothing will change
            self.execution_env
                .write_csr(addr, prev | self.regs[src as usize])?;
        }
        if dest != 0 {
            self.regs[dest as usize] = prev;
        }
        Ok(())
    }

    /// CSR Read & Clear
    fn execute_csrrc(&mut self, addr: u16, src: u8, dest: u8) -> InstrExecResult {
        let prev = self.execution_env.read_csr(addr)?;
        if src != 0 {
            // Don't write the CSR if nothing will change
            self.execution_env
                .write_csr(addr, prev & !self.regs[src as usize])?;
        }
        if dest != 0 {
            self.regs[dest as usize] = prev;
        }
        Ok(())
    }

    // The immediate Variants use the 5 bits that usually encode the source register.
    // This will be zero extended. The decode unit garantees `low_imm` is always < 32.
    /// CSR Read & Write immediate lower 5 bits
    fn execute_csrrwi(&mut self, addr: u16, low_imm: u8, dest: u8) -> InstrExecResult {
        if dest == 0 {
            // Don't read the CSR if the value is discared
            self.execution_env
                .write_csr(addr, self.regs[dest as usize])?;
        } else {
            let prev = self.execution_env.read_csr(addr)?;
            self.execution_env.write_csr(addr, low_imm as Uxlen)?;
            self.regs[dest as usize] = prev;
        }
        Ok(())
    }

    /// CSR Read & Set immediate lower 5 bits
    fn execute_csrrsi(&mut self, addr: u16, low_imm: u8, dest: u8) -> InstrExecResult {
        let prev = self.execution_env.read_csr(addr)?;
        if low_imm != 0 {
            // Don't write the CSR if nothing will change
            self.execution_env
                .write_csr(addr, prev | (low_imm as Uxlen))?;
        }
        if dest != 0 {
            self.regs[dest as usize] = prev;
        }
        Ok(())
    }

    /// CSR Read & Clear immediate lower 5 bits
    fn execute_csrrci(&mut self, addr: u16, low_imm: u8, dest: u8) -> InstrExecResult {
        let prev = self.execution_env.read_csr(addr)?;
        if low_imm != 0 {
            // Don't write the CSR if nothing will change
            self.execution_env
                .write_csr(addr, prev & !(low_imm as Uxlen))?;
        }
        if dest != 0 {
            self.regs[dest as usize] = prev;
        }
        Ok(())
    }
}
