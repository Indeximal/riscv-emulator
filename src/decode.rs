//! TODO: 2.3 (p16): S, B, U, J type

#![allow(dead_code)]

use crate::Uxlen;

pub(crate) struct RType {
    pub opcode: u8,
    pub funct3: u8,
    pub funct7: u8,
    pub rs1: u8,
    pub rs2: u8,
    pub rd: u8,
}

impl From<u32> for RType {
    fn from(instr: u32) -> RType {
        RType {
            opcode: (instr & 0b111_1111) as u8,
            funct3: ((instr >> 12) & 0b111) as u8,
            funct7: ((instr >> 25) & 0b111_1111) as u8,
            rs1: ((instr >> 15) & 0b1_1111) as u8,
            rs2: ((instr >> 20) & 0b1_1111) as u8,
            rd: ((instr >> 7) & 0b1_1111) as u8,
        }
    }
}

pub(crate) struct IType {
    pub opcode: u8,
    pub funct3: u8,
    pub rs1: u8,
    pub rd: u8,
    // TODO: 64 bit ??
    pub imm: Uxlen,
}

impl From<u32> for IType {
    fn from(instr: u32) -> IType {
        IType {
            opcode: (instr & 0b111_1111) as u8,
            funct3: ((instr >> 12) & 0b111) as u8,
            rs1: ((instr >> 15) & 0b1_1111) as u8,
            rd: ((instr >> 7) & 0b1_1111) as u8,
            // Shifting as i32 garantees sign extension
            imm: (instr as i32 >> 20) as u32,
        }
    }
}

pub(crate) struct UType {
    pub opcode: u8,
    pub rd: u8,
    pub imm: Uxlen,
}

impl From<u32> for UType {
    fn from(instr: u32) -> UType {
        UType {
            opcode: (instr & 0b111_1111) as u8,
            rd: ((instr >> 7) & 0b1_1111) as u8,
            imm: instr & 0xff_ff_f0_00,
        }
    }
}

// From Chapter 24
pub mod opcode {
    pub const LOAD: u8 = 0b00_000_11;
    pub const LOAD_FP: u8 = 0b00_001_11;
    pub const CUSTOM_0: u8 = 0b00_010_11;
    pub const MISC_MEM: u8 = 0b00_011_11;
    pub const OP_IMM: u8 = 0b00_100_11;
    pub const AUIPC: u8 = 0b00_101_11;
    pub const OP_IMM_32: u8 = 0b00_110_11;

    pub const STORE: u8 = 0b01_000_11;
    pub const STORE_FP: u8 = 0b01_001_11;
    pub const CUSTOM_1: u8 = 0b01_010_11;
    pub const AMO: u8 = 0b01_011_11;
    pub const OP: u8 = 0b01_100_11;
    pub const LUI: u8 = 0b01_101_11;
    pub const OP_32: u8 = 0b01_110_11;

    pub const MADD: u8 = 0b10_000_11;
    pub const MSUB: u8 = 0b10_001_11;
    pub const NMSUB: u8 = 0b10_010_11;
    pub const NMADD: u8 = 0b10_011_11;
    pub const OP_FP: u8 = 0b10_100_11;
    pub const RESERVED_0: u8 = 0b10_101_11;
    pub const CUSTOM_2: u8 = 0b10_110_11;

    pub const BRANCH: u8 = 0b11_000_11;
    pub const JALR: u8 = 0b11_001_11;
    pub const RESERVED_1: u8 = 0b11_010_11;
    pub const JAL: u8 = 0b11_011_11;
    pub const SYSTEM: u8 = 0b11_100_11;
    pub const RESERVED_2: u8 = 0b11_101_11;
    pub const CUSTOM_3: u8 = 0b11_110_11;
}

pub fn get_opcode(instr: u32) -> u8 {
    (instr & 0b111_1111) as u8
}
