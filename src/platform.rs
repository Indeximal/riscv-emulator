use crate::Uxlen;

use self::exception::{SynchronousCause, TrapCause};

pub mod exception {
    use crate::{Ixlen, Uxlen};
    use num_enum::TryFromPrimitive;

    #[derive(Debug, Clone, Copy)]
    pub enum TrapCause {
        Interrupt(InterruptCause),
        Exception(SynchronousCause),
    }

    // Interrupt bit 0
    #[derive(Debug, Clone, Copy, TryFromPrimitive)]
    #[repr(u32)]
    pub enum SynchronousCause {
        InstructionAddressMisaligned = 0,
        InstructionAccessFault = 1,
        IllegalInstruction = 2,
        Breakpoint = 3,
        LoadAddressMisaligned = 4,
        LoadAccessFault = 5,
        StoreAMOAddressMisaligned = 6,
        StoreAMOAccessFault = 7,
        EnvironmentCallFromUmode = 8,
        EnvironmentCallFromSmode = 9,
        EnvironmentCallFromMmode = 11,
        InstructionPageFault = 12,
        LoadPageFault = 13,
        StoreAMOPageFault = 15,
        /// Custom cause upon reset
        Reset = 24,
        /// Custom cause, when software tries to set the field to an unsupported value.
        Unsupported = 25,
        /// This isn't a Trap!! Its a "reverse-trap" of sorts.
        MachineReturn = 26,
    }

    // Interrupt bit 1
    #[derive(Debug, Clone, Copy, PartialEq, TryFromPrimitive)]
    #[repr(u32)]
    pub enum InterruptCause {
        SupervisorSoftwareInterrupt = 1,
        MachineSoftwareInterrupt = 3,
        SupervisorTimerInterrupt = 5,
        MachineTimerInterrupt = 7,
        SupervisorExternalInterrupt = 9,
        MachineExternalInterrupt = 11,
        /// Custom cause, when software tries to set the field to an unsupported value.
        Unsupported = 16,
    }

    #[derive(Debug, Clone, Copy)]
    pub(crate) enum TrapVector {
        /// Both synchronous and asynchronous traps set the PC to the inner value.
        /// Inner is garanteed 4 aligned. Mode = 0.
        Direct(Uxlen),
        /// Both synchronous traps set the PC to the inner value.
        /// Asynchronous traps set the PC to the inner value + 4 * mcause.
        /// Inner is garanteed 4 aligned. Mode = 1.
        Vectored(Uxlen),
    }

    impl Into<u32> for TrapCause {
        fn into(self) -> u32 {
            match self {
                TrapCause::Interrupt(cause) => (1 << 31) | cause as u32,
                TrapCause::Exception(cause) => cause as u32,
            }
        }
    }

    impl Into<u64> for TrapCause {
        fn into(self) -> u64 {
            match self {
                TrapCause::Interrupt(cause) => (1 << 63) | cause as u64,
                TrapCause::Exception(cause) => cause as u64,
            }
        }
    }

    impl From<Uxlen> for TrapCause {
        /// Cast any value into a supported cause while respecting the interrupt flag.
        fn from(value: Uxlen) -> Self {
            // XLEN independent msb check
            if (value as Ixlen) < 0 {
                TrapCause::Interrupt(
                    InterruptCause::try_from(value & 0xff_ff)
                        .unwrap_or(InterruptCause::Unsupported),
                )
            } else {
                TrapCause::Exception(
                    SynchronousCause::try_from(value).unwrap_or(SynchronousCause::Unsupported),
                )
            }
        }
    }

    impl Into<Uxlen> for TrapVector {
        fn into(self) -> Uxlen {
            match self {
                TrapVector::Direct(base) => base & !0b11,
                TrapVector::Vectored(base) => base & !0b11 + 1,
            }
        }
    }

    impl TryFrom<Uxlen> for TrapVector {
        type Error = ();

        fn try_from(value: Uxlen) -> Result<Self, Self::Error> {
            let base = value & !0b11;
            match value & 0b11 {
                0 => Ok(TrapVector::Direct(base)),
                1 => Ok(TrapVector::Vectored(base)),
                _ => Err(()),
            }
        }
    }

    #[test]
    fn simple_interruptcause_cast() {
        let e = InterruptCause::SupervisorTimerInterrupt;
        assert_eq!(e as crate::Uxlen, 5);

        let cause = 9;
        let ee: InterruptCause = cause.try_into().expect("Cast failed");
        assert_eq!(ee, InterruptCause::SupervisorExternalInterrupt);
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
pub trait AddressSpace {
    fn read_word(&self, addr: Uxlen) -> Result<u32, SynchronousCause>;
    fn read_halfword(&self, addr: Uxlen) -> Result<u16, SynchronousCause>;
    fn read_byte(&self, addr: Uxlen) -> Result<u8, SynchronousCause>;
    fn write_word(&mut self, addr: Uxlen, val: u32) -> Result<(), SynchronousCause>;
    fn write_halfword(&mut self, addr: Uxlen, val: u16) -> Result<(), SynchronousCause>;
    fn write_byte(&mut self, addr: Uxlen, val: u8) -> Result<(), SynchronousCause>;
}

#[derive(Debug, Clone, Copy)]
pub enum PriviledgeMode {
    /// Level 3: 11: Machine (M)
    Machine = 3,
    /// Level 1: 01: Supervisor (S)
    //Supervisor,
    /// Level 0: 00: User (U)
    User = 0,
}

pub struct PlatformState {
    /// Hart Id. Zero in single core system. Keep low, but unique.
    csr_mhartid: Uxlen,
    /// This WARL register is constant in this implementation. 0 if not implemented.
    csr_misa: Uxlen,
    /// In this simulation, the cycle, time and instret counter are all the same value.
    tick_count: u64,

    /// The current priviledge mode
    priviledge: PriviledgeMode,
    /// Machine exception return address. Stores the address of the instrution
    /// that trapped into M mode.
    /// On Read the lower two bits are zero FIXME.
    ///
    /// TODO: Write on taking a trap
    csr_mepc: Uxlen,
    /// Specifies the behaviour of a trap into machine mode.
    csr_mtvec: exception::TrapVector,
    /// Cause of the latest trap into machine mode.
    csr_mcause: TrapCause,
    /// Status registers. Mostly unimplemented, but contains trap stack.
    csr_mstatus: MStatusReg,
    /// Additional Machine mode register.
    csr_mscratch: Uxlen,
}

/// This struct encodes the `mstatus` register.
/// It is incomplete.
pub struct MStatusReg {
    /// Machine global interrupt enable bit. Same level interrupts are enabled when true
    /// and this is encoded as the bit set to 1.
    /// Higher level interrupts are always enabled and lower interrupts always disabled.
    /// bit 3.
    mie: bool,

    /// Previous machine interrupt enable bit. bit 7.
    mpie: bool,

    /// Previous priviledge mode. bits 11 & 12.
    mpp: PriviledgeMode,
    // TODO: UXL! (3.1.6.2)

    // TODO: all the memory protection stuff, but can be read only zero
    // e.g MPRV: Modify priviledge (use `mpp` as effective memory priviledge)

    // Endianness is always little endian. thus encoded as zero.

    // No float, vector or additional state so FS, VS, XS and SD are read only zero.
}

impl MStatusReg {
    fn encode(&self) -> Uxlen {
        ((self.mie as Uxlen) << 3) | ((self.mpie as Uxlen) << 7) | ((self.mpp as Uxlen) << 11)
    }

    fn update(&mut self, val: Uxlen) {
        // FIXME: is ignoring invalid bit writes fine?
        self.mie = val & (1 << 3) != 0;
        self.mpie = val & (1 << 7) != 0;
        self.mpp = match (val >> 11) & 0b11 {
            0b11 => PriviledgeMode::Machine,
            0b00 => PriviledgeMode::User,
            _ => PriviledgeMode::User,
        }
    }
}

impl Default for PlatformState {
    /// The reset state
    fn default() -> Self {
        Self {
            csr_mhartid: 0,
            /// Defines MXLEN and implemented extensions. FIXME: dynamic 64 bit
            csr_misa: (1 << 30) | crate::isa_flags::I | crate::isa_flags::U,
            tick_count: 0,
            // Unspecified after reset
            csr_mepc: 0,
            priviledge: PriviledgeMode::Machine,
            // Unspecified after reset
            csr_mtvec: exception::TrapVector::Direct(0),
            csr_mcause: TrapCause::Exception(SynchronousCause::Reset),
            csr_mstatus: MStatusReg {
                mie: true,
                mpie: true,
                mpp: PriviledgeMode::User,
            },
            csr_mscratch: 0,
        }
    }
}

impl PlatformState {
    /// The lower 12 bits of `addr` encode the CSR specifier.
    /// Section 2.2 of the priviledged Spec
    ///
    /// The result is zero extended to `Uxlen`.
    pub fn read_csr(&mut self, addr: u16) -> Result<Uxlen, SynchronousCause> {
        use PriviledgeMode::*;

        match (self.priviledge, addr) {
            // Performance counter (0xC00..=0xC9F for user, 0xB00..=0xB9F for machine).
            // FIXME: fix permissions with `mcounteren` csr
            // (_, 0xC00) => Ok(self.tick_count as Uxlen), // Cycle
            // (_, 0xC01) => Ok(self.tick_count as Uxlen), // Time
            // (_, 0xC02) => Ok(self.tick_count as Uxlen), // Instruction retired
            // (_, 0xC80) => Ok((self.tick_count >> 32) as Uxlen), // Cycle high
            // (_, 0xC81) => Ok((self.tick_count >> 32) as Uxlen), // Time high
            // (_, 0xC82) => Ok((self.tick_count >> 32) as Uxlen), // Instruction retired high
            // (_, 0xC00..=0xC9F) => Ok(0),                // Other counters
            (Machine, 0xB00) => Ok(self.tick_count as Uxlen), // Cycle
            (Machine, 0xB02) => Ok(self.tick_count as Uxlen), // Instruction retired
            (Machine, 0xB80) => Ok((self.tick_count >> 32) as Uxlen), // Cycle high
            (Machine, 0xB81) => Ok((self.tick_count >> 32) as Uxlen), // Time high
            (Machine, 0xB82) => Ok((self.tick_count >> 32) as Uxlen), // Instruction retired high
            (Machine, 0xB00..=0xB9F) => Ok(0),                // Other counters
            (Machine, 0x323..=0x33F) => Ok(0),                // Event selectors
            (Machine, 0x306) => Ok(0),                        // Counter enable (make available)
            (Machine, 0x320) => Ok(0),                        // Counter inhibit
            // Trap handling
            (Machine, 0x300) => Ok(self.csr_mstatus.encode()), // Machine status register
            (Machine, 0x310) => Ok(0),                         // Machine status register upper
            (Machine, 0x305) => Ok(self.csr_mtvec.into()),     // Machine trap vector
            (Machine, 0x341) => Ok(self.csr_mepc & !0b11), // Machine exception return address (aligned)
            (Machine, 0x342) => Ok(self.csr_mcause.into()), // Machine trap cause
            (Machine, 0x340) => Ok(self.csr_mscratch),     // Machine scratch
            // TODO: Interrupt handling (disabled for now)
            (Machine, 0x304) => Ok(0), // Machine interrupt pending
            (Machine, 0x344) => Ok(0), // Machine interrupt enable
            // Static platform information:
            (Machine, 0x301) => Ok(self.csr_misa), // Machine ISA
            (Machine, 0xF11) => Ok(0),             // Vendor id. Zero since this is not commercial
            (Machine, 0xF12) => Ok(0), // Architecture id. Zero since this is not registered
            (Machine, 0xF13) => Ok(0x13_09_B9_5C), // Implementation id. Randomly chosen
            (Machine, 0xF14) => Ok(self.csr_mhartid), // Hart id
            // Unrecognised or unallowed CSR access
            _ => Err(SynchronousCause::IllegalInstruction),
        }
    }

    /// The lower 12 bits of `addr` encode the CSR specifier.
    pub fn write_csr(&mut self, addr: u16, value: Uxlen) -> Result<(), SynchronousCause> {
        use PriviledgeMode::*;

        match (self.priviledge, addr) {
            // Performance Counters (read only, user & machine & setup)
            (_, 0xC00..=0xC9F) => Err(SynchronousCause::IllegalInstruction),
            (_, 0xB00..=0xB9F) => Err(SynchronousCause::IllegalInstruction),
            (_, 0x323..=0x33F) => Err(SynchronousCause::IllegalInstruction),
            // Trap handling
            (Machine, 0x305) => {
                // Set machine trap vector address, ignore unsupported modes
                if let Ok(trap_vec) = value.try_into() {
                    self.csr_mtvec = trap_vec;
                }
                Ok(())
            }
            (Machine, 0x341) => {
                // Set machine exception return address
                self.csr_mepc = value;
                Ok(())
            }
            (Machine, 0x342) => {
                // Set machine trap cause, maybe set as unsupported
                // FIXME: log when a unsupported cause is set?
                self.csr_mepc = value.into();
                Ok(())
            }
            (Machine, 0x300) => {
                // Machine status register
                self.csr_mstatus.update(value);
                Ok(())
            }

            (Machine, 0x340) => {
                // Machine scratch
                self.csr_mscratch = value;
                Ok(())
            }
            // TODO: Interrupt handling, ignored for now
            (Machine, 0x304) => Ok(()), // Machine interrupt pending
            (Machine, 0x344) => Ok(()), // Machine interrupt enable
            // Static platform information (read only in this implementation)
            (Machine, 0x301) => Ok(()), // Ignore misa write
            (Machine, 0xF11..=0xF14) => Err(SynchronousCause::IllegalInstruction),
            // Unrecognised or unallowed CSR access
            _ => Err(SynchronousCause::IllegalInstruction),
        }
    }

    /// Registers a trap in the platform state.
    /// Returns the intruction address of the trap handler, continue executing there.
    pub fn trap(&mut self, addr: Uxlen, cause: TrapCause) -> Uxlen {
        // FIXME: check specs for things I forgot here??
        // TODO: Supervisor delegate?
        self.csr_mcause = cause;
        self.csr_mepc = addr;

        let previous_priv = self.priviledge;

        // Always trap into machine mode for now
        self.csr_mstatus.mpie = self.csr_mstatus.mie;
        self.csr_mstatus.mie = false;
        self.csr_mstatus.mpp = previous_priv;
        self.priviledge = PriviledgeMode::Machine;

        match self.csr_mtvec {
            exception::TrapVector::Direct(base) => base,
            exception::TrapVector::Vectored(base) => match cause {
                TrapCause::Interrupt(_) => base,
                TrapCause::Exception(ecause) => base + 4 * ecause as Uxlen,
            },
        }
    }

    /// Returns from a (machine) trap.
    /// TODO: SRET
    ///
    /// Returns the intruction address prior to the trap handler, continue executing there.
    ///
    /// *"An MRET or SRET instruction is used to return from a trap in M-mode or S-mode respectively.
    /// When executing an xRET instruction, supposing xPP holds the value y, xIE is set to xPIE; the
    /// privilege mode is changed to y; xPIE is set to 1; and xPP is set to the least-privileged supported
    /// mode (U if U-mode is implemented, else M). If xPP!=M, xRET also sets MPRV=0"*
    pub fn trap_return(&mut self) -> Uxlen {
        self.csr_mstatus.mie = self.csr_mstatus.mpie;
        self.priviledge = self.csr_mstatus.mpp;
        self.csr_mstatus.mpie = true;
        self.csr_mstatus.mpp = PriviledgeMode::User;
        // FIXME: ? MPRV = 0 if mpp wasn't Machine

        self.csr_mepc
    }

    pub fn increment_tick(&mut self) {
        self.tick_count += 1;
    }

    pub fn priviledge(&self) -> PriviledgeMode {
        self.priviledge
    }
}
