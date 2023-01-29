
https://riscv.org/technical/specifications/

# Execution Environment Spec
* ISA: RV32I_Zicsr (currently), Goal is RV64IMAC_Zicsr_Zifenci
* Priviledge modes: Machine mode only (currently), Goal is 3 level: M, S, U.
Maybe add Debug mode aswell
* Address space: phyiscal 16MiB main memory at 0x100_0000 (currently)
Goal is virtual memory (maybe Phyical Memory Protection PMP)
* Num Harts: 1 currently, maybe multiple at some point
* Memory Model: Will always be sequentially consitent (Thus Ztso in particular)


# TODO
* M
* A
* C
* Exceptions
* Tests

# Goal
Support running seL4.
Needs platform support: https://docs.sel4.systems/Hardware/
https://docs.sel4.systems/Hardware/spike.html


