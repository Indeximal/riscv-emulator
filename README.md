
https://riscv.org/technical/specifications/

# Execution Environment Spec
* ISA: RV32I_Zicsr_Zifencei (currently), Goal is RV64IMAC_Zicsr_Zifencei
* Priviledge modes: Machine mode only (currently), Goal is 3 level: M, S, U.
Maybe add Debug mode aswell
* Address space: phyiscal 16MiB main memory at 0x100_0000 (currently)
Goal is virtual memory (maybe Phyical Memory Protection PMP)
* Num Harts: 1 currently, maybe multiple at some point
* Memory Model: Will always be sequentially consitent (Thus Ztso in particular)
* TODO: Reset and NonMaskableInterrupt Vector location

# TODO
* Exceptions
* Ebreak & syscall
* M
* A
* C
* Tests

# Goal
Support running seL4.
Needs platform support: https://docs.sel4.systems/Hardware/
https://docs.sel4.systems/Hardware/spike.html

# Tests
There are some tests here:
https://github.com/riscv-software-src/riscv-tests
that runs on TVMs which I don't find specified.

But there is also a https://riscof.readthedocs.io/en/stable/arch-tests.html
with RISCV-config.

## TVM rv32ui reverse engineering
The program should load to 0x80000000, both in 32 and 64 bit, and start execution there.

### CSRs
- `mhartid` must read 0, else the test stalls.
- `mtvec` must be writable. It is used to skip potentially illegal instructions.
- `satp` is set to zero or skipped if this traps.
- `pmpaddr0` and `pmpcfg0` are set to -1 and 31 respectively or skipped if they trap.
- `mie` must be writable. Set to 0 to disable interrupts.
- `medeleg` and `mideleg` are set to 0 or skipped if they trap.
- `stvec` is maybe set to 0 (Not sure since there seems to be dead code there).
- `mstatus` is set to 0 (probaly to return to the lowest priviledge).
- `mepc` is set to the address of the first test.
Then a `mret` is executed, dropping priviledge and start the testing.

### Trap vector
The trap vector is directly mapped to 0x80000004 after init.
Interupts 8, 9 & 11 (the three ECALL variants) call `write_tohost`.
The rest I don't get. Its seems wrong. Exception get a code 1337.

### Host communication
`write_tohost` writes a word in `gp` to 0x80001000, probably
a memory mapped output.

If the program is run in 64 bit, error code 1 is written.
If at the end of execution, `gp` is zero, the program stalls.
Else it returns 1 on success or 2*TestcaseNumber + 1 on failure.
Plus is tests some registers.


## GNU Toolchain installation
for https://github.com/riscv-collab/riscv-gnu-toolchain
I apt installed the following:

```
autoconf/jammy,jammy 2.71-2 all
automake/jammy,jammy 1:1.16.5-1.3 all
autotools-dev/jammy,jammy 20220109.1 all
bison/jammy 2:3.8.2+dfsg-1build1 amd64
build-essential/jammy 12.9ubuntu3 amd64
flex/jammy 2.6.4-8build2 amd64
gawk/jammy 1:5.1.0-1build3 amd64
gperf/jammy 3.1-1build1 amd64
libgmp-dev/jammy 2:6.2.1+dfsg-3ubuntu1 amd64
libmpc-dev/jammy 1.2.1-2build1 amd64
libmpfr-dev/jammy 4.1.0-3build3 amd64
libtool/jammy,jammy 2.4.6-15build2 all
ninja-build/jammy 1.10.1-1 amd64
patchutils/jammy 0.4.2-1build2 amd64
texinfo/jammy 6.8-4build1 amd64
zlib1g-dev/jammy-updates,jammy-security 1:1.2.11.dfsg-2ubuntu9.2 amd64

The following additional packages will be installed:
  dpkg-dev fakeroot libalgorithm-diff-perl libalgorithm-diff-xs-perl libalgorithm-merge-perl
  libfakeroot libfl-dev libfl2 libgmpxx4ldbl libltdl-dev libsigsegv2 libtext-unidecode-perl
  libxml-libxml-perl libxml-namespacesupport-perl libxml-sax-base-perl libxml-sax-expat-perl
  libxml-sax-perl lto-disabled-list m4 tex-common
Suggested packages:
  autoconf-archive gnu-standards autoconf-doc gettext bison-doc debian-keyring flex-doc
  gawk-doc gmp-doc libgmp10-doc libtool-doc libmpfr-doc gfortran | fortran95-compiler gcj-jdk
  libxml-sax-expatxs-perl m4-doc debhelper texlive-base texlive-latex-base
  texlive-plain-generic texlive-fonts-recommended
The following NEW packages will be installed:
  autoconf automake autotools-dev bison build-essential dpkg-dev fakeroot flex gawk gperf
  libalgorithm-diff-perl libalgorithm-diff-xs-perl libalgorithm-merge-perl libfakeroot
  libfl-dev libfl2 libgmp-dev libgmpxx4ldbl libltdl-dev libmpc-dev libmpfr-dev libsigsegv2
  libtext-unidecode-perl libtool libxml-libxml-perl libxml-namespacesupport-perl
  libxml-sax-base-perl libxml-sax-expat-perl libxml-sax-perl lto-disabled-list m4 ninja-build
  patchutils tex-common texinfo zlib1g-dev
0 upgraded, 36 newly installed, 0 to remove and 7 not upgraded.
```



