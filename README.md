# powerpc [![Build Status]][actions] [![Latest Version]][crates.io] [![Api Rustdoc]][rustdoc] ![Rust Version]

[Build Status]: https://github.com/encounter/powerpc-rs/actions/workflows/test.yml/badge.svg
[actions]: https://github.com/encounter/powerpc-rs/actions
[Latest Version]: https://img.shields.io/crates/v/powerpc.svg
[crates.io]: https://crates.io/crates/powerpc
[Api Rustdoc]: https://img.shields.io/badge/api-rustdoc-blue.svg
[rustdoc]: https://docs.rs/powerpc
[Rust Version]: https://img.shields.io/badge/rust-1.74+-blue.svg?maxAge=3600

(Previously `ppc750cl`)

Rust disassembler and assembler for the PowerPC ISA.

### Supported Extensions

- PowerPC 64-bit
- Paired Singles 
  - PowerPC 750CXe "Gekko" (Nintendo GameCube) 
  - PowerPC 750CL "Broadway" (Nintendo Wii)
- AltiVec
- VMX128 
  - PowerPC "Xenon" (Xbox 360)

If you need support for other extensions, please open an issue.

## Usage

In Cargo.toml:

```toml
[dependencies]
powerpc = "0.4" # disassembler
powerpc-asm = "0.4" # assembler
```

Disassembling and printing instructions:

```rust
use powerpc::{Argument, Extensions, Ins, Opcode, Simm, GPR};

let ins = Ins::new(0x38A00000, Extensions::none());
assert_eq!(ins.op, Opcode::Addi);

// Basic form
let parsed = ins.basic();
assert_eq!(parsed.args[0], Argument::GPR(GPR(5)));
assert_eq!(parsed.args[1], Argument::GPR(GPR(0)));
assert_eq!(parsed.args[2], Argument::Simm(Simm(0)));
assert_eq!(parsed.to_string(), "addi r5, r0, 0x0");

// Simplified form
let parsed = ins.simplified();
assert_eq!(parsed.to_string(), "li r5, 0x0");
```

Assembling instructions:

```rust
use powerpc_asm::{assemble, Argument, Arguments};

let args: Arguments = [
    Argument::Unsigned(5),
    Argument::Unsigned(0),
    Argument::Signed(0),
    Argument::None,
    Argument::None,
];
let code = assemble("addi", &args).expect("Invalid arguments");
assert_eq!(code, 0x38A00000); // addi r5, r0, 0x0
```

## Building

```
cargo run --package powerpc-genisa
cargo test
```

## isa.yaml

The file [isa.yaml](./isa.yaml) contains a definition of the PowerPC instruction set.

Similarly to LLVM TableGen, the program `powerpc-genisa` generates Rust files implementing core functionality
for the disassembler and assembler.

## Safety & Correctness

- The disassembler has been fuzzed over all ~4.29 billion possible instructions (via `powerpc-fuzz`).
- It is safe to run the disassembler over untrusted byte arrays.
- However, no guarantees on correctness are made (yet). Expect bugs.

## Performance

With a single thread on Ryzen 9 3900X:

- Disassembling & printing: ~12M insn/s (~50 MB/s)
- Disassembling only: ~275M insn/s (~1 GB/s)
