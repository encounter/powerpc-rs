mod asm;
mod condition;
mod disasm;
mod isa;

use crate::asm::gen_asm;
use crate::disasm::gen_disasm;
use anyhow::{ensure, Context, Result};
use condition::{parse_conditions, ConditionOp, ConditionValue};
use isa::load_isa;
use std::path::Path;

/// Identifier literal.
#[macro_export]
macro_rules! ident {
    ($name:ident) => {
        proc_macro2::Ident::new(stringify!($name), proc_macro2::Span::call_site())
    };
}

fn main() -> Result<()> {
    simple_logger::SimpleLogger::new().env().init().unwrap();

    let isa = load_isa(Path::new("isa.yaml"))?;
    // Make sure we can fit the opcodes into a u8
    // ensure!(isa.opcodes.len() <= 255);
    log::info!("num opcodes: {}", isa.opcodes.len());

    // Sanity check the opcodes and mnemonics
    // Calculate the bitmask for each opcode and compare it to the stored bitmask
    let mut max_args = 0;
    for opcode in &isa.opcodes {
        let mut calc_bitmask = opcode.mask(&isa);
        if opcode.bitmask != calc_bitmask {
            log::warn!(
                "Opcode {}: Calculated bitmask mismatch: {:#010X} != {:#010X} ({:032b} != {:032b})",
                opcode.name,
                opcode.bitmask,
                calc_bitmask,
                opcode.bitmask,
                calc_bitmask
            );
        }
        if opcode.pattern & !opcode.bitmask != 0 {
            log::warn!(
                "Opcode {}: Pattern has bits set outside of bitmask: {:#010X} & !{:#010X} != 0 ({:032b} & !{:032b} != 0)",
                opcode.name,
                opcode.pattern,
                opcode.bitmask,
                opcode.pattern,
                opcode.bitmask
            );
        }

        // Make sure we can account for every bit with fields and modifiers
        for arg in &opcode.args {
            let field = isa
                .find_field(arg)
                .with_context(|| format!("Opcode {}: unknown field {}", opcode.name, arg))?;
            calc_bitmask |= field.mask();
        }
        for modifier_name in &opcode.modifiers {
            let modifier = isa.find_modifier(modifier_name).with_context(|| {
                format!("Opcode {}: unknown modifier {}", opcode.name, modifier_name)
            })?;
            if let Some(condition) = &modifier.condition {
                for condition in parse_conditions(condition, &isa)? {
                    // Only check constant conditions
                    if condition.op == ConditionOp::Eq
                        && matches!(
                            condition.value,
                            ConditionValue::ConstantUnsigned(_) | ConditionValue::ConstantSigned(_)
                        )
                    {
                        calc_bitmask |= condition.field.shift_value(condition.field_mask);
                    }
                }
            } else {
                calc_bitmask |= modifier.mask();
            }
        }
        if calc_bitmask != u32::MAX {
            log::warn!(
                "Opcode {}: Calculated bitmask is non-exhaustive: {:#010X}, {:032b}",
                opcode.name,
                calc_bitmask,
                calc_bitmask
            );
        }

        max_args = max_args.max(opcode.args.len());
    }

    // Check each mnemonic, make sure we can account for every bit
    // with fields, modifiers, and conditions
    for mnemonic in &isa.mnemonics {
        let opcode = isa.find_opcode(&mnemonic.opcode).with_context(|| {
            format!("Mnemonic {}: unknown opcode {}", mnemonic.name, mnemonic.opcode)
        })?;
        let mut calc_bitmask = opcode.mask(&isa);
        for arg in &mnemonic.args {
            let field = isa
                .find_field(arg)
                .with_context(|| format!("Mnemonic {}: unknown field {}", mnemonic.name, arg))?;
            calc_bitmask |= field.mask();
        }
        for modifier_name in mnemonic.modifiers.as_deref().unwrap_or(&opcode.modifiers) {
            let modifier = isa.find_modifier(modifier_name).with_context(|| {
                format!("Mnemonic {}: unknown modifier {}", mnemonic.name, modifier_name)
            })?;
            if let Some(condition) = &modifier.condition {
                for condition in parse_conditions(condition, &isa)? {
                    // Only check constant conditions
                    if condition.op == ConditionOp::Eq
                        && matches!(
                            condition.value,
                            ConditionValue::ConstantUnsigned(_) | ConditionValue::ConstantSigned(_)
                        )
                    {
                        calc_bitmask |= condition.field.shift_value(condition.field_mask);
                    }
                }
            } else {
                calc_bitmask |= modifier.mask();
            }
        }
        for condition in parse_conditions(&mnemonic.condition, &isa)? {
            if condition.op != ConditionOp::Eq {
                continue;
            }
            let field_bitmask = condition.field.shift_value(condition.field_mask);
            if calc_bitmask & field_bitmask != 0 {
                log::warn!(
                    "Mnmemonic {}: {:#010X} & {:#010X} != 0",
                    mnemonic.name,
                    calc_bitmask,
                    field_bitmask,
                );
            }
            calc_bitmask |= field_bitmask;
        }
        if calc_bitmask != u32::MAX {
            log::warn!(
                "Mnemonic {}: Calculated bitmask is non-exhaustive: {:#010X}, {:032b}",
                mnemonic.name,
                calc_bitmask,
                calc_bitmask
            );
        }
    }

    let tokens = gen_disasm(&isa, max_args)?;
    let file = syn::parse2(tokens)?;
    let formatted = prettyplease::unparse(&file);
    std::fs::write("disasm/src/generated.rs", formatted)?;

    let tokens = gen_asm(&isa, max_args)?;
    let file = syn::parse2(tokens)?;
    let formatted = prettyplease::unparse(&file);
    std::fs::write("asm/src/generated.rs", formatted)?;

    Ok(())
}
