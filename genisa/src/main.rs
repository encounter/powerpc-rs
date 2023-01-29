#![feature(iterator_try_collect)]

mod asm;

use std::collections::HashMap;
use std::fs::File;
use std::io::Write;
use std::ops::Range;
use std::process::{Command, Stdio};
use std::str::FromStr;

use itertools::Itertools;
use proc_macro2::{Group, Ident, Literal, Span, TokenStream, TokenTree};
use quote::quote;
use serde::{Deserialize, Deserializer};
use syn::{LitChar, LitInt, LitStr};
use crate::asm::asm_main;

macro_rules! token_stream {
    ($stream:ident) => {
        TokenStream::from_iter($stream.into_iter())
    };
}

fn main() {
    if let Err(err) = _main() {
        eprintln!("{}", err);
        std::process::exit(1);
    }
    // if let Err(err) = asm_main() {
    //     eprintln!("{}", err);
    //     std::process::exit(1);
    // }
}

type Error = Box<dyn std::error::Error>;
type Result<T> = std::result::Result<T, Error>;

fn _main() -> Result<()> {
    let isa = load_isa()?;

    let mut unformatted_code = Vec::<u8>::new();
    writeln!(
        &mut unformatted_code,
        "{}",
        quote! {
            use crate::prelude::*;
        }
    )?;
    writeln!(&mut unformatted_code, "{}", isa.gen_opcode_enum()?)?;
    writeln!(&mut unformatted_code, "{}", isa.gen_field_enum()?)?;
    writeln!(&mut unformatted_code, "{}", isa.gen_field_impl()?)?;
    writeln!(&mut unformatted_code, "{}", isa.gen_ins_impl()?)?;

    let formatted_code = rustfmt(unformatted_code);
    File::create("./disasm/src/generated.rs")?.write_all(&formatted_code)?;

    Ok(())
}

fn rustfmt(code: Vec<u8>) -> Vec<u8> {
    let mut rustfmt = Command::new("rustfmt")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .expect("failed to spawn rustfmt");

    let mut stdin = rustfmt.stdin.take().unwrap();
    std::thread::spawn(move || {
        let _ = stdin.write_all(&code);
    });

    let rustfmt_res = rustfmt.wait_with_output().expect("failed to run rustfmt");
    if !rustfmt_res.status.success() {
        panic!("rustfmt failed");
    }

    rustfmt_res.stdout
}

#[derive(Default)]
pub(crate) struct BitRange(Range<u8>);

impl<'de> Deserialize<'de> for BitRange {
    fn deserialize<D>(deserializer: D) -> std::result::Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let range_str: String = Deserialize::deserialize(deserializer)?;
        if let Some((start_str, stop_str)) = range_str.split_once("..") {
            let start = start_str.parse::<u8>().map_err(serde::de::Error::custom)?;
            let stop = stop_str.parse::<u8>().map_err(serde::de::Error::custom)?;
            Ok(Self(start..stop))
        } else {
            let bit_idx = range_str.parse::<u8>().map_err(serde::de::Error::custom)?;
            Ok(Self(bit_idx..bit_idx))
        }
    }
}

#[derive(Deserialize, Default)]
#[serde(default)]
pub(crate) struct Field {
    name: String,
    desc: String,
    bits: BitRange,
    signed: bool,
    split: bool,
    arg: Option<String>,
    shift_left: u8,
}

impl Field {
    fn variant_identifier(&self) -> Option<TokenTree> {
        self.identifier("")
    }

    fn identifier(&self, prefix: &str) -> Option<TokenTree> {
        if self.name.strip_suffix(".nz").is_none() {
            Some(to_rust_ident(prefix, &self.name))
        } else {
            None
        }
    }

    fn express_value(&self, code: TokenStream) -> TokenStream {
        let mut val = quote!(#code);

        let shift = 32 - self.bits.0.end;
        if shift > 0 {
            val = quote!((#val >> #shift));
        }

        let mask = (1u32 << self.bits.0.len()) - 1;
        if mask != 0xFFFF_FFFF {
            let mask = LitInt::new(&format!("0x{:x}", mask), Span::call_site());
            val = quote!((#val & #mask));
        }

        if self.split {
            val = quote!((((#val & 0b11111_00000u32) >> 5u32) | ((#val & 0b00000_11111u32) << 5u32)) as u32);
        }

        // https://graphics.stanford.edu/~seander/bithacks.html#VariableSignExtend
        if self.signed {
            let mask2 = 1u32 << (self.bits.0.len() - 1);
            let mask2 = LitInt::new(&format!("0x{:x}", mask2), Span::call_site());
            val = quote!((((#val ^ #mask2).wrapping_sub(#mask2)) as i32))
        }

        let val_shift = self.shift_left;
        if val_shift > 0 {
            val = quote!((#val << #val_shift));
        }

        val
    }

    fn express_value_self(&self) -> TokenStream {
        self.express_value(quote!(self.code))
    }

    fn enum_variant_definition(&self) -> Option<TokenStream> {
        let ident = self.variant_identifier()?;
        Some(if let Some(arg) = &self.arg {
            let arg = TokenTree::Ident(Ident::new(arg, Span::call_site()));
            quote! {
                #ident(#arg),
            }
        } else {
            quote! {
                #ident,
            }
        })
    }

    pub(crate) fn construct_variant(&self, code: TokenStream) -> TokenStream {
        let field_variant = self.variant_identifier();
        if let Some(arg) = &self.arg {
            let field_arg = TokenTree::Ident(Ident::new(arg, Span::call_site()));
            let value = self.express_value(code);
            quote! {
                Field::#field_variant(#field_arg(#value as _))
            }
        } else {
            quote! {
                Field::#field_variant
            }
        }
    }

    fn construct_variant_self(&self) -> TokenStream {
        self.construct_variant(quote!(self.code))
    }

    fn construct_accessor(&self) -> TokenStream {
        let field_variant = match self.identifier("field_") {
            Some(v) => v,
            None => return TokenStream::new(),
        };
        if self.arg.is_none() {
            return TokenStream::new();
        }
        let value = self.express_value_self();
        let ret_type = if self.signed {
            quote!(isize)
        } else {
            quote!(usize)
        };
        quote! {
            #[inline(always)]
            pub fn #field_variant(&self) -> #ret_type {
                #value as _
            }
        }
    }
}

#[derive(Deserialize, Default)]
#[serde(default)]
pub(crate) struct Opcode {
    name: String,
    desc: String,
    bitmask: u32,
    pattern: u32,
    modifiers: Vec<String>,
    side_effects: Vec<String>,
    args: Vec<String>,
    defs: Vec<String>,
    uses: Vec<String>,
}

impl Opcode {
    fn variant_identifier(&self) -> Result<TokenTree> {
        to_rust_variant(&self.name)
    }
}

#[derive(Deserialize, Default)]
#[serde(default)]
pub(crate) struct Mnemonic {
    name: String,
    opcode: String,
    // Overrides modifier list from opcode
    modifiers: Option<Vec<String>>,
    args: Vec<String>,
    condition: String,
}

#[derive(Deserialize, Default, Clone)]
#[serde(default)]
pub(crate) struct Modifier {
    name: String,
    suffix: char,
    bit: u8,
    condition: String,
}

impl Modifier {
    fn express_value_self(&self, field_by_name: &HashMap<String, &Field>) -> Result<TokenStream> {
        if self.condition.is_empty() {
            let modifier_bit = self.bit as usize;
            Ok(quote!(self.bit(#modifier_bit)))
        } else {
            compile_mnemonic_condition(field_by_name, &self.condition)
        }
    }

    fn construct_accessor(&self, field_by_name: &HashMap<String, &Field>) -> Result<TokenStream> {
        let field_variant = to_rust_ident("field_", &self.name);
        let value = self.express_value_self(field_by_name)?;
        Ok(quote! {
            #[inline(always)]
            pub fn #field_variant(&self) -> bool {
                #value
            }
        })
    }
}

#[derive(Deserialize, Default)]
#[serde(default)]
pub(crate) struct Isa {
    fields: Vec<Field>,
    modifiers: Vec<Modifier>,
    opcodes: Vec<Opcode>,
    mnemonics: Vec<Mnemonic>,
}

fn load_isa() -> Result<Isa> {
    let yaml_file = File::open("isa.yaml")?;
    let isa: Isa = serde_yaml::from_reader(yaml_file)?;
    Ok(isa)
}

impl Isa {
    fn gen_opcode_enum(&self) -> Result<TokenStream> {
        // Create enum variants.
        let enum_variants = self
            .opcodes
            .iter()
            .map(|opcode| -> Result<TokenStream> {
                let ident = opcode.variant_identifier()?;
                Ok(quote! {
                    #ident,
                })
            })
            .try_collect::<TokenStream, Vec<TokenStream>, Error>()?;
        let enum_variants = token_stream!(enum_variants);

        // Create functions.
        let mnemonic_fn = self.gen_mnemonic_fn()?;
        let detect_fn = self.gen_opcode_detect()?;

        // Create final enum.
        let opcode_enum = quote! {
            #[derive(Debug, Copy, Clone, Eq, PartialEq)]
            pub enum Opcode {
                Illegal = -1,
                #enum_variants
            }
            #[allow(clippy::all)]
            impl Opcode {
                #mnemonic_fn
                #detect_fn
            }
        };
        Ok(opcode_enum)
    }

    fn gen_mnemonic_fn(&self) -> Result<TokenStream> {
        // Create match arms.
        let match_arms = self
            .opcodes
            .iter()
            .map(|opcode| {
                let variant = opcode.variant_identifier()?;
                let literal = Literal::string(&opcode.name);
                Ok(quote! {
                    Opcode::#variant => #literal,
                })
            })
            .try_collect::<TokenStream, Vec<TokenStream>, Error>()?;
        let match_arms = token_stream!(match_arms);
        // Create final function.
        let mnemonic_fn = quote! {
            pub(crate) fn _mnemonic(self) -> &'static str {
                match self {
                    Opcode::Illegal => "<illegal>",
                    #match_arms
                }
            }
        };
        Ok(mnemonic_fn)
    }

    fn gen_opcode_detect(&self) -> Result<TokenStream> {
        // Generate if chain.
        let if_chain = self
            .opcodes
            .iter()
            .map(|opcode| {
                let bitmask_str = format!("{:>#8x}", opcode.bitmask);
                let bitmask = LitInt::new(&bitmask_str, Span::call_site());
                let pattern_str = format!("{:>#8x}", opcode.pattern);
                let pattern = LitInt::new(&pattern_str, Span::call_site());
                let identifier = opcode.variant_identifier()?;
                Ok(quote! {
                    if code & #bitmask == #pattern {
                        return Opcode::#identifier;
                    }
                })
            })
            .try_collect::<TokenStream, Vec<TokenStream>, Error>()?;
        let if_chain = token_stream!(if_chain);
        // Generate function.
        let func = quote! {
            pub(crate) fn _detect(code: u32) -> Self {
                #if_chain
                Opcode::Illegal
            }
        };
        Ok(func)
    }

    fn gen_field_enum(&self) -> Result<TokenStream> {
        // Create enum variants.
        let mut enum_variants = Vec::new();
        for field in &self.fields {
            if let Some(field) = field.enum_variant_definition() {
                enum_variants.push(field);
            }
        }
        let enum_variants = token_stream!(enum_variants);

        // Create final enum.
        let field_enum = quote! {
            #[allow(non_camel_case_types)]
            #[derive(Debug, Copy, Clone, Eq, PartialEq)]
            pub enum Field {
                #enum_variants
            }
        };
        Ok(field_enum)
    }

    fn gen_field_argument(&self) -> Result<TokenStream> {
        let mut match_arms = Vec::new();
        for field in &self.fields {
            if let Some(variant) = field.variant_identifier() {
                if let Some(arg_str) = field.arg.as_ref() {
                    let arg = Ident::new(arg_str, Span::call_site());
                    match_arms.push(quote! { Field::#variant(x) => Some(Argument::#arg(*x)), });
                }
            }
        }
        let match_arms = token_stream!(match_arms);
        Ok(quote! {
            pub fn argument(&self) -> Option<Argument> {
                match self {
                    #match_arms
                    _ => None,
                }
            }
        })
    }

    fn gen_field_name(&self) -> Result<TokenStream> {
        let mut match_arms = Vec::new();
        for field in &self.fields {
            if let Some(variant) = field.variant_identifier() {
                let name = LitStr::new(&variant.to_string(), Span::call_site());
                let arg = field.arg.as_ref().map(|_| quote!((_)));
                match_arms.push(quote! { Field::#variant #arg => #name, });
            }
        }
        let match_arms = token_stream!(match_arms);
        Ok(quote! {
            pub fn name(&self) -> &'static str {
                match self {
                    #match_arms
                }
            }
        })
    }

    fn gen_field_impl(&self) -> Result<TokenStream> {
        let field_argument = self.gen_field_argument()?;
        let field_name = self.gen_field_name()?;
        Ok(quote! {
            impl Field {
                #field_argument
                #field_name
            }
        })
    }

    fn gen_ins_impl(&self) -> Result<TokenStream> {
        // Map fields by name.
        let mut field_by_name = HashMap::<String, &Field>::new();
        for field in &self.fields {
            field_by_name.insert(field.name.clone(), field);
        }
        let mut modifier_by_name = HashMap::<String, &Modifier>::new();
        for modifier in &self.modifiers {
            modifier_by_name.insert(modifier.name.clone(), modifier);
        }
        // Map mnemonics by opcode.
        let mut mnemonics_by_opcode = HashMap::<&String, Vec<&Mnemonic>>::new();
        for simple in &self.mnemonics {
            mnemonics_by_opcode
                .entry(&simple.opcode)
                .or_insert_with(Vec::new)
                .push(simple)
        }
        // Generate match arms for each opcode.
        let mut field_match_arms = Vec::new();
        let mut def_match_arms = Vec::new();
        let mut use_match_arms = Vec::new();
        let mut suffix_match_arms = Vec::new();
        let mut simplified_ins_match_arms = Vec::new();
        for opcode in &self.opcodes {
            // Generate fields of opcode.
            let mut fields = Vec::new();
            for arg in &opcode.args {
                let field: &Field = field_by_name
                    .get(arg)
                    .ok_or_else(|| Error::from(format!("undefined field {}", arg)))?;
                let variant = field.construct_variant_self();
                fields.extend(quote! { #variant, })
            }
            let fields = token_stream!(fields);
            // Emit match arm.
            let ident = opcode.variant_identifier()?;
            field_match_arms.push(quote! {
                Opcode::#ident => vec![#fields],
            });

            // Generate modifiers.
            let suffix = express_suffix(&modifier_by_name, &field_by_name, &opcode.modifiers)?;
            suffix_match_arms.push(quote! {
                Opcode::#ident => #suffix,
            });

            // Generate defs.
            let mut defs = Vec::new();
            for arg in &opcode.defs {
                let field: &Field = field_by_name.get(arg).ok_or_else(|| {
                    syn::Error::new(Span::call_site(), format!("undefined field {}", arg))
                })?;
                let variant = field.construct_variant_self();
                defs.extend(quote! { #variant, })
            }
            let defs = token_stream!(defs);
            let ident = opcode.variant_identifier()?;
            def_match_arms.push(quote! {
                Opcode::#ident => vec![#defs],
            });

            // Generate uses.
            let mut uses = Vec::new();
            let mut special_uses = Vec::new();
            for arg in &opcode.uses {
                // Detect non-zero modifier.
                let mut arg = arg.as_str();
                let mut non_zero = false;
                if let Some(substr) = arg.strip_suffix(".nz") {
                    non_zero = true;
                    arg = substr;
                }
                // Get underlying field.
                let field: &Field = field_by_name.get(arg).ok_or_else(|| {
                    syn::Error::new(Span::call_site(), format!("undefined field {}", arg))
                })?;
                let variant = field.construct_variant_self();
                if non_zero {
                    let value = field.express_value_self();
                    special_uses.extend(quote! {
                        if (#value) != 0 {
                            uses.push(#variant);
                        }
                    })
                } else {
                    uses.extend(quote! {
                        #variant,
                    })
                }
            }
            let uses = token_stream!(uses);
            let ident = opcode.variant_identifier()?;
            let special_uses = token_stream!(special_uses);
            use_match_arms.push(quote! {
                Opcode::#ident => {
                    let mut uses = vec![#uses];
                    #special_uses
                    uses
                },
            });

            // Generate instruction simplification.
            if let Some(mnemonics) = mnemonics_by_opcode.get(&opcode.name) {
                let mut simplified_conditions = Vec::new();
                for mnemonic in mnemonics {
                    if mnemonic.condition.is_empty() {
                        continue; // TODO else branch
                    }
                    simplified_conditions.push(quote!(if));
                    simplified_conditions.push(compile_mnemonic_condition(
                        &field_by_name,
                        &mnemonic.condition,
                    )?);
                    // Emit branch.
                    let mnemonic_lit = LitStr::new(&mnemonic.name, Span::call_site());
                    // Emit suffix.
                    let modifiers = mnemonic.modifiers.as_ref().unwrap_or(&opcode.modifiers);
                    let suffix = express_suffix(&modifier_by_name, &field_by_name, modifiers)?;
                    // Extract arguments.
                    let mut args = Vec::new();
                    for arg in &mnemonic.args {
                        let (field_name, expression) = arg.split_once('=').unwrap_or((arg, arg));
                        let field = field_by_name
                            .get(field_name)
                            .unwrap_or_else(|| panic!("field not found: {}", arg));
                        let variant = Ident::new(field.arg.as_ref().unwrap(), Span::call_site());
                        let value = compile_mnemonic_condition(&field_by_name, expression)?;
                        args.push(quote!(Argument::#variant(#variant((#value) as _)),));
                    }
                    let args = token_stream!(args);
                    simplified_conditions.push(quote! {
                        {
                            return SimplifiedIns {
                                mnemonic: #mnemonic_lit,
                                suffix: #suffix,
                                args: vec![#args],
                                ins: self,
                            };
                        }
                    });
                }
                let simplified_conditions = token_stream!(simplified_conditions);
                simplified_ins_match_arms.push(quote! {
                    Opcode::#ident => {
                        #simplified_conditions
                    },
                });
            }
        }
        let field_match_arms = token_stream!(field_match_arms);
        let def_match_arms = token_stream!(def_match_arms);
        let use_match_arms = token_stream!(use_match_arms);
        let suffix_match_arms = token_stream!(suffix_match_arms);
        let simplified_ins_match_arms = token_stream!(simplified_ins_match_arms);
        let field_accessors =
            TokenStream::from_iter(self.fields.iter().map(|field| field.construct_accessor()));
        let modifiers: Vec<TokenStream> = self
            .modifiers
            .iter()
            .map(|modifier| modifier.construct_accessor(&field_by_name))
            .try_collect()?;
        let modifier_accessors = TokenStream::from_iter(modifiers);
        // Generate final fields function.
        let ins_impl = quote! {
            #[allow(clippy::all, unused_mut)]
            impl Ins {
                pub(crate) fn _fields(&self) -> Vec<Field> {
                    match self.op {
                        Opcode::Illegal => vec![],
                        #field_match_arms
                    }
                }

                pub(crate) fn _defs(&self) -> Vec<Field> {
                    match self.op {
                        Opcode::Illegal => vec![],
                        #def_match_arms
                    }
                }

                pub(crate) fn _uses(&self) -> Vec<Field> {
                    match self.op {
                        Opcode::Illegal => vec![],
                        #use_match_arms
                    }
                }

                pub(crate) fn _suffix(&self) -> String {
                    match self.op {
                        Opcode::Illegal => String::new(),
                        #suffix_match_arms
                    }
                }

                pub(crate) fn _simplified(self) -> SimplifiedIns {
                    match self.op {
                        #simplified_ins_match_arms
                        _ => {}
                    }
                    SimplifiedIns::basic_form(self)
                }
            }
            #[allow(clippy::all, non_snake_case)]
            impl Ins {
                #field_accessors
                #modifier_accessors
            }
        };
        Ok(ins_impl)
    }
}

/// Converts the given key into an identifier.
pub(crate) fn to_rust_ident(prefix: &str, key: &str) -> TokenTree {
    TokenTree::Ident(Ident::new(
        &(prefix.to_owned() + &key.replace('.', "_")),
        Span::call_site(),
    ))
}

/// Converts the given key into an enum variant key.
pub(crate) fn to_rust_variant(key: &str) -> Result<TokenTree> {
    Ok(TokenTree::Ident(Ident::new(
        &to_rust_variant_str(key)?,
        Span::call_site(),
    )))
}

fn to_rust_variant_str(key: &str) -> Result<String> {
    let mut s = String::new();
    let mut chars = key.chars();
    loop {
        // Make first char uppercase.
        let c = match chars.next() {
            None => return Ok(s),
            Some(c) => c,
        };
        s.push(match c {
            'a'..='z' => c.to_ascii_uppercase(),
            'A'..='Z' => c,
            _ => return Err(format!("invalid identifier: {}", key).into()),
        });
        loop {
            let c = match chars.next() {
                None => return Ok(s),
                Some(c) => c,
            };
            match c.to_ascii_lowercase() {
                '0'..='9' | 'a'..='z' => s.push(c),
                '_' => break,
                '.' => {
                    s.push('_');
                    break;
                }
                _ => return Err(format!("invalid character in opcode name: {}", key).into()),
            }
        }
    }
}

/// Compiles conditions such as `S == B` into valid Rust expressions on a PowerPC instruction.
fn compile_mnemonic_condition(
    field_by_name: &HashMap<String, &Field>,
    code: &str,
) -> Result<TokenStream> {
    let src_stream = TokenStream::from_str(code)?;
    fn map_ident(field_by_name: &HashMap<String, &Field>, token: TokenTree) -> TokenStream {
        match token {
            TokenTree::Ident(ref ident) => {
                if let Some(field) = field_by_name.get(&ident.to_string()) {
                    return field.express_value_self();
                }
            }
            TokenTree::Group(ref group) => {
                let iter = group
                    .stream()
                    .into_iter()
                    .flat_map(|token| map_ident(field_by_name, token));
                let stream = TokenStream::from_iter(iter);
                return TokenStream::from(TokenTree::Group(Group::new(group.delimiter(), stream)));
            }
            _ => {}
        }
        token.into()
    }
    let token_iter = src_stream
        .into_iter()
        .flat_map(|token| map_ident(field_by_name, token));
    Ok(TokenStream::from_iter(token_iter))
}

fn express_suffix(
    modifier_by_name: &HashMap<String, &Modifier>,
    field_by_name: &HashMap<String, &Field>,
    modifiers: &[String],
) -> Result<TokenStream> {
    Ok(if modifiers.is_empty() {
        quote!(String::new())
    } else {
        let mut chars = Vec::new();
        for mod_name in modifiers {
            let modifier: &Modifier = modifier_by_name
                .get(mod_name)
                .ok_or_else(|| Error::from(format!("undefined modifier {}", mod_name)))?;
            let lit_char = LitChar::new(modifier.suffix, Span::call_site());
            let modifier_bit = modifier.express_value_self(field_by_name)?;
            chars.push(quote! {
                if #modifier_bit {
                    s.push(#lit_char);
                }
            });
        }
        let chars = token_stream!(chars);
        quote!({
            {
                let mut s = String::with_capacity(4);
                #chars
                s
            }
        })
    })
}
