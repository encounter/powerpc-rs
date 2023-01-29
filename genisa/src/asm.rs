use std::{
    collections::{hash_map::Entry, HashMap},
    fs::File,
    io::Write,
    str::FromStr,
};

use pratt::{Affix, Associativity, PrattParser, Precedence, Result as PrattResult};
use proc_macro2::{token_stream, Ident, Literal, Spacing, Span, TokenStream, TokenTree};
use quote::{__private::ext::RepToTokensExt, quote, ToTokens};
use syn::{parse::Parser, LitInt};

use crate::{load_isa, rustfmt, to_rust_variant, Field, Isa, Modifier, Opcode};

type Error = Box<dyn std::error::Error>;
type Result<T> = std::result::Result<T, Error>;

macro_rules! token_stream {
    ($stream:ident) => {
        TokenStream::from_iter($stream.into_iter())
    };
}

pub(crate) fn asm_main() -> Result<()> {
    let isa = load_isa()?;

    let mut unformatted_code = Vec::<u8>::new();
    writeln!(&mut unformatted_code, "{}", quote! {
        use crate::prelude::*;
    })?;
    writeln!(&mut unformatted_code, "{}", gen_fields(&isa)?)?;
    writeln!(&mut unformatted_code, "{}", gen_opcode_from_str(&isa)?)?;

    let formatted_code = rustfmt(unformatted_code);
    File::create("./asm/src/generated.rs")?.write_all(&formatted_code)?;

    Ok(())
}

fn gen_apply_field(field: &Field) -> Result<TokenStream> {
    let mut val = quote! { value as u32 };

    let val_shift = field.shift_left;
    if field.shift_left > 0 {
        val = quote!((#val >> #val_shift));
    }

    // https://graphics.stanford.edu/~seander/bithacks.html#VariableSignExtend
    if field.signed {
        // let mask2 = 1u32 << (self.bits.0.len() - 1);
        // let mask2 = LitInt::new(&format!("0x{:x}", mask2), Span::call_site());
        // val = quote!((((#val ^ #mask2).wrapping_sub(#mask2)) as i32))
    } else {
        // val = quote! { #val };
    }

    if field.split {
        val = quote!((((#val & 0b11111_00000u32) >> 5u32) | ((#val & 0b00000_11111u32) << 5u32)) as u32);
    }

    let mask = (1u32 << field.bits.0.len()) - 1;
    if mask != 0xFFFF_FFFF {
        let mask = LitInt::new(&format!("0x{:x}", mask), Span::call_site());
        val = quote!((#val & #mask));
    }

    let shift = 32 - field.bits.0.end;
    if shift > 0 {
        val = quote!((#val << #shift));
    }

    let ident = to_rust_variant(&field.name)?;
    Ok(quote! {
        Field::#ident => code | #val,
    })
}

fn gen_fields(isa: &Isa) -> Result<TokenStream> {
    let fields = TokenStream::from_iter(
        isa.fields
            .iter()
            .filter(|field| !field.bits.0.is_empty())
            .map(|field| -> Result<TokenStream> {
                let ident = to_rust_variant(field.name.as_str())?;
                Ok(quote! { #ident, })
            })
            .try_collect::<TokenStream>()?,
    );
    let field_match = TokenStream::from_iter(
        isa.fields
            .iter()
            .filter(|field| !field.bits.0.is_empty())
            .map(|field| gen_apply_field(field))
            .try_collect::<TokenStream>()?,
    );
    return Ok(quote! {
        pub enum Field {
            #fields
        }
        pub const fn apply_field(code: u32, field: Field, value: i32) -> u32 {
            match field {
                #field_match
            }
        }
    });
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_gpr() {
        assert_eq!(parse_gpr("r0").unwrap(), (0, ""));
        assert_eq!(parse_gpr("r31").unwrap(), (31, ""));
        assert_eq!(parse_gpr("1234").unwrap(), (1234, ""));
    }
}

struct OpcodeInfo {
    code: u32,
    args: Vec<String>,
}

fn gen_opcode_from_str(isa: &Isa) -> Result<TokenStream> {
    let mut map_builder = phf_codegen::Map::<String>::new();
    let mut opcode_map = HashMap::<String, Vec<Option<OpcodeInfo>>>::new();
    for opcode in &isa.opcodes {
        let mut modifiers = Vec::<Modifier>::with_capacity(opcode.modifiers.len());
        for modifier_name in &opcode.modifiers {
            modifiers.push(match isa.modifiers.iter().find(|m| m.name == *modifier_name) {
                Some(modifier) => modifier.clone(),
                None => return Err(Error::from(format!("Modifier {} not found", modifier_name))),
            });
        }
        'outer: for bits in 0..(1 << modifiers.len()) {
            let mut suffix = String::new();
            let mut set_bits = 0u32;
            for (idx, modifier) in modifiers.iter().enumerate() {
                if bits & (1 << idx) != 0 {
                    if set_bits & (1 << modifier.bit) != 0 {
                        // Incompatible combination
                        continue 'outer;
                    }
                    set_bits |= 1 << modifier.bit;
                    suffix.push(modifier.suffix);
                }
            }
            let name = format!("{}{}", opcode.name, suffix);
            let info = OpcodeInfo { code: opcode.pattern, args: opcode.args.clone() };
            match opcode_map.entry(name) {
                Entry::Occupied(mut entry) => {
                    let vec = entry.get_mut();
                    if vec.len() < opcode.args.len() + 1 {
                        vec.resize_with(opcode.args.len() + 1, || None);
                    }
                    vec[opcode.args.len()] = Some(info);
                }
                Entry::Vacant(entry) => {
                    let mut vec = Vec::<Option<OpcodeInfo>>::new();
                    vec.resize_with(opcode.args.len() + 1, || None);
                    vec[opcode.args.len()] = Some(info);
                    entry.insert(vec);
                }
            }
            // println!("Adding opcode {}", name);
            // let quoted_name = format!("\"{}\"", name);
            // map_builder.entry(name, quoted_name.as_str());
        }
    }
    for mnemonic in &isa.mnemonics {
        let opcode = isa.opcodes.iter().find(|o| o.name == mnemonic.opcode).ok_or_else(|| {
            Error::from(format!("Opcode {} not found for {}", mnemonic.opcode, mnemonic.name))
        })?;
        let modifier_names = mnemonic.modifiers.as_ref().unwrap_or(&opcode.modifiers);
        let mut modifiers = Vec::<Modifier>::with_capacity(modifier_names.len());
        for modifier_name in modifier_names {
            modifiers.push(match isa.modifiers.iter().find(|m| m.name == *modifier_name) {
                Some(modifier) => modifier.clone(),
                None => return Err(Error::from(format!("Modifier {} not found", modifier_name))),
            });
        }
        'outer: for bits in 0..(1 << modifiers.len()) {
            let mut suffix = String::new();
            let mut set_bits = 0u32;
            for (idx, modifier) in modifiers.iter().enumerate() {
                if bits & (1 << idx) != 0 {
                    if set_bits & (1 << modifier.bit) != 0 {
                        // Incompatible combination
                        continue 'outer;
                    }
                    set_bits |= 1 << modifier.bit;
                    suffix.push(modifier.suffix);
                }
            }
            let name = format!("{}{}", mnemonic.name, suffix);
            let mut code = opcode.pattern;
            {
                let tokens: TokenStream = mnemonic.condition.parse()?;
                let mut iter = tokens.into_iter();
                let mut vec = Vec::<ParsedToken>::new();
                loop {
                    match parse_token(&mut iter) {
                        Some(token) => vec.push(token),
                        None => break,
                    }
                }
                let expr = ExprParser.parse(vec.into_iter()).unwrap();
                match apply_expr(code, expr, isa)? {
                    ExprResult::Int(out) => {
                        code = out;
                    }
                    _ => unreachable!(),
                }
            }
            // for arg in mnemonic.args {
            //     code = apply_field(code, )
            // }
            let info = OpcodeInfo { code, args: mnemonic.args.clone() };
            match opcode_map.entry(name) {
                Entry::Occupied(mut entry) => {
                    let vec = entry.get_mut();
                    if vec.len() < mnemonic.args.len() + 1 {
                        vec.resize_with(mnemonic.args.len() + 1, || None);
                    }
                    vec[mnemonic.args.len()] = Some(info);
                }
                Entry::Vacant(entry) => {
                    let mut vec = Vec::<Option<OpcodeInfo>>::new();
                    vec.resize_with(mnemonic.args.len() + 1, || None);
                    vec[mnemonic.args.len()] = Some(info);
                    entry.insert(vec);
                }
            }
            // println!("Adding mnemonic {}", name);
            // let quoted_name = format!("\"{}\"", name);
            // map_builder.entry(name, quoted_name.as_str());
        }
    }
    for (name, infos) in opcode_map {
        let opcodes = TokenStream::from_iter(infos.iter().map(|info| {
            if let Some(info) = info {
                let code = LitInt::new(&format!("0x{:x}", info.code), Span::call_site());
                let args = TokenStream::from_iter(info.args.iter().map(|arg| {
                    let arg_s = arg.split_once('=').map(|(first, _)| first).unwrap_or(arg);
                    let ident = to_rust_variant(arg_s).unwrap();
                    quote! { Field::#ident, }
                }));
                quote! {
                    Some(OpcodeInfo {
                        code: #code,
                        args: &[ #args ],
                    }),
                }
            } else {
                quote! { None, }
            }
        }));
        map_builder.entry(name, quote! { &[#opcodes] }.to_string().as_str());
    }
    let map: TokenStream = map_builder.build().to_string().parse()?;
    return Ok(quote! {
        struct OpcodeInfo {
            code: u32,
            args: &'static [Field],
        }
        static OPCODES: phf::Map<&'static str, &'static [Option<OpcodeInfo>]> = #map;
        fn opcode_from_str(str: &str) -> Option<&'static [Option<OpcodeInfo>]> {
            OPCODES.get(str).map(|x| *x)
        }
    });
}

fn apply_field(code: u32, field: &Field, value: i32) -> u32 {
    let mut val = value as u32;

    let val_shift = field.shift_left;
    if field.shift_left > 0 {
        val = val >> val_shift;
    }

    // https://graphics.stanford.edu/~seander/bithacks.html#VariableSignExtend
    if field.signed {
        // let mask2 = 1u32 << (self.bits.0.len() - 1);
        // let mask2 = LitInt::new(&format!("0x{:x}", mask2), Span::call_site());
        // val = quote!((((#val ^ #mask2).wrapping_sub(#mask2)) as i32))
    } else {
        // val = quote! { #val };
    }

    if field.split {
        val = (((val & 0b11111_00000u32) >> 5u32) | ((val & 0b00000_11111u32) << 5u32)) as u32;
    }

    let mask = (1u32 << field.bits.0.len()) - 1;
    if mask != 0xFFFF_FFFF {
        val = val & mask;
    }

    let shift = 32 - field.bits.0.end;
    if shift > 0 {
        val = val << shift;
    }

    code | val
}

#[derive(Debug, PartialEq)]
enum Operator {
    BitAnd,
    LogicalAnd,
    Equal,
}

#[derive(Debug)]
enum ParsedToken {
    Ident(Ident),
    Group(Vec<ParsedToken>),
    Literal(Literal),
    Operator(Operator),
}

#[derive(Debug)]
pub enum Expr {
    BinOp(Box<Expr>, BinOpKind, Box<Expr>),
    // UnOp(UnOpKind, Box<Expr>),
    Literal(Literal),
    Ident(Ident),
}

#[derive(Debug)]
pub enum BinOpKind {
    // &
    BitAnd,
    // &&
    LogicalAnd,
    // ==
    Eq,
}

#[derive(Debug)]
pub enum UnOp {}

fn parse_token(iter: &mut token_stream::IntoIter) -> Option<ParsedToken> {
    match iter.next() {
        Some(TokenTree::Group(group)) => {
            let mut iter = group.stream().into_iter();
            let mut vec = Vec::<ParsedToken>::new();
            loop {
                match parse_token(&mut iter) {
                    Some(token) => vec.push(token),
                    None => break,
                }
            }
            Some(ParsedToken::Group(vec))
        }
        Some(TokenTree::Punct(mut punct)) => {
            let mut str = String::new();
            str.push(punct.as_char());
            while punct.spacing() == Spacing::Joint {
                match iter.next() {
                    Some(TokenTree::Punct(new_punct)) => {
                        punct = new_punct;
                    }
                    token => panic!("unexpected token {:?}", token),
                }
                str.push(punct.as_char());
            }
            Some(ParsedToken::Operator(match str.as_str() {
                "&" => Operator::BitAnd,
                "&&" => Operator::LogicalAnd,
                "==" => Operator::Equal,
                op => todo!("operator {}", op),
            }))
        }
        Some(TokenTree::Ident(ident)) => Some(ParsedToken::Ident(ident)),
        Some(TokenTree::Literal(literal)) => Some(ParsedToken::Literal(literal)),
        None => None,
    }
}

struct ExprParser;

impl<I> PrattParser<I> for ExprParser
where I: Iterator<Item = ParsedToken>
{
    type Error = pratt::NoError;
    type Input = ParsedToken;
    type Output = Expr;

    fn query(&mut self, tree: &ParsedToken) -> PrattResult<Affix> {
        let affix = match tree {
            ParsedToken::Operator(Operator::BitAnd) => {
                Affix::Infix(Precedence(3), Associativity::Left)
            }
            ParsedToken::Operator(Operator::Equal) => {
                Affix::Infix(Precedence(2), Associativity::Left)
            }
            ParsedToken::Operator(Operator::LogicalAnd) => {
                Affix::Infix(Precedence(1), Associativity::Left)
            }
            ParsedToken::Group(_) | ParsedToken::Literal(_) | ParsedToken::Ident(_) => {
                Affix::Nilfix
            }
        };
        Ok(affix)
    }

    // Construct a primary expression, e.g. a number
    fn primary(&mut self, tree: ParsedToken) -> PrattResult<Expr> {
        let expr = match tree {
            ParsedToken::Ident(num) => Expr::Ident(num),
            ParsedToken::Literal(literal) => Expr::Literal(literal),
            ParsedToken::Group(group) => self.parse(&mut group.into_iter()).unwrap(),
            _ => unreachable!(),
        };
        Ok(expr)
    }

    // Construct a binary infix expression, e.g. 1+1
    fn infix(&mut self, lhs: Expr, tree: ParsedToken, rhs: Expr) -> PrattResult<Expr> {
        let op = match tree {
            ParsedToken::Operator(Operator::BitAnd) => BinOpKind::BitAnd,
            ParsedToken::Operator(Operator::LogicalAnd) => BinOpKind::LogicalAnd,
            ParsedToken::Operator(Operator::Equal) => BinOpKind::Eq,
            _ => unreachable!(),
        };
        Ok(Expr::BinOp(Box::new(lhs), op, Box::new(rhs)))
    }

    fn prefix(&mut self, _tree: ParsedToken, _rhs: Expr) -> PrattResult<Expr> { unreachable!() }

    fn postfix(&mut self, _lhs: Expr, _tree: ParsedToken) -> PrattResult<Expr> { unreachable!() }
}

#[derive(Debug)]
enum ExprResult {
    Int(u32),
    Ident(String),
}

fn apply_expr(mut code: u32, expr: Expr, isa: &Isa) -> Result<ExprResult> {
    match expr {
        Expr::BinOp(lhs, kind, rhs) => match kind {
            BinOpKind::BitAnd => match *lhs {
                // ignoring rhs
                Expr::Ident(ident) => Ok(ExprResult::Ident(ident.to_string())),
                other => todo!("BitAnd {:?}", other),
            },
            BinOpKind::LogicalAnd => {
                code = match apply_expr(code, *lhs, isa)? {
                    ExprResult::Int(code) => code,
                    _ => unreachable!(),
                };
                code = match apply_expr(code, *rhs, isa)? {
                    ExprResult::Int(code) => code,
                    _ => unreachable!(),
                };
                Ok(ExprResult::Int(code))
            }
            BinOpKind::Eq => {
                let field_name = match apply_expr(code, *lhs, isa)? {
                    ExprResult::Ident(ident) => ident,
                    other => todo!("eq lhs {:?}", other),
                };
                let field = isa
                    .fields
                    .iter()
                    .find(|field| field.name == field_name)
                    .ok_or_else(|| Error::from(format!("Field {} not found", field_name)))?;
                let value = match apply_expr(code, *rhs, isa)? {
                    ExprResult::Int(value) => value,
                    // other => todo!("eq rhs {:?}", other),
                    _ => return Ok(ExprResult::Int(code))
                };
                code = apply_field(code, field, value as i32);
                Ok(ExprResult::Int(code))
            }
        },
        Expr::Literal(lit) => Ok(ExprResult::Int(LitInt::from(lit).base10_parse()?)),
        Expr::Ident(id) => Ok(ExprResult::Ident(id.to_string())),
    }
}
