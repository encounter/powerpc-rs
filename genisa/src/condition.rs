use std::str::FromStr;

use anyhow::{anyhow, Context, Result};
use proc_macro2::{Group, Ident, TokenStream, TokenTree};
use quote::quote;

use crate::isa::{parse_signed, parse_unsigned, Field, HexLiteral, Isa, SignedHexLiteral};

/// A condition that must be met for a modifier to be applied
/// or for a simplified mnemonic to be matched.
#[derive(Clone, Debug)]
pub struct Condition<'a> {
    pub field: &'a Field,
    pub field_mask: u32,
    pub op: ConditionOp,
    pub value: ConditionValue<'a>,
}

/// The operation of a complex condition.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum ConditionOp {
    /// Equal to. (e.g. `MB == 0`)
    Eq,
    /// Not equal to. (e.g. `simm != -0x8000`)
    Ne,
    /// Less than. (e.g. `simm < 0`)
    Lt,
    /// Greater than. (e.g. `SH > 16`)
    Gt,
    /// Less than or equal to. (e.g. `SH <= 16`)
    Lte,
    /// Greater than or equal to. (e.g. `SH >= 32 - MB`)
    Gte,
}

/// The value of a condition.
#[derive(Clone, Debug)]
pub enum ConditionValue<'a> {
    /// A constant unsigned value. (e.g. `MB == 0`)
    ConstantUnsigned(u32),
    /// A constant signed value. (e.g. `simm != -0x8000`)
    ConstantSigned(i32),
    /// A field value. (e.g. `rB == rS`)
    Field(&'a Field),
    /// A complex condition. (e.g. `SH >= 32 - MB`)
    Complex(&'a str),
}

/// Parse a condition string into a list of conditions. (e.g. `SH >= 32 - MB && MB == 0`)
/// Maybe turn this into a real lexer/parser if it gets more complex.
pub fn parse_conditions<'a>(condition: &'a str, isa: &'a Isa) -> Result<Vec<Condition<'a>>> {
    let mut conditions = Vec::new();
    for tok in condition.split(" && ") {
        let (mut field, value, op) = if let Some((field, value)) = tok.split_once(" == ") {
            (field, value, ConditionOp::Eq)
        } else if let Some((field, value)) = tok.split_once(" != ") {
            (field, value, ConditionOp::Ne)
        } else if let Some((field, value)) = tok.split_once(" < ") {
            (field, value, ConditionOp::Lt)
        } else if let Some((field, value)) = tok.split_once(" > ") {
            (field, value, ConditionOp::Gt)
        } else if let Some((field, value)) = tok.split_once(" <= ") {
            (field, value, ConditionOp::Lte)
        } else if let Some((field, value)) = tok.split_once(" >= ") {
            (field, value, ConditionOp::Gte)
        } else {
            log::error!("Invalid condition: {}", tok);
            continue;
        };
        let mut field_mask = u32::MAX;
        if let Some((n, mask)) = field.split_once(" & ") {
            field = n;
            field_mask = parse_unsigned(mask)?;
        };
        let field = isa
            .find_field(field)
            .with_context(|| format!("Condition references unknown field {field}"))?;
        let value = if let Ok(value) = parse_unsigned(value) {
            ConditionValue::ConstantUnsigned(value)
        } else if let Ok(value) = parse_signed(value) {
            ConditionValue::ConstantSigned(value)
        } else if let Some(field) = isa.find_field(value) {
            ConditionValue::Field(field)
        } else {
            ConditionValue::Complex(value)
        };
        conditions.push(Condition { field, field_mask, op, value });
    }
    Ok(conditions)
}

impl Condition<'_> {
    pub fn to_token_stream(&self, isa: &Isa, self_ident: Ident) -> Result<TokenStream> {
        // Accessor
        let field = self.field;
        let mut accessor = quote!(#self_ident.#field());
        if self.field_mask != u32::MAX {
            let mask = HexLiteral(self.field_mask);
            accessor = quote! { (#accessor & #mask) };
        }

        // Operator
        let op = match self.op {
            ConditionOp::Eq => quote! { == },
            ConditionOp::Ne => quote! { != },
            ConditionOp::Lt => quote! { < },
            ConditionOp::Gt => quote! { > },
            ConditionOp::Lte => quote! { <= },
            ConditionOp::Gte => quote! { >= },
        };

        // Value
        let value = match self.value {
            ConditionValue::ConstantUnsigned(v) => {
                let v = HexLiteral(v);
                quote! { #v }
            }
            ConditionValue::ConstantSigned(v) => {
                let v = SignedHexLiteral(v);
                quote! { #v }
            }
            ConditionValue::Field(f) => {
                quote! { #self_ident.#f() }
            }
            ConditionValue::Complex(c) => {
                replace_fields(c, isa, |f| Ok(quote! { #self_ident.#f() }))?
            }
        };

        Ok(quote! { #accessor #op #value })
    }
}

pub fn replace_fields(
    s: &str,
    isa: &Isa,
    mut accessor: impl FnMut(&Field) -> Result<TokenStream>,
) -> Result<TokenStream> {
    fn replace_inner(
        s: TokenStream,
        isa: &Isa,
        accessor: &mut impl FnMut(&Field) -> Result<TokenStream>,
    ) -> Result<TokenStream> {
        s.into_iter()
            .map(|t| -> Result<TokenStream> {
                match &t {
                    TokenTree::Ident(ident) => {
                        if let Some(field) = isa.find_field(&ident.to_string()) {
                            return accessor(field);
                        }
                    }
                    TokenTree::Group(g) => {
                        return Ok(TokenStream::from(TokenTree::Group(Group::new(
                            g.delimiter(),
                            replace_inner(g.stream(), isa, accessor)?,
                        ))));
                    }
                    _ => {}
                }
                Ok(TokenStream::from(t))
            })
            .collect::<Result<TokenStream>>()
    }
    let stream = TokenStream::from_str(s).map_err(|e| anyhow!("{}", e))?;
    replace_inner(stream, isa, &mut accessor)
}
