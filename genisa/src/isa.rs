use std::collections::HashMap;
use std::{fs::File, path::Path, str::FromStr};

use anyhow::{Context, Result};
use num_traits::PrimInt;
use proc_macro2::{Ident, Span, TokenStream};
use quote::{format_ident, ToTokens};
use serde::de::IntoDeserializer;
use serde::{Deserialize, Deserializer, Serialize};

pub fn load_isa(path: &Path) -> Result<Isa> {
    let yaml_file =
        File::open(path).with_context(|| format!("Failed to open file {}", path.display()))?;
    let isa: Isa = serde_yaml::from_reader(yaml_file)
        .with_context(|| format!("While parsing file {}", path.display()))?;
    Ok(isa)
}

#[derive(Deserialize, Serialize, Clone, Debug, Default)]
#[serde(default)]
pub struct Isa {
    pub fields: Vec<Field>,
    pub modifiers: Vec<Modifier>,
    pub opcodes: Vec<Opcode>,
    pub mnemonics: Vec<Mnemonic>,
}

impl Isa {
    pub fn find_field(&self, name: &str) -> Option<&Field> {
        self.fields.iter().find(|f| f.name == name)
    }

    pub fn find_modifier(&self, name: &str) -> Option<&Modifier> {
        self.modifiers.iter().find(|m| m.name == name)
    }

    pub fn find_opcode(&self, name: &str) -> Option<&Opcode> {
        self.opcodes.iter().find(|o| o.name == name)
    }
}

#[derive(Deserialize, Serialize, Clone, Debug, Default)]
#[serde(default)]
pub struct Field {
    pub name: String,
    pub desc: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub bits: Option<SplitBitRange>,
    pub signed: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub arg: Option<String>,
    pub shift_left: u8,
}

impl Field {
    /// Calculate the field mask from its bit range
    pub fn mask(&self) -> u32 {
        self.bits.as_ref().map(|b| b.mask()).unwrap_or(0)
    }

    /// Shift and mask a value according to the field
    pub fn shift_value(&self, value: u32) -> u32 {
        self.bits.as_ref().map(|b| b.shift_value(value >> self.shift_left)).unwrap_or(0)
    }

    pub fn ident(&self) -> Ident {
        format_ident!("field_{}", to_ident(&self.name))
    }

    pub fn doc(&self) -> String {
        if self.desc.is_empty() {
            format!(" {}", self.name)
        } else {
            format!(" {}: {}", self.name, self.desc)
        }
    }
}

impl ToTokens for Field {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        self.ident().to_tokens(tokens)
    }
}

#[derive(Deserialize, Serialize, Clone, Debug, Default)]
#[serde(default)]
pub struct Opcode {
    pub name: String,
    pub desc: String,
    pub bitmask: u32,
    pub pattern: u32,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub modifiers: Vec<String>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub args: Vec<String>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub defs: Vec<String>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub uses: Vec<String>,
}

impl Opcode {
    /// Calculate the opcode mask from its fields and modifiers
    pub fn mask(&self, isa: &Isa) -> u32 {
        let mut calc_bitmask = 0u32;
        for arg_n in &self.args {
            let Some(field) = isa.find_field(arg_n) else {
                continue;
            };
            calc_bitmask |= field.mask();
        }
        for modifier_n in &self.modifiers {
            let Some(modifier) = isa.find_modifier(modifier_n) else {
                continue;
            };
            calc_bitmask |= modifier.mask();
        }
        !calc_bitmask
    }

    pub fn ident(&self) -> Ident {
        Ident::new(&to_ident(&self.name), Span::call_site())
    }

    pub fn variant(&self) -> Ident {
        Ident::new(&to_variant(&self.name), Span::call_site())
    }

    pub fn doc(&self) -> String {
        if self.desc.is_empty() {
            format!(" {}", self.name)
        } else {
            format!(" {}: {}", self.name, self.desc)
        }
    }
}

impl ToTokens for Opcode {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        self.ident().to_tokens(tokens)
    }
}

#[derive(Deserialize, Serialize, Clone, Debug, Default)]
#[serde(default)]
pub struct Mnemonic {
    pub name: String,
    pub desc: String,
    pub opcode: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    // Overrides modifier list from opcode
    pub modifiers: Option<Vec<String>>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub args: Vec<String>,
    pub condition: String,
    #[serde(skip_serializing_if = "HashMap::is_empty")]
    pub replace: HashMap<String, String>,
    #[serde(skip_serializing_if = "HashMap::is_empty")]
    pub replace_assemble: HashMap<String, String>,
}

#[derive(Deserialize, Serialize, Clone, Debug, Default)]
#[serde(default)]
pub struct Modifier {
    pub name: String,
    pub desc: String,
    pub suffix: char,
    pub bit: u8,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub defs: Vec<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub condition: Option<String>,
}

impl Modifier {
    /// Calculate the modifier mask from its bit
    pub fn mask(&self) -> u32 {
        1 << (31 - self.bit)
    }

    pub fn ident(&self) -> Ident {
        format_ident!("field_{}", to_ident(&self.name))
    }

    pub fn doc(&self) -> String {
        if self.desc.is_empty() {
            format!(" {}", self.name)
        } else {
            format!(" {}: {}", self.name, self.desc)
        }
    }
}

impl ToTokens for Modifier {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        self.ident().to_tokens(tokens)
    }
}

/// A collection of modifiers
type Modifiers<'a> = Vec<&'a Modifier>;

/// Whether a collection of modifiers is valid (all bits are unique)
pub fn modifiers_valid(modifiers: &Modifiers) -> bool {
    let bits = modifiers.iter().map(|m| m.bit).collect::<Vec<_>>();
    bits.iter().all(|&b| bits.iter().filter(|&&x| x == b).count() == 1)
}

/// Iterate over all possible combinations of modifiers
pub fn modifiers_iter<'a>(
    modifiers: &'a [String],
    isa: &'a Isa,
) -> impl Iterator<Item = Modifiers<'a>> {
    (0..=(1 << modifiers.len()) - 1).map(move |b| {
        modifiers
            .iter()
            .enumerate()
            .filter(|(i, _)| b & (1 << i) != 0)
            .map(|(_, m)| isa.find_modifier(m).unwrap())
            .collect::<Vec<_>>()
    })
}

#[derive(Copy, Clone, Debug, Default)]
pub struct BitRange(pub (u8, u8));

impl BitRange {
    #[inline]
    pub fn new(start: u8, end: u8) -> Self {
        Self((start, end))
    }

    #[inline]
    pub fn start(&self) -> u8 {
        self.0 .0
    }

    #[inline]
    pub fn end(&self) -> u8 {
        self.0 .1
    }

    /// Calculate the mask from the range
    #[inline]
    pub fn mask(&self) -> u32 {
        self.max_value() << self.shift()
    }

    /// Number of bits to shift
    #[inline]
    pub fn shift(&self) -> u8 {
        32 - self.end()
    }

    /// Number of bits in the range
    #[inline]
    pub fn len(&self) -> u8 {
        self.end() - self.start()
    }

    /// Shift and mask a value according to the range
    #[inline]
    pub fn shift_value(&self, value: u32) -> u32 {
        (value & self.max_value()) << self.shift()
    }

    /// Calculate the maximum value that can be represented by the range
    #[inline]
    pub fn max_value(&self) -> u32 {
        (1 << self.len()) - 1
    }
}

impl<'de> Deserialize<'de> for BitRange {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let range_str: String = Deserialize::deserialize(deserializer)?;
        if let Some((start_str, end_str)) = range_str.split_once("..") {
            let start = start_str.trim().parse::<u8>().map_err(serde::de::Error::custom)?;
            let end = end_str.trim().parse::<u8>().map_err(serde::de::Error::custom)?;
            Ok(Self::new(start, end))
        } else {
            let bit_idx = range_str.trim().parse::<u8>().map_err(serde::de::Error::custom)?;
            Ok(Self::new(bit_idx, bit_idx + 1))
        }
    }
}

impl Serialize for BitRange {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        if self.start() + 1 == self.end() {
            self.start().to_string().serialize(serializer)
        } else {
            format!("{}..{}", self.start(), self.end()).serialize(serializer)
        }
    }
}

/// A collection of bit ranges, used to represent a (possibly non-contiguous) set of bits
#[derive(Clone, Debug, Default)]
pub struct SplitBitRange(pub Vec<BitRange>);

impl SplitBitRange {
    #[inline]
    pub fn end(&self) -> u8 {
        self.0.iter().map(|r| r.end()).max().unwrap_or(0)
    }

    /// Calculate the mask from the range
    #[inline]
    pub fn mask(&self) -> u32 {
        self.0.iter().map(|r| r.mask()).fold(0, |acc, m| acc | m)
    }

    /// Number of bits to shift
    #[inline]
    pub fn shift(&self) -> u8 {
        32 - self.end()
    }

    /// Number of bits in the range
    #[inline]
    pub fn len(&self) -> u8 {
        self.0.iter().map(|r| r.len()).sum()
    }

    /// Shift and mask a value according to the range
    #[inline]
    pub fn shift_value(&self, mut value: u32) -> u32 {
        let mut result = 0;
        for range in self.0.iter().rev() {
            result |= range.shift_value(value);
            value >>= range.len();
        }
        result
    }

    /// Calculate the maximum value that can be represented by the range
    #[inline]
    pub fn max_value(&self) -> u32 {
        (1 << self.len()) - 1
    }
}

impl<'de> Deserialize<'de> for SplitBitRange {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let ranges_str: String = Deserialize::deserialize(deserializer)?;
        let mut ranges = Vec::new();
        for range_str in ranges_str.split(',') {
            ranges.push(BitRange::deserialize(range_str.trim().into_deserializer())?);
        }
        Ok(Self(ranges))
    }
}

impl Serialize for SplitBitRange {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let mut ranges_str = String::new();
        for (i, range) in self.0.iter().enumerate() {
            if i > 0 {
                ranges_str.push(',');
            }
            if range.start() + 1 == range.end() {
                ranges_str.push_str(&range.start().to_string());
            } else {
                ranges_str.push_str(&format!("{}..{}", range.start(), range.end()));
            }
        }
        serializer.serialize_str(&ranges_str)
    }
}

pub fn to_ident(key: &str) -> String {
    key.to_ascii_lowercase().replace('.', "_").replace('+', "p").replace('-', "m")
}

pub fn to_variant(key: &str) -> String {
    let mut s = String::new();
    let mut chars = key.chars();
    loop {
        // Make first char uppercase.
        let c = match chars.next() {
            None => return s,
            Some(c) => c,
        };
        s.push(match c {
            'a'..='z' => c.to_ascii_uppercase(),
            'A'..='Z' => c,
            _ => panic!("invalid identifier: {key}"),
        });
        loop {
            let c = match chars.next() {
                None => return s,
                Some(c) => c,
            };
            match c.to_ascii_lowercase() {
                '0'..='9' | 'a'..='z' => s.push(c),
                '_' => break,
                '.' => {
                    s.push('_');
                    break;
                }
                _ => panic!("invalid character in variant: {key}"),
            }
        }
    }
}

/// Parse an unsigned number in decimal, binary, or hexadecimal format.
pub fn parse_unsigned(mask: &str) -> Result<u32, std::num::ParseIntError> {
    if let Some(mask) = mask.strip_prefix("0b") {
        u32::from_str_radix(mask, 2)
    } else if let Some(mask) = mask.strip_prefix("0x") {
        u32::from_str_radix(mask, 16)
    } else {
        mask.parse::<u32>()
    }
}

/// Parse a signed number in decimal, binary, or hexadecimal format.
pub fn parse_signed(mask: &str) -> Result<i32, std::num::ParseIntError> {
    if let Some(mask) = mask.strip_prefix('-') {
        if let Some(mask) = mask.strip_prefix("0b") {
            i32::from_str_radix(mask, 2).map(|n| -n)
        } else if let Some(mask) = mask.strip_prefix("0x") {
            i32::from_str_radix(mask, 16).map(|n| -n)
        } else {
            mask.parse::<i32>().map(|n| -n)
        }
    } else {
        parse_unsigned(mask).map(|n| n as i32)
    }
}

pub struct HexLiteral<T>(pub T);

impl<T> std::fmt::LowerHex for HexLiteral<T>
where
    T: std::fmt::LowerHex,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::LowerHex::fmt(&self.0, f)
    }
}

impl<T> ToTokens for HexLiteral<T>
where
    T: std::fmt::LowerHex,
{
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let s = format!("{self:#x}");
        tokens.extend(TokenStream::from_str(&s).unwrap());
    }
}

pub struct SignedHexLiteral<T>(pub T);

impl<T> std::fmt::LowerHex for SignedHexLiteral<T>
where
    T: PrimInt + std::fmt::LowerHex,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.0 < T::zero() {
            write!(f, "-")?;
            let int = self.0.to_i64().unwrap_or_default();
            std::fmt::LowerHex::fmt(&-int, f)
        } else {
            std::fmt::LowerHex::fmt(&self.0, f)
        }
    }
}

impl<T> ToTokens for SignedHexLiteral<T>
where
    T: PrimInt + std::fmt::LowerHex,
{
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let s = format!("{self:#x}");
        tokens.extend(TokenStream::from_str(&s).unwrap());
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_split_bit_range() {
        let range = SplitBitRange(vec![BitRange::new(26, 27), BitRange::new(21, 26)]);
        assert_eq!(range.mask(), 0b0000_0000_0000_0000_0000_0111_1110_0000);
        assert_eq!(range.shift(), 5);
        assert_eq!(range.len(), 6);
        assert_eq!(range.max_value(), 0x3F);
        assert_eq!(range.shift_value(u32::MAX), 0b0000_0000_0000_0000_0000_0111_1110_0000);
        assert_eq!(range.shift_value(0x1F), 0b0000_0000_0000_0000_0000_0111_1100_0000);
    }

    #[test]
    fn test_split_bit_range_non_contiguous() {
        let range = SplitBitRange(vec![BitRange::new(30, 31), BitRange::new(16, 21)]);
        assert_eq!(range.mask(), 0b0000_0000_0000_0000_1111_1000_0000_0010);
        assert_eq!(range.shift(), 1);
        assert_eq!(range.len(), 6);
        assert_eq!(range.max_value(), 0x3F);
        assert_eq!(range.shift_value(u32::MAX), 0b0000_0000_0000_0000_1111_1000_0000_0010);
        assert_eq!(range.shift_value(0x1F), 0b0000_0000_0000_0000_1111_1000_0000_0000);
    }
}
