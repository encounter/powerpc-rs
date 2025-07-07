use crate::Arguments;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum ArgumentError {
    #[error(
        "argument index {index} is out of range: {value} (expected between {start} and {end})"
    )]
    ArgOutOfRangeUnsigned { index: usize, value: u32, start: u32, end: u32 },
    #[error(
        "argument index {index} is out of range: {value} (expected between {start} and {end})"
    )]
    ArgOutOfRangeSigned { index: usize, value: i32, start: i32, end: i32 },
    #[error("unexpected number of arguments: {value} (expected at most {expected})")]
    ArgCount { value: usize, expected: usize },
    #[error("unknown instruction mnemonic")]
    UnknownMnemonic,
}

#[derive(Debug, Default, Clone, Copy, Eq, PartialEq)]
pub enum Argument {
    #[default]
    None,
    Unsigned(u32),
    Signed(i32),
}

pub const fn parse_unsigned(
    args: &Arguments,
    index: usize,
    start: u32,
    end: u32,
) -> Result<u32, ArgumentError> {
    match args[index] {
        Argument::Unsigned(value) => {
            if value >= start && value <= end {
                Ok(value)
            } else {
                Err(ArgumentError::ArgOutOfRangeUnsigned { index, value, start, end })
            }
        }
        Argument::Signed(value) => {
            if value >= start as i32 && value <= end as i32 {
                Ok(value as u32)
            } else {
                Err(ArgumentError::ArgOutOfRangeUnsigned { index, value: value as u32, start, end })
            }
        }
        Argument::None => Err(ArgumentError::ArgCount { value: index, expected: index + 1 }),
    }
}

pub const fn parse_signed(
    args: &Arguments,
    index: usize,
    start: i32,
    end: i32,
) -> Result<i32, ArgumentError> {
    match args[index] {
        Argument::Unsigned(value) => {
            if (start < 0 || value >= start as u32) && value <= end as u32 {
                Ok(value as i32)
            } else {
                Err(ArgumentError::ArgOutOfRangeSigned { index, value: value as i32, start, end })
            }
        }
        Argument::Signed(value) => {
            if value >= start && value <= end {
                Ok(value)
            } else {
                Err(ArgumentError::ArgOutOfRangeSigned { index, value, start, end })
            }
        }
        Argument::None => Err(ArgumentError::ArgCount { value: index, expected: index + 1 }),
    }
}

pub const fn arg_count(args: &Arguments) -> usize {
    let mut i = 0;
    while i < args.len() && !matches!(args[i], Argument::None) {
        i += 1;
    }
    i
}

pub const fn check_arg_count(args: &Arguments, expected: usize) -> Result<(), ArgumentError> {
    let value = arg_count(args);
    if value == expected {
        Ok(())
    } else {
        Err(ArgumentError::ArgCount { value, expected })
    }
}
