use powerpc::{Argument, Extension, Extensions, Ins, Opcode, FPR, GPR};

const EXTENSIONS: Extensions = Extensions::from_extension(Extension::PairedSingles);

macro_rules! assert_asm {
    ($ins:ident, $disasm:literal) => {{
        assert_eq!(format!("{}", $ins.simplified()), $disasm)
    }};
    ($code:literal, $disasm:literal) => {{
        let ins = Ins::new($code, EXTENSIONS);
        assert_eq!(format!("{}", ins.simplified()), $disasm)
    }};
}

#[test]
fn test_ins_dcbz_l() {
    assert_asm!(0x10061FEC, "dcbz_l r6, r3");
}

#[test]
fn test_ins_psq_l() {
    assert_asm!(0xE02500AC, "psq_l f1, 0xac(r5), 0, qr0");
}

#[test]
fn test_ins_psq_lu() {
    assert_asm!(0xE5435010, "psq_lu f10, 0x10(r3), 0, qr5");
}

#[test]
fn test_ins_psq_lx() {
    let ins = Ins::new(0x1000000C, EXTENSIONS);
    assert_eq!(ins.op, Opcode::PsqLx);
    // assert_eq!(
    //     ins.fields(),
    //     vec![
    //         frD(FPR(0)),
    //         rA(GPR(0)),
    //         rB(GPR(0)),
    //         ps_WX(OpaqueU(0)),
    //         ps_IX(GQR(0)),
    //     ]
    // );
    assert_eq!(
        ins.defs(),
        [Argument::FPR(FPR(0)), Argument::None, Argument::None, Argument::None, Argument::None]
    );
    assert_eq!(
        ins.uses(),
        [Argument::None, Argument::GPR(GPR(0)), Argument::None, Argument::None, Argument::None]
    );

    assert_asm!(0x1000000C, "psq_lx f0, r0, r0, 0, qr0");
}

#[test]
fn test_ins_psq_st() {
    assert_asm!(0xF1230210, "psq_st f9, 0x210(r3), 0, qr0");
    assert_asm!(0xF1238008, "psq_st f9, 0x8(r3), 1, qr0");
}

#[test]
fn test_ins_psq_stu() {
    assert_asm!(0xF40A0020, "psq_stu f0, 0x20(r10), 0, qr0");
}

#[test]
fn test_ins_psq_stx() {
    assert_asm!(0x13E1000E, "psq_stx f31, r1, r0, 0, qr0");
}

#[test]
fn test_ins_ps_abs() {
    assert_asm!(0x10A03210, "ps_abs f5, f6");
}

#[test]
fn test_ins_ps_add() {
    assert_asm!(0x1006382A, "ps_add f0, f6, f7");
}

#[test]
fn test_ins_ps_cmpo0() {
    assert_asm!(0x10070840, "ps_cmpo0 cr0, f7, f1");
}

#[test]
fn test_ins_ps_cmpu0() {
    assert_asm!(0x10003000, "ps_cmpu0 cr0, f0, f6");
}

#[test]
fn test_ins_ps_cmpu1() {
    assert_asm!(0x10003080, "ps_cmpu1 cr0, f0, f6");
}

#[test]
fn test_ins_ps_madd() {
    assert_asm!(0x112141FA, "ps_madd f9, f1, f7, f8");
}

#[test]
fn test_ins_ps_madds0() {
    assert_asm!(0x10AC299C, "ps_madds0 f5, f12, f6, f5");
}

#[test]
fn test_ins_ps_madds1() {
    assert_asm!(0x110640DE, "ps_madds1 f8, f6, f3, f8");
}

#[test]
fn test_ins_ps_merge00() {
    assert_asm!(0x10400420, "ps_merge00 f2, f0, f0");
}

#[test]
fn test_ins_ps_merge01() {
    assert_asm!(0x10400C60, "ps_merge01 f2, f0, f1");
}

#[test]
fn test_ins_ps_merge10() {
    assert_asm!(0x104004A0, "ps_merge10 f2, f0, f0");
}

#[test]
fn test_ins_ps_merge11() {
    assert_asm!(0x10AA14E0, "ps_merge11 f5, f10, f2");
}

#[test]
fn test_ins_ps_mr() {
    assert_asm!(0x10200090, "ps_mr f1, f0");
}

#[test]
fn test_ins_ps_msub() {
    assert_asm!(0x10A53778, "ps_msub f5, f5, f29, f6");
}

#[test]
fn test_ins_ps_mul() {
    assert_asm!(0x10000032, "ps_mul f0, f0, f0");
}

#[test]
fn test_ins_ps_muls0() {
    assert_asm!(0x100002D8, "ps_muls0 f0, f0, f11");
}

#[test]
fn test_ins_ps_muls1() {
    assert_asm!(0x10A2005A, "ps_muls1 f5, f2, f1");
}

#[test]
fn test_ins_ps_nabs() {
    assert_asm!(0x10803210, "ps_abs f4, f6");
}

#[test]
fn test_ins_ps_neg() {
    assert_asm!(0x10E03850, "ps_neg f7, f7");
}

#[test]
fn test_ins_ps_nmadd() {
    assert_asm!(0x10CB30FE, "ps_nmadd f6, f11, f3, f6");
}

#[test]
fn test_ins_ps_nmsub() {
    assert_asm!(0x107E083C, "ps_nmsub f3, f30, f0, f1");
}

#[test]
fn test_ins_ps_sel() {
    assert_asm!(0x106428EE, "ps_sel f3, f4, f3, f5");
}

#[test]
fn test_ins_ps_sub() {
    assert_asm!(0x10A92828, "ps_sub f5, f9, f5");
}

#[test]
fn test_ins_ps_sum0() {
    assert_asm!(0x10230854, "ps_sum0 f1, f3, f1, f1");
}

#[test]
fn test_ins_ps_sum1() {
    assert_asm!(0x10A12956, "ps_sum1 f5, f1, f5, f5");
}
