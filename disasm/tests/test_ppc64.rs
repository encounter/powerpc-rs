use powerpc::{Extension, Extensions, Ins};

const EXTENSIONS: Extensions = Extensions::from_extension(Extension::Ppc64);

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
fn test_ins_cntlzd() {
    assert_asm!(0x7CA30074, "cntlzd r3, r5");
}

#[test]
fn test_vmx_dcbzl() {
    assert_asm!(0x7c2327ec, "dcbzl r3, r4");
    assert_asm!(0x7c20ffec, "dcbzl r0, r31");
}

#[test]
fn test_ins_divd() {
    assert_asm!(0x7CA63BD2, "divd r5, r6, r7");
}

#[test]
fn test_ins_divdu() {
    assert_asm!(0x7C839392, "divdu r4, r3, r18");
}

#[test]
fn test_ins_extsw() {
    assert_asm!(0x7CC307B4, "extsw r3, r6");
    assert_asm!(0x7CC307B5, "extsw. r3, r6");
}

#[test]
fn test_ins_fcfid() {
    assert_asm!(0xFC602E9C, "fcfid f3, f5");
}

#[test]
fn test_ins_fctid() {
    assert_asm!(0xFC60065C, "fctid f3, f0");
}

#[test]
fn test_ins_fctidz() {
    assert_asm!(0xFC60065E, "fctidz f3, f0");
}

#[test]
fn test_ins_fsqrt() {
    assert_asm!(0xfc60f82c, "fsqrt f3, f31");
    assert_asm!(0xffe0102d, "fsqrt. f31, f2");
}

#[test]
fn test_ins_fsqrts() {
    assert_asm!(0xec40182c, "fsqrts f2, f3");
    assert_asm!(0xec60f82d, "fsqrts. f3, f31");
}

#[test]
fn test_ins_ld() {
    assert_asm!(0xebe10058, "ld r31, 0x58(r1)");
    assert_asm!(0xe9790010, "ld r11, 0x10(r25)");
}

#[test]
fn test_ins_ldarx() {
    assert_asm!(0x7C6538A8, "ldarx r3, r5, r7");
}

#[test]
fn test_ins_ldu() {
    assert_asm!(0xe97cfff9, "ldu r11, -0x8(r28)");
    assert_asm!(0xe8deffe9, "ldu r6, -0x18(r30)");
}

#[test]
fn test_ins_ldux() {
    assert_asm!(0x7C60286A, "ldux r3, r0, r5");
}

#[test]
fn test_ins_ldx() {
    assert_asm!(0x7C60282A, "ldx r3, r0, r5");
}

#[test]
fn test_ins_lwa() {
    assert_asm!(0xe97fffea, "lwa r11, -0x18(r31)");
}

#[test]
fn test_ins_lwaux() {
    assert_asm!(0x7C8532EA, "lwaux r4, r5, r6");
}

#[test]
fn test_ins_lwax() {
    assert_asm!(0x7CA63AAA, "lwax r5, r6, r7");
}

#[test]
fn test_ins_mfocrf() {
    assert_asm!(0x7d702026, "mfocrf r11, 2");
}

#[test]
fn test_ins_mtmsrd() {
    assert_asm!(0x7C000164, "mtmsrd r0, 0");
    assert_asm!(0x7D210164, "mtmsrd r9, 1");
}

#[test]
fn test_ins_mtsrd() {
    assert_asm!(0x7E0000A4, "mtsrd 0, r16");
}

#[test]
fn test_ins_mtsrdin() {
    assert_asm!(0x7C8040E4, "mtsrdin r4, r8");
}

#[test]
fn test_ins_mulhd() {
    assert_asm!(0x7C7CF892, "mulhd r3, r28, r31");
}

#[test]
fn test_ins_mulhdu() {
    assert_asm!(0x7CBCF812, "mulhdu r5, r28, r31");
}

#[test]
fn test_ins_mulld() {
    assert_asm!(0x7C6419D2, "mulld r3, r4, r3");
    assert_asm!(0x7d6b49d2, "mulld r11, r11, r9");
}

#[test]
fn test_ins_rfid() {
    assert_asm!(0x4c000024, "rfid");
}

#[test]
fn test_ins_rldcl() {
    assert_asm!(0x780336D0, "rldcl r3, r0, r6, 27");
    assert_asm!(0x78033010, "rotld r3, r0, r6");
}

#[test]
fn test_ins_rldcr() {
    assert_asm!(0x78A345D2, "rldcr r3, r5, r8, 23");
}

#[test]
fn test_ins_rldic() {
    assert_asm!(0x78C51928, "rldic r5, r6, 3, 36");
}

#[test]
fn test_ins_rldicl() {
    assert_asm!(0x78c50020, "rldicl r5, r6, 0, 32");
    assert_asm!(0x7bab07a0, "rldicl r11, r29, 0, 62");
}

#[test]
fn test_ins_rldicr() {
    assert_asm!(0x7883ffe6, "rldicr r3, r4, 63, 63");
    assert_asm!(0x798c37e4, "rldicr r12, r12, 6, 63");
    assert_asm!(0x798c07c6, "rldicr r12, r12, 32, 31");
    assert_asm!(0x798ccfe6, "rldicr r12, r12, 57, 63");
}

#[test]
fn test_ins_rldimi() {
    assert_asm!(0x78a3a04e, "rldimi r3, r5, 52, 1");
    assert_asm!(0x794b000e, "rldimi r11, r10, 32, 0");
    assert_asm!(0x780331CC, "rldimi r3, r0, 6, 7");
}

#[test]
fn test_ins_slbia() {
    assert_asm!(0x7c0003e4, "slbia");
}

#[test]
fn test_ins_slbie() {
    assert_asm!(0x7C002B64, "slbie r5");
}

#[test]
fn test_ins_sld() {
    assert_asm!(0x7d6a5036, "sld r10, r11, r10");
    assert_asm!(0x7D034836, "sld r3, r8, r9");
}

#[test]
fn test_ins_srad() {
    assert_asm!(0x7d0b5e34, "srad r11, r8, r11");
    assert_asm!(0x7C033634, "srad r3, r0, r6");
}

#[test]
fn test_ins_sradi() {
    assert_asm!(0x7cc4a674, "sradi r4, r6, 20");
    assert_asm!(0x7d6b0676, "sradi r11, r11, 32");
}

#[test]
fn test_ins_srd() {
    assert_asm!(0x7d0a4c36, "srd r10, r8, r9");
    assert_asm!(0x7d675436, "srd r7, r11, r10");
    assert_asm!(0x7C001C36, "srd r0, r0, r3");
    assert_asm!(0x7C600436, "srd r0, r3, r0");
}

#[test]
fn test_ins_std() {
    assert_asm!(0xfbe1fff0, "std r31, -0x10(r1)");
}

#[test]
fn test_ins_stdcx() {
    assert_asm!(0x7CA749AD, "stdcx. r5, r7, r9");
    assert_asm!(0x7fc0e9ad, "stdcx. r30, r0, r29");
}

#[test]
fn test_ins_stdu() {
    assert_asm!(0xf9690009, "stdu r11, 0x8(r9)");
    assert_asm!(0xf97ffff9, "stdu r11, -0x8(r31)");
}

#[test]
fn test_ins_stdux() {
    assert_asm!(0x7C03316A, "stdux r0, r3, r6");
    assert_asm!(0x7d5cc96a, "stdux r10, r28, r25");
}

#[test]
fn test_ins_stdx() {
    assert_asm!(0x7CA7F92A, "stdx r5, r7, r31");
    assert_asm!(0x7cc3212a, "stdx r6, r3, r4");
}

#[test]
fn test_ins_td() {
    assert_asm!(0x7DC30088, "td 14, r3, r0");
}

#[test]
fn test_ins_tdi() {
    assert_asm!(0x09830058, "tdi 12, r3, 0x58");
}
