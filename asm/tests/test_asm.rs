use ppc750cl_asm::*;
use Argument::{None, Signed as S, Unsigned as U};

macro_rules! assert_asm {
    ($mnemonic:literal, $arg1:expr, $arg2:expr, $arg3:expr, $arg4:expr, $arg5: expr, $code:literal) => {{
        assert_eq!(assemble($mnemonic, &[$arg1, $arg2, $arg3, $arg4, $arg5]).unwrap(), $code)
    }};
    ($mnemonic:literal, $arg1:expr, $arg2:expr, $arg3:expr, $arg4:expr, $code:literal) => {{
        assert_eq!(assemble($mnemonic, &[$arg1, $arg2, $arg3, $arg4, None]).unwrap(), $code)
    }};
    ($mnemonic:literal, $arg1:expr, $arg2:expr, $arg3:expr, $code:literal) => {{
        assert_eq!(assemble($mnemonic, &[$arg1, $arg2, $arg3, None, None]).unwrap(), $code)
    }};
    ($mnemonic:literal, $arg1:expr, $arg2:expr, $code:literal) => {{
        assert_eq!(assemble($mnemonic, &[$arg1, $arg2, None, None, None]).unwrap(), $code)
    }};
    ($mnemonic:literal, $arg1:expr, $code:literal) => {{
        assert_eq!(assemble($mnemonic, &[$arg1, None, None, None, None]).unwrap(), $code)
    }};
    ($mnemonic:literal, $code:literal) => {{
        assert_eq!(assemble($mnemonic, &[None, None, None, None, None]).unwrap(), $code)
    }};
}

#[test]
fn test_ins_add() {
    assert_asm!("add", U(2), U(3), U(4), 0x7C432214); // add r2, r3, r4
    assert_asm!("add.", U(7), U(6), U(5), 0x7CE62A15); // add. r7, r6, r5
    assert_asm!("addo", U(31), U(31), U(31), 0x7FFFFE14); // addo r31, r31, r31
    assert_asm!("addo.", U(28), U(29), U(30), 0x7F9DF615); // addo. r28, r29, r30
}

#[test]
fn test_ins_addc() {
    assert_asm!("addc", U(2), U(3), U(4), 0x7C432014); // addc r2, r3, r4
    assert_asm!("addc.", U(7), U(6), U(5), 0x7CE62815); // addc. r7, r6, r5
    assert_asm!("addco", U(31), U(31), U(31), 0x7FFFFC14); // addco r31, r31, r31
    assert_asm!("addco.", U(28), U(29), U(30), 0x7F9DF415); // addco. r28, r29, r30
}

#[test]
fn test_ins_addi() {
    assert_asm!("addi", U(0), U(1), U(0x140), 0x38010140); // addi r0, r1, 0x140
    assert_asm!("addi", U(0), U(4), S(-0x7000), 0x38049000); // addi r0, r4, -0x7000
    assert_asm!("subi", U(0), U(4), S(0x7000), 0x38049000); // subi r0, r4, 0x7000
    assert_asm!("li", U(5), U(0), 0x38A00000); // li r5, 0
}

#[test]
fn test_ins_b() {
    assert_asm!("b", U(0), 0x48000000); // b 0x0
    assert_asm!("b", U(4), 0x48000004); // b 0x4
    assert_asm!("bl", U(0xA5C8), 0x4800A5C9); // bl 0xa5c8
    assert_asm!("bl", U(0x23B4D8), 0x4823B4D9); // bl 0x23b4d8
    assert_asm!("bl", S(-0x1FC368), 0x4BE03C99); // bl -0x1fc368
    assert_asm!("bl", S(-0x23E5A8), 0x4BDC1A59); // bl -0x23e5a8
    assert_asm!("bla", U(0x60), 0x48000063); // bla 0x60
    assert_asm!("ba", U(0), 0x48000002); // ba 0x0
}

#[test]
fn test_ins_bc() {
    assert_asm!("bge", U(0x8), 0x40800008); // bge 0x8
    assert_asm!("bge", U(0x2350), 0x40802350); // bge 0x2350
    assert_asm!("bge", S(-0x384), 0x4080FC7C); // bge -0x384
    assert_asm!("ble", U(0xac), 0x408100AC); // ble 0xac
    assert_asm!("ble", S(-0x878), 0x4081F788); // ble -0x878
    assert_asm!("bne", U(0x1ba0), 0x40821BA0); // bne 0x1ba0
    assert_asm!("bne", S(-0x1c3c), 0x4082E3C4); // bne -0x1c3c
    assert_asm!("bne", U(1), U(0xd8), 0x408600D8); // bne cr1, 0xd8
    assert_asm!("bne", U(1), S(-0x134), 0x4086FECC); // bne cr1, -0x134
    assert_asm!("bge", U(7), U(0xc), 0x409C000C); // bge cr7, 0xc
    assert_asm!("blt", U(0xc), 0x4180000C); // blt 0xc
    assert_asm!("blt", S(-0x640), 0x4180F9C0); // blt -0x640
    assert_asm!("bgt", U(0x21c), 0x4181021C); // bgt 0x21c
    assert_asm!("bgt", S(-0x280), 0x4181FD80); // bgt -0x280
    assert_asm!("beq", U(0x2304), 0x41822304); // beq 0x2304
    assert_asm!("beq", S(-0x1c4), 0x4182FE3C); // beq -0x1c4
    assert_asm!("blt", U(1), U(0x1ac), 0x418401AC); // blt cr1, 0x1ac
    assert_asm!("blt", U(1), S(-0x31c), 0x4184FCE4); // blt cr1, -0x31c
    assert_asm!("bgt", U(1), U(0xc0), 0x418500C0); // bgt cr1, 0xc0
    assert_asm!("bgt", U(1), U(0x2e4), 0x418502E4); // bgt cr1, 0x2e4
    assert_asm!("beq", U(6), U(0x138), 0x419A0138); // beq cr6, 0x138
    assert_asm!("blt", U(7), U(0x8), 0x419C0008); // blt cr7, 0x8
    assert_asm!("bdz", S(-0x10), 0x4240FFF0); // bdz -0x10
    assert_asm!("bdnz", S(-0xaa0), 0x4200F560); // bdnz -0xaa0
    assert_asm!("bdnzf", U(1), U(0x14), 0x40010014); // bdnzf gt, 0x14
    assert_asm!("bdzfl", U(1), U(0x34), 0x40410035); // bdzfl gt, 0x34
    assert_asm!("bdztla", U(3), U(0x20), 0x41430023); // bdztla un, 0x20
    assert_asm!("bdnztla", U(8), S(-0x20), 0x4108FFE3); // bdnztla cr2lt, -0x20
    assert_asm!("bne+", U(0x8), 0x40A20008); // bne+ 0x8
}

#[test]
fn test_ins_bcctr() {
    assert_asm!("bctr", 0x4E800420); // bctr
    assert_asm!("bctrl", 0x4E800421); // bctrl
    assert_asm!("beqctr", 0x4D820420); // beqctr
    assert_asm!("bgtctrl", U(3), 0x4D8D0421); // bgtctrl cr3
    assert_asm!("beqctr+", 0x4DA20420); // beqctr+
    assert_asm!("bgtctrl+", U(6), 0x4DB90421); // bgtctrl+ cr6
}

#[test]
fn test_ins_bclr() {
    assert_asm!("bgelr", 0x4C800020); // bgelr
    assert_asm!("bgelr+", 0x4CA00020); // bgelr+
    assert_asm!("blelr", 0x4C810020); // blelr
    assert_asm!("bnelr", 0x4C820020); // bnelr
    assert_asm!("bnelr", U(7), 0x4C9E0020); // bnelr cr7
    assert_asm!("bltlr", 0x4D800020); // bltlr
    assert_asm!("bgtlr", 0x4D810020); // bgtlr
    assert_asm!("beqlr", 0x4D820020); // beqlr
    assert_asm!("beqlr", U(1), 0x4D860020); // beqlr cr1
    assert_asm!("blr", 0x4E800020); // blr
    assert_asm!("blrl", 0x4E800021); // blrl
    assert_asm!("bdnztlr", U(0), 0x4D000020); // bdnztlr lt
    assert_asm!("bdnzflrl", U(31), 0x4C1F0021); // bdnzflrl cr7un
}

#[test]
fn test_ins_cmpi() {
    assert_asm!("cmpi", U(6), U(0), U(31), U(0), 0x2F1F0000); // cmpi r6, 0, 31, 0
    assert_asm!("cmpwi", U(5), U(0xd00), 0x2C050D00); // cmpwi r5, 0xd00
    assert_asm!("cmpwi", U(6), U(31), U(0), 0x2F1F0000); // cmpwi r6, 0
}

#[test]
fn test_ins_mfspr() {
    assert_asm!("mfsrr0", U(16), 0x7E1A02A6); // mfsrr0 r16
    assert_asm!("mfspr", U(3), U(1008), 0x7C70FAA6); // mfspr r3, HID0
    assert_asm!("mfibatu", U(3), U(2), 0x7C7482A6); // mfibatu r3, 2
    assert_asm!("mfibatl", U(3), U(3), 0x7C7782A6); // mfibatl r3, 3
}

#[test]
fn test_ins_rlwimi() {
    assert_asm!("rlwimi", U(3), U(0), U(0), U(27), U(31), 0x500306FE); // rlwimi r3, r0, 0, 27, 31
    assert_asm!("rlwimi", U(3), U(0), U(5), U(21), U(26), 0x50032D74); // rlwimi r3, r0, 5, 21, 26
    assert_asm!("clrrwi.", U(0), U(0), U(0), 0x5400003F); // clrrwi. r0, r0, 0
}

#[test]
fn test_ins_rlwinm() {
    assert_asm!("rlwinm", U(0), U(0), U(0), U(16), U(25), 0x54000432); // rlwinm r0, r0, 0, 16, 25
    assert_asm!("rlwinm", U(9), U(0), U(12), U(8), U(19), 0x54096226); // rlwinm r9, r0, 12, 8, 19
    assert_asm!("rlwinm.", U(0), U(0), U(0), U(16), U(17), 0x54000423); // rlwinm. r0, r0, 0, 16, 17
    assert_asm!("slwi", U(5), U(31), U(2), 0x57E5103A); // slwi r5, r31, 2
    assert_asm!("extlwi", U(3), U(4), U(20), U(4), 0x54832026); // extlwi r3, r4, 20, 4
    assert_asm!("extrwi", U(3), U(4), U(20), U(1), 0x5483AB3E); // extrwi r3, r4, 20, 1
    assert_asm!("extrwi", U(0), U(0), U(2), U(2), 0x540027BE); // extrwi r0, r0, 2, 2
    assert_asm!("rlwinm", U(3), U(4), U(19), U(12), U(31), 0x54839B3E); // rlwinm r3, r4, 19, 12, 31
    assert_asm!("rotlwi", U(3), U(4), U(4), 0x5483203E); // rotlwi r3, r4, 4
    assert_asm!("rotrwi", U(3), U(4), U(4), 0x5483E03E); // rotrwi r3, r4, 4
    assert_asm!("clrlwi", U(4), U(3), U(16), 0x5464043E); // clrlwi r4, r3, 16
    assert_asm!("clrrwi", U(3), U(4), U(4), 0x54830036); // clrrwi r3, r4, 4
    assert_asm!("clrlslwi", U(4), U(3), U(31), U(1), 0x54640FBC); // clrlslwi r4, r3, 31, 1
    assert_asm!("clrlslwi", U(9), U(0), U(27), U(5), 0x54092DB4); // clrlslwi r9, r0, 27, 5
    assert_asm!("clrlslwi", U(9), U(0), U(20), U(12), 0x54096226); // clrlslwi r9, r0, 20, 12
}

#[test]
fn test_tw() {
    assert_asm!("tw", U(0), U(6), U(7), 0x7C063808); // tw 0, r6, r7
    assert_asm!("tweq", U(4), U(5), 0x7C842808); // tweq r4, r5
    assert_asm!("twlge", U(4), U(5), 0x7CA42808); // twlge r4, r5
    assert_asm!("trap", 0x7FE00008); // trap
}

#[test]
fn test_twi() {
    assert_asm!("twi", U(0), U(0), U(0), 0x0C000000); // twi 0, r0, 0x0
    assert_asm!("twgti", U(7), S(-0x1), 0x0D07FFFF); // twgti r7, -0x1
    assert_asm!("twllei", U(4), S(-0xff), 0x0CC4FF01); // twllei r4, -0xff
    assert_asm!("twui", U(4), U(0x3), 0x0FE40003); // twui r4, 0x3
}

#[test]
fn test_ins_xor() {
    assert_asm!("xor", U(5), U(0), U(5), 0x7C052A78); // xor r5, r0, r5
    assert_asm!("xor.", U(7), U(9), U(10), 0x7D275279); // xor. r7, r9, r10
}

#[test]
fn test_sync() {
    assert_asm!("sync", 0x7C0004AC); // sync
    assert_asm!("sync", U(0), 0x7C0004AC); // sync 0
    assert_asm!("lwsync", 0x7C2004AC); // lwsync
    assert_asm!("sync", U(1), 0x7C2004AC); // sync 1
    assert_asm!("ptesync", 0x7C4004AC); // ptesync
    assert_asm!("sync", U(2), 0x7C4004AC); // sync 2
}

#[test]
fn test_rldcl() {
    assert_asm!("rldcl", U(3), U(0), U(6), U(27), 0x780336D0); // rldcl r3, r0, r6, 27
    assert_asm!("rotld", U(3), U(0), U(6), 0x78033010); // rotld r3, r0, r6
}

#[test]
fn test_rldic() {
    assert_asm!("rldic", U(5), U(6), U(3), U(36), 0x78C51928); // rldic r5, r6, 3, 36
}

#[test]
fn test_rldicl() {
    assert_asm!("rldicl", U(5), U(6), U(0), U(32), 0x78C50020); // rldicl r5, r6, 0, 32
    assert_asm!("rldicl", U(11), U(29), U(0), U(62), 0x7BAB07A0); // rldicl r11, r29, 0, 62
}

#[test]
fn test_dss() {
    assert_asm!("dss", U(1), U(0), 0x7C20066C); // dss 1, 0
    assert_asm!("dss", U(1), 0x7C20066C); // dss 1
    assert_asm!("dss", U(0), U(1), 0x7E00066C); // dss 0, 1
    assert_asm!("dssall", 0x7E00066C); // dssall
}
