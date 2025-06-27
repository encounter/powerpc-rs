use ppc750cl::{Argument, Ins, InsIter, Opcode, GPR};

macro_rules! assert_asm {
    ($ins:ident, $disasm:literal) => {{
        assert_eq!(format!("{}", $ins.simplified()), $disasm)
    }};
    ($code:literal, $disasm:literal) => {{
        let ins = Ins::new($code);
        assert_eq!(format!("{}", ins.simplified()), $disasm)
    }};
}

macro_rules! assert_basic {
    ($ins:ident, $disasm:literal) => {{
        assert_eq!(format!("{}", $ins.basic_form()), $disasm)
    }};
    ($code:literal, $disasm:literal) => {{
        let ins = Ins::new($code);
        assert_eq!(format!("{}", ins.basic()), $disasm)
    }};
}

#[test]
fn test_ins_add() {
    assert_asm!(0x7C432214, "add r2, r3, r4");
    assert_asm!(0x7CE62A15, "add. r7, r6, r5");
    assert_asm!(0x7FFFFE14, "addo r31, r31, r31");
    assert_asm!(0x7F9DF615, "addo. r28, r29, r30");
}

#[test]
fn test_ins_addc() {
    let ins = Ins::new(0x7c002014);
    assert_eq!(ins.op, Opcode::Addc);
    // assert_eq!(ins.fields(), vec![rD(GPR(0)), rA(GPR(0)), rB(GPR(4))]);
    assert_asm!(ins, "addc r0, r0, r4");
    assert_asm!(0x7C432014, "addc r2, r3, r4");
    assert_asm!(0x7CE62815, "addc. r7, r6, r5");
    assert_asm!(0x7FFFFC14, "addco r31, r31, r31");
    assert_asm!(0x7F9DF415, "addco. r28, r29, r30");
}

#[test]
fn test_ins_addi() {
    let ins = Ins::new(0x38010140);
    assert_eq!(ins.op, Opcode::Addi);
    // assert_eq!(
    //     ins.fields(),
    //     vec![rD(GPR(0)), rA(GPR(1)), simm(Simm(0x140))]
    // );
    assert_eq!(
        ins.defs(),
        [Argument::GPR(GPR(0)), Argument::None, Argument::None, Argument::None, Argument::None]
    );
    assert_eq!(
        ins.uses(),
        [Argument::GPR(GPR(1)), Argument::None, Argument::None, Argument::None, Argument::None]
    );
    assert_asm!(ins, "addi r0, r1, 0x140");

    assert_asm!(0x38010008, "addi r0, r1, 0x8");
    assert_asm!(0x38010010, "addi r0, r1, 0x10");
    assert_asm!(0x38010018, "addi r0, r1, 0x18");
    assert_asm!(0x38010140, "addi r0, r1, 0x140");
    assert_asm!(0x38049000, "subi r0, r4, 0x7000");
    assert_asm!(0x38a00000, "li r5, 0x0");
    assert_basic!(0x38a00000, "addi r5, r0, 0x0");
}

#[test]
fn test_ins_adde() {
    assert_asm!(0x7c006114, "adde r0, r0, r12");
    assert_asm!(0x7C432114, "adde r2, r3, r4");
    assert_asm!(0x7CE62915, "adde. r7, r6, r5");
    assert_asm!(0x7FFFFD14, "addeo r31, r31, r31");
    assert_asm!(0x7F9DF515, "addeo. r28, r29, r30");
}

#[test]
fn test_ins_addic() {
    assert_asm!(0x3060ffff, "subic r3, r0, 0x1");
    assert_asm!(0x30840800, "addic r4, r4, 0x800");
    assert_asm!(0x30a50008, "addic r5, r5, 0x8");
    assert_asm!(0x37DF001C, "addic. r30, r31, 0x1c");
    assert_asm!(0x37E06278, "addic. r31, r0, 0x6278");
    assert_asm!(0x37E3FFFF, "subic. r31, r3, 0x1");
}

#[test]
fn test_ins_addis() {
    assert_asm!(0x3C030000, "addis r0, r3, 0x0");
    assert_asm!(0x3C038000, "addis r0, r3, 0x8000");
    assert_asm!(0x3D00EFCE, "lis r8, 0xefce");
}

#[test]
fn test_ins_addze() {
    assert_asm!(0x7C000194, "addze r0, r0");
}

#[test]
fn test_ins_and() {
    assert_asm!(0x7C001838, "and r0, r0, r3");
    assert_asm!(0x7C001839, "and. r0, r0, r3");
}

#[test]
fn test_ins_andc() {
    assert_asm!(0x7C001878, "andc r0, r0, r3");
}

#[test]
fn test_ins_andi_() {
    assert_asm!(0x70000009, "andi. r0, r0, 0x9");
}

#[test]
fn test_ins_andis_() {
    assert_asm!(0x77c802ff, "andis. r8, r30, 0x2ff");
}

#[test]
fn test_ins_b() {
    assert_asm!(0x48000000, "b 0x0");
    assert_asm!(0x48000004, "b 0x4");
    assert_asm!(0x4800A5C9, "bl 0xa5c8");
    assert_asm!(0x4823B4D9, "bl 0x23b4d8");
    assert_asm!(0x4BE03C99, "bl -0x1fc368");
    assert_asm!(0x4BDC1A59, "bl -0x23e5a8");
    assert_asm!(0x48000063, "bla 0x60");
    assert_asm!(0x48000002, "ba 0x0");
}

#[test]
fn test_ins_bc() {
    assert_asm!(0x40800008, "bge 0x8");
    assert_asm!(0x40802350, "bge 0x2350");
    assert_asm!(0x4080FC7C, "bge -0x384");
    assert_asm!(0x408100AC, "ble 0xac");
    assert_asm!(0x4081F788, "ble -0x878");
    assert_asm!(0x40821BA0, "bne 0x1ba0");
    assert_asm!(0x4082E3C4, "bne -0x1c3c");
    assert_asm!(0x408600D8, "bne cr1, 0xd8");
    assert_asm!(0x4086FECC, "bne cr1, -0x134");
    assert_asm!(0x409C000C, "bge cr7, 0xc");
    assert_asm!(0x4180000C, "blt 0xc");
    assert_asm!(0x4180F9C0, "blt -0x640");
    assert_asm!(0x4181021C, "bgt 0x21c");
    assert_asm!(0x4181FD80, "bgt -0x280");
    assert_asm!(0x41822304, "beq 0x2304");
    assert_asm!(0x4182FE3C, "beq -0x1c4");
    assert_asm!(0x418401AC, "blt cr1, 0x1ac");
    assert_asm!(0x4184FCE4, "blt cr1, -0x31c");
    assert_asm!(0x418500C0, "bgt cr1, 0xc0");
    assert_asm!(0x418502E4, "bgt cr1, 0x2e4");
    assert_asm!(0x419A0138, "beq cr6, 0x138");
    assert_asm!(0x419C0008, "blt cr7, 0x8");
    assert_asm!(0x4240FFF0, "bdz -0x10");
    assert_asm!(0x4200F560, "bdnz -0xaa0");
    assert_asm!(0x40010014, "bdnzf gt, 0x14");
    assert_asm!(0x40410035, "bdzfl gt, 0x34");
    assert_asm!(0x41430023, "bdztla un, 0x20");
    assert_asm!(0x4108FFE3, "bdnztla cr2lt, -0x20");
    assert_asm!(0x40A20008, "bne+ 0x8");
}

#[test]
fn test_ins_bcctr() {
    assert_asm!(0x4E800420, "bctr");
    assert_asm!(0x4E800421, "bctrl");
    assert_asm!(0x4D820420, "beqctr");
    assert_asm!(0x4D8D0421, "bgtctrl cr3");
    assert_asm!(0x4DA20420, "beqctr+");
    assert_asm!(0x4DB90421, "bgtctrl+ cr6");
}

#[test]
fn test_ins_bclr() {
    assert_asm!(0x4C800020, "bgelr");
    assert_asm!(0x4CA00020, "bgelr+");
    assert_asm!(0x4C810020, "blelr");
    assert_asm!(0x4C820020, "bnelr");
    assert_asm!(0x4C9E0020, "bnelr cr7");
    assert_asm!(0x4D800020, "bltlr");
    assert_asm!(0x4D810020, "bgtlr");
    assert_asm!(0x4D820020, "beqlr");
    assert_asm!(0x4D860020, "beqlr cr1");
    assert_asm!(0x4E800020, "blr");
    assert_asm!(0x4E800021, "blrl");
    assert_asm!(0x4D000020, "bdnztlr lt");
    assert_asm!(0x4C1F0021, "bdnzflrl cr7un");
}

#[test]
fn test_ins_cmp() {
    assert_asm!(0x7C030000, "cmpw r3, r0");
}

#[test]
fn test_ins_cmpi() {
    assert_asm!(0x2C050D00, "cmpwi r5, 0xd00");
    assert_asm!(0x2F1F0000, "cmpwi cr6, r31, 0x0");
}

#[test]
fn test_ins_cmpl() {
    assert_asm!(0x7C9A2040, "cmplw cr1, r26, r4");
    assert_asm!(0x7f295840, "cmpld cr6, r9, r11");
}

#[test]
fn test_ins_cmpli() {
    assert_asm!(0x2803FFF3, "cmplwi r3, 0xfff3");
    assert_asm!(0x2884F8F0, "cmplwi cr1, r4, 0xf8f0");
}

#[test]
fn test_ins_cntlzd() {
    assert_asm!(0x7CA30074, "cntlzd r3, r5");
}

#[test]
fn test_ins_cntlzw() {
    assert_asm!(0x7C030034, "cntlzw r3, r0");
}

#[test]
fn test_ins_crand() {
    assert_asm!(0x4C853202, "crand cr1lt, cr1gt, cr1eq");
}

#[test]
fn test_ins_crandc() {
    assert_asm!(0x4C642902, "crandc un, cr1lt, cr1gt");
}

#[test]
fn test_ins_creqv() {
    assert_asm!(0x4CE00A42, "creqv cr1un, lt, gt");
}

#[test]
fn test_ins_crnand() {
    assert_asm!(0x4C2219C2, "crnand gt, eq, un");
}

#[test]
fn test_ins_cror() {
    assert_asm!(0x4C411382, "cror eq, gt, eq");
    assert_asm!(0x4CA63B82, "cror cr1gt, cr1eq, cr1un");
}

#[test]
fn test_ins_crorc() {
    assert_asm!(0x4C432342, "crorc eq, un, cr1lt");
}

#[test]
fn test_ins_crnor() {
    assert_asm!(0x4C011042, "crnor lt, gt, eq");
    assert_asm!(0x4CA63042, "crnot cr1gt, cr1eq");
}

#[test]
fn test_ins_crxor() {
    assert_asm!(0x4CC70182, "crxor cr1eq, cr1un, lt");
}

#[test]
fn test_ins_dcbf() {
    assert_asm!(0x7C0028AC, "dcbf r0, r5");
}

#[test]
fn test_ins_dcbi() {
    assert_asm!(0x7C001BAC, "dcbi r0, r3");
}

#[test]
fn test_ins_dcbst() {
    assert_asm!(0x7C00286C, "dcbst r0, r5");
}

#[test]
fn test_ins_dcbt() {
    assert_asm!(0x7C001A2C, "dcbt r0, r3");
}

#[test]
fn test_ins_dcbz() {
    assert_asm!(0x7C001FEC, "dcbz r0, r3");
}

#[test]
fn test_ins_dcbz_l() {
    assert_asm!(0x10061FEC, "dcbz_l r6, r3");
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
fn test_ins_divw() {
    assert_asm!(0x7C8073D6, "divw r4, r0, r14");
}

#[test]
fn test_ins_divwu() {
    assert_asm!(0x7C69E396, "divwu r3, r9, r28");
}

#[test]
fn test_ins_extsb() {
    assert_asm!(0x7C650774, "extsb r5, r3");
    assert_asm!(0x7C650775, "extsb. r5, r3");
}

#[test]
fn test_ins_extsh() {
    assert_asm!(0x7C000734, "extsh r0, r0");
    assert_asm!(0x7C000735, "extsh. r0, r0");
}

#[test]
fn test_ins_extsw() {
    assert_asm!(0x7CC307B4, "extsw r3, r6");
    assert_asm!(0x7CC307B5, "extsw. r3, r6");
}

#[test]
fn test_ins_fabs() {
    assert_asm!(0xFC000A10, "fabs f0, f1");
}

#[test]
fn test_ins_fadd() {
    assert_asm!(0xFC00282A, "fadd f0, f0, f5");
}

#[test]
fn test_ins_fadds() {
    assert_asm!(0xEC41602A, "fadds f2, f1, f12");
}

#[test]
fn test_ins_fcfid() {
    assert_asm!(0xFC602E9C, "fcfid f3, f5");
}

#[test]
fn test_ins_fcmpo() {
    assert_asm!(0xFC00C840, "fcmpo cr0, f0, f25");
}

#[test]
fn test_ins_fcmpu() {
    assert_asm!(0xFC00D000, "fcmpu cr0, f0, f26");
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
fn test_ins_fctiwz() {
    assert_asm!(0xFC20001E, "fctiwz f1, f0");
}

#[test]
fn test_ins_fdiv() {
    assert_asm!(0xFC200024, "fdiv f1, f0, f0");
}

#[test]
fn test_ins_fdivs() {
    assert_asm!(0xEC01F824, "fdivs f0, f1, f31");
}

#[test]
fn test_ins_fmadds() {
    assert_asm!(0xEC0200FA, "fmadds f0, f2, f3, f0");
}

#[test]
fn test_ins_fmsub() {
    assert_asm!(0xFC000028, "fsub f0, f0, f0");
}

#[test]
fn test_ins_fmsubs() {
    assert_asm!(0xEC00B828, "fsubs f0, f0, f23");
}

#[test]
fn test_ins_fmul() {
    assert_asm!(0xFC0000B2, "fmul f0, f0, f2");
    assert_asm!(0xFC0000F2, "fmul f0, f0, f3");
}

#[test]
fn test_ins_fmuls() {
    assert_asm!(0xEC0007B2, "fmuls f0, f0, f30");
}

#[test]
fn test_ins_fneg() {
    assert_asm!(0xFCE00050, "fneg f7, f0");
}

#[test]
fn test_ins_fnmsub() {
    assert_asm!(0xFCC640BC, "fnmsub f6, f6, f2, f8");
}

#[test]
fn test_ins_fnmsubs() {
    assert_asm!(0xEC022B3C, "fnmsubs f0, f2, f12, f5");
}

#[test]
fn test_ins_fres() {
    assert_asm!(0xEC000830, "fres f0, f1");
}

#[test]
fn test_ins_frsp() {
    assert_asm!(0xFC000018, "frsp f0, f0");
}

#[test]
fn test_ins_frsqrte() {
    assert_asm!(0xFC000834, "frsqrte f0, f1");
}

#[test]
fn test_ins_fsel() {
    assert_asm!(0xFC01F82E, "fsel f0, f1, f0, f31");
}

#[test]
fn test_ins_fsub() {
    assert_asm!(0xFC000828, "fsub f0, f0, f1");
}

#[test]
fn test_ins_fsubs() {
    assert_asm!(0xEC000828, "fsubs f0, f0, f1");
}

#[test]
fn test_ins_icbi() {
    assert_asm!(0x7C001FAC, "icbi r0, r3");
}

#[test]
fn test_ins_isync() {
    assert_asm!(0x4C00012C, "isync");
}

#[test]
fn test_ins_lbz() {
    assert_asm!(0x880104CC, "lbz r0, 0x4cc(r1)");
    assert_asm!(0x8802801B, "lbz r0, -0x7fe5(r2)");
}

#[test]
fn test_ins_lbzu() {
    assert_asm!(0x8D9DCA10, "lbzu r12, -0x35f0(r29)");
    assert_asm!(0x8E3053EC, "lbzu r17, 0x53ec(r16)");
}

#[test]
fn test_ins_lbzux() {
    assert_asm!(0x7C0400EE, "lbzux r0, r4, r0");
}

#[test]
fn test_ins_lbzx() {
    assert_asm!(0x7C0300AE, "lbzx r0, r3, r0");
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
fn test_ins_lfd() {
    assert_asm!(0xC80140C8, "lfd f0, 0x40c8(r1)");
    assert_asm!(0xC8028090, "lfd f0, -0x7f70(r2)");
}

#[test]
fn test_ins_lfdu() {
    assert_asm!(0xCC03FFC0, "lfdu f0, -0x40(r3)");
}

#[test]
fn test_ins_lfdx() {
    assert_asm!(0x7C0404AE, "lfdx f0, r4, r0");
}

#[test]
fn test_ins_lfs() {
    assert_asm!(0xC001027C, "lfs f0, 0x27c(r1)");
    assert_asm!(0xC0028000, "lfs f0, -0x8000(r2)");
}

#[test]
fn test_ins_lfsu() {
    assert_asm!(0xC404FFF4, "lfsu f0, -0xc(r4)");
    assert_asm!(0xC4170084, "lfsu f0, 0x84(r23)");
}

#[test]
fn test_ins_lfsux() {
    assert_asm!(0x7C03846E, "lfsux f0, r3, r16");
}

#[test]
fn test_ins_lfsx() {
    assert_asm!(0x7C03042E, "lfsx f0, r3, r0");
}

#[test]
fn test_ins_lha() {
    assert_asm!(0xA861000E, "lha r3, 0xe(r1)");
    assert_asm!(0xA80D9F64, "lha r0, -0x609c(r13)");
}

#[test]
fn test_ins_lhau() {
    assert_asm!(0xAC060006, "lhau r0, 0x6(r6)");
    assert_asm!(0xAC06FFFA, "lhau r0, -0x6(r6)");
}

#[test]
fn test_ins_lhax() {
    assert_asm!(0x7C0402AE, "lhax r0, r4, r0");
}

#[test]
fn test_ins_lhz() {
    assert_asm!(0xA00104D6, "lhz r0, 0x4d6(r1)");
    assert_asm!(0xA00296DA, "lhz r0, -0x6926(r2)");
}

#[test]
fn test_ins_lhzu() {
    assert_asm!(0xA40A0004, "lhzu r0, 0x4(r10)");
}

#[test]
fn test_ins_lhzux() {
    assert_asm!(0x7C04026E, "lhzux r0, r4, r0");
}

#[test]
fn test_ins_lhzx() {
    assert_asm!(0x7C03022E, "lhzx r0, r3, r0");
}

#[test]
fn test_ins_lmw() {
    assert_asm!(0xBB210444, "lmw r25, 0x444(r1)");
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
fn test_ins_lwbrx() {
    assert_asm!(0x7D80242C, "lwbrx r12, r0, r4");
}

#[test]
fn test_ins_lwz() {
    assert_asm!(0x800294F4, "lwz r0, -0x6b0c(r2)");
    assert_asm!(0x80011254, "lwz r0, 0x1254(r1)");
}

#[test]
fn test_ins_lwzu() {
    assert_asm!(0x84038608, "lwzu r0, -0x79f8(r3)");
    assert_asm!(0x873E5058, "lwzu r25, 0x5058(r30)");
}

#[test]
fn test_ins_lwzux() {
    assert_asm!(0x7C03006E, "lwzux r0, r3, r0");
}

#[test]
fn test_ins_lwzx() {
    assert_asm!(0x7C03002E, "lwzx r0, r3, r0");
}

#[test]
fn test_ins_mcrf() {
    assert_asm!(0x4E1C0000, "mcrf cr4, cr7");
}

#[test]
fn test_ins_mcrfs() {
    assert_asm!(0xFE1C0080, "mcrfs cr4, cr7");
}

#[test]
fn test_ins_mcrxr() {
    assert_asm!(0x7F800400, "mcrxr cr7");
}

#[test]
fn test_ins_mfcr() {
    assert_asm!(0x7C000026, "mfcr r0");
}

#[test]
fn test_ins_mffs() {
    assert_asm!(0xFC00048E, "mffs f0");
}

#[test]
fn test_ins_mfmsr() {
    assert_asm!(0x7C0000A6, "mfmsr r0");
}

#[test]
fn test_ins_mfspr() {
    assert_asm!(0x7E1A02A6, "mfsrr0 r16");
    assert_asm!(0x7C70FAA6, "mfspr r3, HID0");
    assert_asm!(0x7C7482A6, "mfibatu r3, 2");
    assert_asm!(0x7C7782A6, "mfibatl r3, 3");
}

#[test]
fn test_ins_mfsr() {
    assert_asm!(0x7E0004A6, "mfsr r16, 0");
}

#[test]
fn test_ins_mftb() {
    assert_asm!(0x7C8C42E6, "mftb r4, 268");
}

#[test]
fn test_ins_mtcrf() {
    assert_asm!(0x7C6FF120, "mtcrf 255, r3");
}

#[test]
fn test_ins_mtfsb0() {
    assert_asm!(0xFFA0008C, "mtfsb0 cr7gt")
}

#[test]
fn test_ins_mtfsb1() {
    assert_asm!(0xFFA0004C, "mtfsb1 cr7gt");
}

#[test]
fn test_ins_mtfsf() {
    assert_asm!(0xFDFE058E, "mtfsf 255, f0");
    assert_asm!(0xFDFEFD8E, "mtfsf 255, f31");
}

#[test]
fn test_ins_mtmsr() {
    assert_asm!(0x7C000124, "mtmsr r0");
}

#[test]
fn test_ins_mtmsrd() {
    assert_asm!(0x7C000164, "mtmsrd r0, 0");
    assert_asm!(0x7D210164, "mtmsrd r9, 1");
}

#[test]
fn test_ins_mtspr() {
    assert_asm!(0x7E75FBA6, "mtspr DABR, r19");
    assert_asm!(0x7C70FBA6, "mtspr HID0, r3");
    assert_asm!(0x7C7603A6, "mtdec r3");
    assert_asm!(0x7C7043A6, "mtsprg 0, r3");
    assert_asm!(0x7C7143A6, "mtsprg 1, r3");
    assert_asm!(0x7C7343A6, "mtsprg 3, r3");
    assert_asm!(0x7C7083A6, "mtibatu 0, r3");
    assert_asm!(0x7C7483A6, "mtibatu 2, r3");
    assert_asm!(0x7C7783A6, "mtibatl 3, r3");
    assert_asm!(0x7C7D83A6, "mtdbatl 2, r3");
}

#[test]
fn test_ins_mtsr() {
    assert_asm!(0x7E0001A4, "mtsr 0, r16");
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
fn test_ins_mulhw() {
    assert_asm!(0x7C7F2096, "mulhw r3, r31, r4");
}

#[test]
fn test_ins_mulhwu() {
    assert_asm!(0x7C7D0016, "mulhwu r3, r29, r0");
}

#[test]
fn test_ins_mulld() {
    assert_asm!(0x7C6419D2, "mulld r3, r4, r3");
    assert_asm!(0x7d6b49d2, "mulld r11, r11, r9");
}

#[test]
fn test_ins_mulli() {
    assert_asm!(0x1C001880, "mulli r0, r0, 0x1880");
    assert_asm!(0x1FBD0030, "mulli r29, r29, 0x30");
}

#[test]
fn test_ins_mullw() {
    assert_asm!(0x7C7D01D6, "mullw r3, r29, r0");
}

#[test]
fn test_ins_nand() {
    assert_asm!(0x7C7D03B8, "nand r29, r3, r0");
}

#[test]
fn test_ins_neg() {
    assert_asm!(0x7C0600D0, "neg r0, r6");
    assert_asm!(0x7C4A00D1, "neg. r2, r10");
    assert_asm!(0x7CC104D0, "nego r6, r1");
    assert_asm!(0x7DF004D1, "nego. r15, r16");
}

#[test]
fn test_ins_nor() {
    assert_asm!(0x7C0500F8, "nor r5, r0, r0");
}

#[test]
fn test_ins_or() {
    assert_asm!(0x7C04DB78, "or r4, r0, r27");
}

#[test]
fn test_ins_orc() {
    assert_asm!(0x7C042338, "orc r4, r0, r4");
}

#[test]
fn test_ins_ori() {
    assert_asm!(0x60002204, "ori r0, r0, 0x2204");
}

#[test]
fn test_ins_oris() {
    assert_asm!(0x67A06800, "oris r0, r29, 0x6800");
}

// #[test]
// fn test_ins_psq_l() {
//     assert_asm!(0xE02500AC, "psq_l f1, 0xac(r5), 0, qr0");
// }

// #[test]
// fn test_ins_psq_lu() {
//     assert_asm!(0xE5435010, "psq_lu f10, 0x10(r3), 0, qr5");
// }

// #[test]
// fn test_ins_psq_lx() {
//     let ins = Ins::new(0x1000000C);
//     assert_eq!(ins.op, Opcode::PsqLx);
//     // assert_eq!(
//     //     ins.fields(),
//     //     vec![
//     //         frD(FPR(0)),
//     //         rA(GPR(0)),
//     //         rB(GPR(0)),
//     //         ps_WX(OpaqueU(0)),
//     //         ps_IX(GQR(0)),
//     //     ]
//     // );
//     assert_eq!(
//         ins.defs(),
//         [Argument::FPR(FPR(0)), Argument::None, Argument::None, Argument::None, Argument::None]
//     );
//     assert_eq!(
//         ins.uses(),
//         [Argument::None, Argument::GPR(GPR(0)), Argument::None, Argument::None, Argument::None]
//     );

//     assert_asm!(0x1000000C, "psq_lx f0, r0, r0, 0, qr0");
// }

// #[test]
// fn test_ins_psq_st() {
//     assert_asm!(0xF1230210, "psq_st f9, 0x210(r3), 0, qr0");
//     assert_asm!(0xF1238008, "psq_st f9, 0x8(r3), 1, qr0");
// }

// #[test]
// fn test_ins_psq_stu() {
//     assert_asm!(0xF40A0020, "psq_stu f0, 0x20(r10), 0, qr0");
// }

// #[test]
// fn test_ins_psq_stx() {
//     assert_asm!(0x13E1000E, "psq_stx f31, r1, r0, 0, qr0");
// }

// #[test]
// fn test_ins_ps_abs() {
//     assert_asm!(0x10A03210, "ps_abs f5, f6");
// }

// #[test]
// fn test_ins_ps_add() {
//     assert_asm!(0x1006382A, "ps_add f0, f6, f7");
// }

// #[test]
// fn test_ins_ps_cmpo0() {
//     assert_asm!(0x10070840, "ps_cmpo0 cr0, f7, f1");
// }

// #[test]
// fn test_ins_ps_cmpu0() {
//     assert_asm!(0x10003000, "ps_cmpu0 cr0, f0, f6");
// }

// #[test]
// fn test_ins_ps_cmpu1() {
//     assert_asm!(0x10003080, "ps_cmpu1 cr0, f0, f6");
// }

// #[test]
// fn test_ins_ps_madd() {
//     assert_asm!(0x112141FA, "ps_madd f9, f1, f7, f8");
// }

// #[test]
// fn test_ins_ps_madds0() {
//     assert_asm!(0x10AC299C, "ps_madds0 f5, f12, f6, f5");
// }

// #[test]
// fn test_ins_ps_madds1() {
//     assert_asm!(0x110640DE, "ps_madds1 f8, f6, f3, f8");
// }

// #[test]
// fn test_ins_ps_merge00() {
//     assert_asm!(0x10400420, "ps_merge00 f2, f0, f0");
// }

// #[test]
// fn test_ins_ps_merge01() {
//     assert_asm!(0x10400C60, "ps_merge01 f2, f0, f1");
// }

// #[test]
// fn test_ins_ps_merge10() {
//     assert_asm!(0x104004A0, "ps_merge10 f2, f0, f0");
// }

// #[test]
// fn test_ins_ps_merge11() {
//     assert_asm!(0x10AA14E0, "ps_merge11 f5, f10, f2");
// }

// #[test]
// fn test_ins_ps_mr() {
//     assert_asm!(0x10200090, "ps_mr f1, f0");
// }

// #[test]
// fn test_ins_ps_msub() {
//     assert_asm!(0x10A53778, "ps_msub f5, f5, f29, f6");
// }

// #[test]
// fn test_ins_ps_mul() {
//     assert_asm!(0x10000032, "ps_mul f0, f0, f0");
// }

// #[test]
// fn test_ins_ps_muls0() {
//     assert_asm!(0x100002D8, "ps_muls0 f0, f0, f11");
// }

// #[test]
// fn test_ins_ps_muls1() {
//     assert_asm!(0x10A2005A, "ps_muls1 f5, f2, f1");
// }

// #[test]
// fn test_ins_ps_nabs() {
//     assert_asm!(0x10803210, "ps_abs f4, f6");
// }

// #[test]
// fn test_ins_ps_neg() {
//     assert_asm!(0x10E03850, "ps_neg f7, f7");
// }

// #[test]
// fn test_ins_ps_nmadd() {
//     assert_asm!(0x10CB30FE, "ps_nmadd f6, f11, f3, f6");
// }

// #[test]
// fn test_ins_ps_nmsub() {
//     assert_asm!(0x107E083C, "ps_nmsub f3, f30, f0, f1");
// }

// #[test]
// fn test_ins_ps_sel() {
//     assert_asm!(0x106428EE, "ps_sel f3, f4, f3, f5");
// }

// #[test]
// fn test_ins_ps_sub() {
//     assert_asm!(0x10A92828, "ps_sub f5, f9, f5");
// }

// #[test]
// fn test_ins_ps_sum0() {
//     assert_asm!(0x10230854, "ps_sum0 f1, f3, f1, f1");
// }

// #[test]
// fn test_ins_ps_sum1() {
//     assert_asm!(0x10A12956, "ps_sum1 f5, f1, f5, f5");
// }

#[test]
fn test_ins_rfi() {
    assert_asm!(0x4C000064, "rfi");
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
fn test_ins_rlwimi() {
    assert_asm!(0x500306FE, "rlwimi r3, r0, 0, 27, 31");
    assert_asm!(0x50032D74, "rlwimi r3, r0, 5, 21, 26");
    assert_asm!(0x5400003F, "clrrwi. r0, r0, 0");
}

#[test]
fn test_ins_rlwinm() {
    assert_asm!(0x54000423, "rlwinm. r0, r0, 0, 16, 17");
    assert_asm!(0x54000432, "rlwinm r0, r0, 0, 16, 25");
    assert_basic!(0x54096226, "rlwinm r9, r0, 12, 8, 19");

    // mnemonics
    assert_asm!(0x57E5103A, "slwi r5, r31, 2");
    assert_asm!(0x54832026, "extlwi r3, r4, 20, 4");
    assert_asm!(0x5483AB3E, "extrwi r3, r4, 20, 1");
    assert_asm!(0x540027BE, "extrwi r0, r0, 2, 2");
    assert_asm!(0x54839B3E, "rlwinm r3, r4, 19, 12, 31");
    assert_asm!(0x5483203E, "rotlwi r3, r4, 4");
    assert_asm!(0x5483E03E, "rotrwi r3, r4, 4");
    assert_asm!(0x5464043E, "clrlwi r4, r3, 16");
    assert_asm!(0x54830036, "clrrwi r3, r4, 4");
    assert_asm!(0x54640FBC, "clrlslwi r4, r3, 31, 1");
    assert_asm!(0x54092DB4, "clrlslwi r9, r0, 27, 5");
    assert_asm!(0x54096226, "clrlslwi r9, r0, 20, 12");
}

#[test]
fn test_ins_rlwnm() {
    assert_asm!(0x5D6A67FE, "rlwnm r10, r11, r12, 31, 31");
    assert_asm!(0x5FC52EFE, "rlwnm r5, r30, r5, 27, 31");
    assert_asm!(0x5FC5283F, "rotlw. r5, r30, r5");
}

#[test]
fn test_ins_sc() {
    assert_asm!(0x44000002, "sc");
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
fn test_ins_slw() {
    assert_asm!(0x7C042830, "slw r4, r0, r5");
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
fn test_ins_sraw() {
    assert_asm!(0x7C043E30, "sraw r4, r0, r7");
}

#[test]
fn test_ins_srawi() {
    assert_asm!(0x7C000E70, "srawi r0, r0, 1");
    assert_asm!(0x7C001670, "srawi r0, r0, 2");
}

#[test]
fn test_ins_srd() {
    assert_asm!(0x7d0a4c36, "srd r10, r8, r9");
    assert_asm!(0x7d675436, "srd r7, r11, r10");
    assert_asm!(0x7C001C36, "srd r0, r0, r3");
    assert_asm!(0x7C600436, "srd r0, r3, r0");
}

#[test]
fn test_ins_srw() {
    assert_asm!(0x7C001C30, "srw r0, r0, r3");
    assert_asm!(0x7C600430, "srw r0, r3, r0");
}

#[test]
fn test_ins_stb() {
    assert_asm!(0x980105EC, "stb r0, 0x5ec(r1)");
    assert_asm!(0x98030000, "stb r0, 0x0(r3)");
}

#[test]
fn test_ins_stbu() {
    assert_asm!(0x9D2A7428, "stbu r9, 0x7428(r10)");
    assert_asm!(0x9D66FFFF, "stbu r11, -0x1(r6)");
}

#[test]
fn test_ins_stbux() {
    assert_asm!(0x7C08F9EE, "stbux r0, r8, r31");
}

#[test]
fn test_ins_stbx() {
    assert_asm!(0x7C03F9AE, "stbx r0, r3, r31");
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
fn test_ins_stfd() {
    assert_asm!(0xD80D97B0, "stfd f0, -0x6850(r13)");
    assert_asm!(0xD8050090, "stfd f0, 0x90(r5)");
}

#[test]
fn test_ins_stfdu() {
    assert_asm!(0xDC24FFC0, "stfdu f1, -0x40(r4)");
}

#[test]
fn test_ins_stfdx() {
    assert_asm!(0x7C4405AE, "stfdx f2, r4, r0");
}

#[test]
fn test_ins_stfs() {
    assert_asm!(0xD003086C, "stfs f0, 0x86c(r3)");
    assert_asm!(0xD0038000, "stfs f0, -0x8000(r3)");
}

#[test]
fn test_ins_stfsx() {
    assert_asm!(0x7C465D2E, "stfsx f2, r6, r11");
}

#[test]
fn test_ins_sth() {
    assert_asm!(0xB0038A7C, "sth r0, -0x7584(r3)");
    assert_asm!(0xB0035036, "sth r0, 0x5036(r3)");
}

#[test]
fn test_ins_sthbrx() {
    assert_asm!(0x7C60072C, "sthbrx r3, r0, r0");
}

#[test]
fn test_ins_sthu() {
    assert_asm!(0xB4055B88, "sthu r0, 0x5b88(r5)");
}

#[test]
fn test_ins_sthux() {
    assert_asm!(0x7C03236E, "sthux r0, r3, r4");
}

#[test]
fn test_ins_sthx() {
    assert_asm!(0x7C1C2B2E, "sthx r0, r28, r5");
}

#[test]
fn test_ins_stmw() {
    assert_asm!(0xBFA202A4, "stmw r29, 0x2a4(r2)");
}

#[test]
fn test_ins_stw() {
    assert_asm!(0x900140CC, "stw r0, 0x40cc(r1)");
    assert_asm!(0x9003FFBC, "stw r0, -0x44(r3)");
}

#[test]
fn test_ins_stwbrx() {
    assert_asm!(0x7C00FD2C, "stwbrx r0, r0, r31");
}

#[test]
fn test_ins_stwu() {
    assert_asm!(0x9421EBC0, "stwu r1, -0x1440(r1)");
}

#[test]
fn test_ins_stwux() {
    assert_asm!(0x7C01B96E, "stwux r0, r1, r23");
}

#[test]
fn test_ins_stwx() {
    assert_asm!(0x7C03212E, "stwx r0, r3, r4");
}

#[test]
fn test_ins_subf() {
    assert_asm!(0x7C051850, "subf r0, r5, r3");
    assert_asm!(0x7C051851, "subf. r0, r5, r3");
}

#[test]
fn test_ins_subfc() {
    assert_asm!(0x7C040010, "subfc r0, r4, r0");
}

#[test]
fn test_ins_subfe() {
    assert_asm!(0x7C030110, "subfe r0, r3, r0");
}

#[test]
fn test_ins_subfic() {
    assert_asm!(0x200602FF, "subfic r0, r6, 0x2ff");
}

#[test]
fn test_ins_subfze() {
    assert_asm!(0x7C000190, "subfze r0, r0");
}

#[test]
fn test_ins_sync() {
    assert_basic!(0x7c0004ac, "sync 0");
    assert_basic!(0x7c2004ac, "sync 1");
    assert_basic!(0x7c4004ac, "sync 2");
    assert_asm!(0x7c0004ac, "sync");
    assert_asm!(0x7c2004ac, "lwsync");
    assert_asm!(0x7c4004Ac, "ptesync");
}

#[test]
fn test_ins_td() {
    assert_asm!(0x7DC30088, "td 14, r3, r0");
}

#[test]
fn test_ins_tdi() {
    assert_asm!(0x09830058, "tdi 12, r3, 0x58");
}

#[test]
fn test_tlbie() {
    assert_asm!(0x7C001A64, "tlbie r3");
}

#[test]
fn test_tlbsync() {
    assert_asm!(0x7C00046C, "tlbsync");
}

#[test]
fn test_tw() {
    assert_asm!(0x7C063808, "tw 0, r6, r7");
    assert_asm!(0x7C842808, "tweq r4, r5");
    assert_asm!(0x7CA42808, "twlge r4, r5");
    assert_asm!(0x7FE00008, "trap");
}

#[test]
fn test_twi() {
    assert_asm!(0x0C000000, "twi 0, r0, 0x0");
    assert_asm!(0x0D07FFFF, "twgti r7, -0x1");
    assert_asm!(0x0CC4FF01, "twllei r4, -0xff");
    assert_asm!(0x0FE40003, "twui r4, 0x3");
}

#[test]
fn test_ins_xor() {
    assert_asm!(0x7C052A78, "xor r5, r0, r5");
    assert_asm!(0x7D275279, "xor. r7, r9, r10");
}

#[test]
fn test_ins_xori() {
    assert_asm!(0x68E71021, "xori r7, r7, 0x1021");
}

#[test]
fn test_ins_xoris() {
    assert_asm!(0x6E3D8000, "xoris r29, r17, 0x8000");
}

#[test]
fn test_ins_iter() {
    let mut iter = InsIter::new(&[0x7C, 0x43, 0x22, 0x14, 0x7E, 0x1A, 0x02, 0xA6, 0xFF], 0);
    assert_eq!(iter.next(), Some((0, Ins::new(0x7C432214))));
    assert_eq!(iter.next(), Some((4, Ins::new(0x7E1A02A6))));
    assert_eq!(iter.next(), None);
}
