use ppc750cl::Ins;

macro_rules! assert_asm {
    ($ins:ident, $disasm:literal) => {{
        assert_eq!(format!("{}", $ins.simplified()), $disasm)
    }};
    ($code:literal, $disasm:literal) => {{
        let ins = Ins::new($code);
        assert_eq!(format!("{}", ins.simplified()), $disasm)
    }};
}

#[test]
fn test_vec_dss() {
    assert_asm!(0x7C60066C, "dss 3");
    assert_asm!(0x7E00066C, "dssall");
}

#[test]
fn test_vec_dst() {
    assert_asm!(0x7C6742AC, "dst r7, r8, 3");
    assert_asm!(0x7E232AAC, "dstt r3, r5, 1");
}

#[test]
fn test_vec_dstst() {
    assert_asm!(0x7C44FAEC, "dstst r4, r31, 2");
    assert_asm!(0x7E63DAEC, "dststt r3, r27, 3");
}

#[test]
fn test_vec_lvebx() {
    assert_asm!(0x7C64380E, "lvebx v3, r4, r7");
}

#[test]
fn test_vec_lvehx() {
    assert_asm!(0x7CA8F84E, "lvehx v5, r8, r31");
}

#[test]
fn test_vec_lvewx() {
    assert_asm!(0x7D09508E, "lvewx v8, r9, r10");
}

#[test]
fn test_vec_lvsl() {
    assert_asm!(0x7CA6480C, "lvsl v5, r6, r9");
}

#[test]
fn test_vec_lvsr() {
    assert_asm!(0x7C60284C, "lvsr v3, r0, r5");
}

#[test]
fn test_vec_lvx() {
    assert_asm!(0x7CF2E8CE, "lvx v7, r18, r29");
}

#[test]
fn test_vec_lvxl() {
    assert_asm!(0x7D17FACE, "lvxl v8, r23, r31");
}

#[test]
fn test_vec_mfvscr() {
    assert_asm!(0x13E00604, "mfvscr v31");
}

#[test]
fn test_vec_mtvscr() {
    assert_asm!(0x1000CE44, "mtvscr v25");
}

#[test]
fn test_vec_stvebx() {
    assert_asm!(0x7CE3210E, "stvebx v7, r3, r4");
}

#[test]
fn test_vec_stvehx() {
    assert_asm!(0x7F25514E, "stvehx v25, r5, r10");
}

#[test]
fn test_vec_stvewx() {
    assert_asm!(0x7E08498E, "stvewx v16, r8, r9");
}

#[test]
fn test_vec_stvx() {
    assert_asm!(0x7FE039CE, "stvx v31, r0, r7");
}

#[test]
fn test_vec_stvxl() {
    assert_asm!(0x7E8EF3CE, "stvxl v20, r14, r30");
}

#[test]
fn test_vec_vaddcuw() {
    assert_asm!(0x10A63980, "vaddcuw v5, v6, v7");
}

#[test]
fn test_vec_vaddfp() {
    assert_asm!(0x13BEF80A, "vaddfp v29, v30, v31");
}

#[test]
fn test_vec_vaddsbs() {
    assert_asm!(0x10035300, "vaddsbs v0, v3, v10");
}

#[test]
fn test_vec_vaddsws() {
    assert_asm!(0x11043B80, "vaddsws v8, v4, v7");
}

#[test]
fn test_vec_vaddubm() {
    assert_asm!(0x100CE000, "vaddubm v0, v12, v28");
}

#[test]
fn test_vec_vaddubs() {
    assert_asm!(0x10AACA00, "vaddubs v5, v10, v25");
}

#[test]
fn test_vec_vadduhm() {
    assert_asm!(0x1112E040, "vadduhm v8, v18, v28");
}

#[test]
fn test_vec_vadduhs() {
    assert_asm!(0x1071EA40, "vadduhs v3, v17, v29");
}

#[test]
fn test_vec_vadduwm() {
    assert_asm!(0x10D6F080, "vadduwm v6, v22, v30");
}

#[test]
fn test_vec_vadduws() {
    assert_asm!(0x1109B280, "vadduws v8, v9, v22");
}

#[test]
fn test_vec_vand() {
    assert_asm!(0x1156BC04, "vand v10, v22, v23");
}

#[test]
fn test_vec_vandc() {
    assert_asm!(0x10F4F444, "vandc v7, v20, v30");
}

#[test]
fn test_vec_vavgsb() {
    assert_asm!(0x10BC1D02, "vavgsb v5, v28, v3");
}

#[test]
fn test_vec_vavgsh() {
    assert_asm!(0x106DBD42, "vavgsh v3, v13, v23");
}

#[test]
fn test_vec_vavgsw() {
    assert_asm!(0x112CAD82, "vavgsw v9, v12, v21");
}

#[test]
fn test_vec_vavgub() {
    assert_asm!(0x100FF402, "vavgub v0, v15, v30");
}

#[test]
fn test_vec_vavguh() {
    assert_asm!(0x108EC442, "vavguh v4, v14, v24");
}

#[test]
fn test_vec_vavguw() {
    assert_asm!(0x10674482, "vavguw v3, v7, v8");
}

#[test]
fn test_vec_vcfsx() {
    assert_asm!(0x101D534A, "vcfsx v0, v10, 0x1d");
}

#[test]
fn test_vec_vcfux() {
    assert_asm!(0x10B03B0A, "vcfux v5, v7, 0x10");
}

#[test]
fn test_vec_vcmpbfp() {
    assert_asm!(0x106963C6, "vcmpbfp v3, v9, v12");
    assert_asm!(0x10E84FC6, "vcmpbfp. v7, v8, v9");
}

#[test]
fn test_vec_vcmpeqfp() {
    assert_asm!(0x108640C6, "vcmpeqfp v4, v6, v8");
    assert_asm!(0x10A304C6, "vcmpeqfp. v5, v3, v0");
}

#[test]
fn test_vec_vcmpequb() {
    assert_asm!(0x1011D806, "vcmpequb v0, v17, v27");
    assert_asm!(0x10649C06, "vcmpequb. v3, v4, v19");
}

#[test]
fn test_vec_vcmpequh() {
    assert_asm!(0x10A86046, "vcmpequh v5, v8, v12");
    assert_asm!(0x10E60446, "vcmpequh. v7, v6, v0");
}

#[test]
fn test_vec_vcmpequw() {
    assert_asm!(0x10664086, "vcmpequw v3, v6, v8");
    assert_asm!(0x10A85486, "vcmpequw. v5, v8, v10");
}

#[test]
fn test_vec_vcmpgefp() {
    assert_asm!(0x100329C6, "vcmpgefp v0, v3, v5");
    assert_asm!(0x108545C6, "vcmpgefp. v4, v5, v8");
}

#[test]
fn test_vec_vcmpgtfp() {
    assert_asm!(0x10A0CAC6, "vcmpgtfp v5, v0, v25");
    assert_asm!(0x10E3A6C6, "vcmpgtfp. v7, v3, v20");
}

#[test]
fn test_vec_vcmpgtsb() {
    assert_asm!(0x10602306, "vcmpgtsb v3, v0, v4");
    assert_asm!(0x10E88706, "vcmpgtsb. v7, v8, v16");
}

#[test]
fn test_vec_vcmpgtsh() {
    assert_asm!(0x10A69B46, "vcmpgtsh v5, v6, v19");
    assert_asm!(0x1192C746, "vcmpgtsh. v12, v18, v24");
}

#[test]
fn test_vec_vcmpgtsw() {
    assert_asm!(0x1140F386, "vcmpgtsw v10, v0, v30");
    assert_asm!(0x1297DF86, "vcmpgtsw. v20, v23, v27");
}

#[test]
fn test_vec_vcmpgtub() {
    assert_asm!(0x10A88206, "vcmpgtub v5, v8, v16");
    assert_asm!(0x13CAA606, "vcmpgtub. v30, v10, v20");
}

#[test]
fn test_vec_vcmpgtuh() {
    assert_asm!(0x101BFA46, "vcmpgtuh v0, v27, v31");
    assert_asm!(0x10853646, "vcmpgtuh. v4, v5, v6");
}

#[test]
fn test_vec_vcmpgtuw() {
    assert_asm!(0x1070D286, "vcmpgtuw v3, v16, v26");
    assert_asm!(0x10FAFE86, "vcmpgtuw. v7, v26, v31");
}

#[test]
fn test_vec_vctsxs() {
    assert_asm!(0x10743BCA, "vctsxs v3, v7, 0x14");
}

#[test]
fn test_vec_vctuxs() {
    assert_asm!(0x10AB638A, "vctuxs v5, v12, 0xb");
}

#[test]
fn test_vec_vexptefp() {
    assert_asm!(0x10E0518A, "vexptefp v7, v10");
}

#[test]
fn test_vec_vlogefp() {
    assert_asm!(0x100031CA, "vlogefp v0, v6");
}

#[test]
fn test_vec_vmaddfp() {
    assert_asm!(0x1003396E, "vmaddfp v0, v3, v5, v7");
}

#[test]
fn test_vec_vmaxfp() {
    assert_asm!(0x10C84C0A, "vmaxfp v6, v8, v9");
}

#[test]
fn test_vec_vmaxsb() {
    assert_asm!(0x100AB102, "vmaxsb v0, v10, v22");
}

#[test]
fn test_vec_vmaxsh() {
    assert_asm!(0x1298E142, "vmaxsh v20, v24, v28");
}

#[test]
fn test_vec_vmaxsw() {
    assert_asm!(0x13DF6182, "vmaxsw v30, v31, v12");
}

#[test]
fn test_vec_vmaxub() {
    assert_asm!(0x1198F002, "vmaxub v12, v24, v30");
}

#[test]
fn test_vec_vmaxuh() {
    assert_asm!(0x1236D842, "vmaxuh v17, v22, v27");
}

#[test]
fn test_vec_vmaxuw() {
    assert_asm!(0x114CC082, "vmaxuw v10, v12, v24");
}

#[test]
fn test_vec_vmhaddshs() {
    assert_asm!(0x10A63A20, "vmhaddshs v5, v6, v7, v8");
}

#[test]
fn test_vec_vmhraddshs() {
    assert_asm!(0x112A63A1, "vmhraddshs v9, v10, v12, v14");
}

#[test]
fn test_vec_vminfp() {
    assert_asm!(0x106AAC4A, "vminfp v3, v10, v21");
}

#[test]
fn test_vec_vminsb() {
    assert_asm!(0x10643B02, "vminsb v3, v4, v7");
}

#[test]
fn test_vec_vminsh() {
    assert_asm!(0x10E9B342, "vminsh v7, v9, v22");
}

#[test]
fn test_vec_vminsw() {
    assert_asm!(0x118F9382, "vminsw v12, v15, v18");
}

#[test]
fn test_vec_vminub() {
    assert_asm!(0x108ED202, "vminub v4, v14, v26");
}

#[test]
fn test_vec_vminuh() {
    assert_asm!(0x11F19A42, "vminuh v15, v17, v19");
}

#[test]
fn test_vec_vminuw() {
    assert_asm!(0x1254F282, "vminuw v18, v20, v30");
}

#[test]
fn test_vec_vmladduhm() {
    assert_asm!(0x10608762, "vmladduhm v3, v0, v16, v29");
}

#[test]
fn test_vec_vmrghb() {
    assert_asm!(0x10F4A80C, "vmrghb v7, v20, v21");
}

#[test]
fn test_vec_vmrghh() {
    assert_asm!(0x110AC84C, "vmrghh v8, v10, v25");
}

#[test]
fn test_vec_vmrghw() {
    assert_asm!(0x1198E08C, "vmrghw v12, v24, v28");
}

#[test]
fn test_vec_vmrglb() {
    assert_asm!(0x1299F10C, "vmrglb v20, v25, v30");
}

#[test]
fn test_vec_vmrglh() {
    assert_asm!(0x131CF94C, "vmrglh v24, v28, v31");
}

#[test]
fn test_vec_vmrglw() {
    assert_asm!(0x13DF018C, "vmrglw v30, v31, v0");
}

#[test]
fn test_vec_vmsummbm() {
    assert_asm!(0x10044325, "vmsummbm v0, v4, v8, v12");
}

#[test]
fn test_vec_vmsumshm() {
    assert_asm!(0x1114DFE8, "vmsumshm v8, v20, v27, v31");
}

#[test]
fn test_vec_vmsumshs() {
    assert_asm!(0x1150ADE9, "vmsumshs v10, v16, v21, v23");
}

#[test]
fn test_vec_vmsumubm() {
    assert_asm!(0x1198D7A4, "vmsumubm v12, v24, v26, v30");
}

#[test]
fn test_vec_vmsumuhm() {
    assert_asm!(0x13C503E6, "vmsumuhm v30, v5, v0, v15");
}

#[test]
fn test_vec_vmsumuhs() {
    assert_asm!(0x10032167, "vmsumuhs v0, v3, v4, v5");
}

#[test]
fn test_vec_vmulesb() {
    assert_asm!(0x110EC308, "vmulesb v8, v14, v24");
}

#[test]
fn test_vec_vmulesh() {
    assert_asm!(0x10602B48, "vmulesh v3, v0, v5");
}

#[test]
fn test_vec_vmuleub() {
    assert_asm!(0x10076208, "vmuleub v0, v7, v12");
}

#[test]
fn test_vec_vmuleuh() {
    assert_asm!(0x1200FA48, "vmuleuh v16, v0, v31");
}

#[test]
fn test_vec_vmulosb() {
    assert_asm!(0x11E01908, "vmulosb v15, v0, v3");
}

#[test]
fn test_vec_vmulosh() {
    assert_asm!(0x10685148, "vmulosh v3, v8, v10");
}

#[test]
fn test_vec_vmuloub() {
    assert_asm!(0x10854008, "vmuloub v4, v5, v8");
}

#[test]
fn test_vec_vmulouh() {
    assert_asm!(0x10A70048, "vmulouh v5, v7, v0");
}

#[test]
fn test_vec_vnmsubfp() {
    assert_asm!(0x1060F42F, "vnmsubfp v3, v0, v16, v30");
}

#[test]
fn test_vec_vnor() {
    assert_asm!(0x10605504, "vnor v3, v0, v10");
    assert_asm!(0x10884504, "vnot v4, v8");
}

#[test]
fn test_vec_vor() {
    assert_asm!(0x100D7C84, "vor v0, v13, v15");
    assert_asm!(0x1077BC84, "vmr v3, v23");
}

#[test]
fn test_vec_vperm() {
    assert_asm!(0x10a5302b, "vperm v5, v5, v6, v0");
}

#[test]
fn test_vec_vpkpx() {
    assert_asm!(0x10AFE30E, "vpkpx v5, v15, v28");
}

#[test]
fn test_vec_vpkshss() {
    assert_asm!(0x1006498E, "vpkshss v0, v6, v9");
}

#[test]
fn test_vec_vpkshus() {
    assert_asm!(0x1220990E, "vpkshus v17, v0, v19");
}

#[test]
fn test_vec_vpkswss() {
    assert_asm!(0x1253A1CE, "vpkswss v18, v19, v20");
}

#[test]
fn test_vec_vpkswus() {
    assert_asm!(0x128AF14E, "vpkswus v20, v10, v30");
}

#[test]
fn test_vec_vpkuhum() {
    assert_asm!(0x10BBA00E, "vpkuhum v5, v27, v20");
}

#[test]
fn test_vec_vpkuhus() {
    assert_asm!(0x11AE788E, "vpkuhus v13, v14, v15");
}

#[test]
fn test_vec_vpkuwum() {
    assert_asm!(0x114B604E, "vpkuwum v10, v11, v12");
}

#[test]
fn test_vec_vpkuwus() {
    assert_asm!(0x1176F8CE, "vpkuwus v11, v22, v31");
}

#[test]
fn test_vec_vrefp() {
    assert_asm!(0x1180C10A, "vrefp v12, v24");
}

#[test]
fn test_vec_vrfim() {
    assert_asm!(0x1240F2CA, "vrfim v18, v30");
}

#[test]
fn test_vec_vrfin() {
    assert_asm!(0x1140620A, "vrfin v10, v12");
}

#[test]
fn test_vec_vrfip() {
    assert_asm!(0x10E08A8A, "vrfip v7, v17");
}

#[test]
fn test_vec_vrfiz() {
    assert_asm!(0x1000A24A, "vrfiz v0, v20");
}

#[test]
fn test_vec_vrlb() {
    assert_asm!(0x10EF8804, "vrlb v7, v15, v17");
}

#[test]
fn test_vec_vrlh() {
    assert_asm!(0x12129844, "vrlh v16, v18, v19");
}

#[test]
fn test_vec_vrlw() {
    assert_asm!(0x11540084, "vrlw v10, v20, v0");
}

#[test]
fn test_vec_vrsqrtefp() {
    assert_asm!(0x1060794A, "vrsqrtefp v3, v15");
}

#[test]
fn test_vec_vsel() {
    assert_asm!(0x100329AA, "vsel v0, v3, v5, v6");
}

#[test]
fn test_vec_vsl() {
    assert_asm!(0x108CC1C4, "vsl v4, v12, v24");
}

#[test]
fn test_vec_vslb() {
    assert_asm!(0x114E9104, "vslb v10, v14, v18");
}

#[test]
fn test_vec_vsldoi() {
    assert_asm!(0x10601B6C, "vsldoi v3, v0, v3, 13");
}

#[test]
fn test_vec_vslh() {
    assert_asm!(0x10AFC144, "vslh v5, v15, v24");
}

#[test]
fn test_vec_vslo() {
    assert_asm!(0x10F1DC0C, "vslo v7, v17, v27");
}

#[test]
fn test_vec_vslw() {
    assert_asm!(0x11128184, "vslw v8, v18, v16");
}

#[test]
fn test_vec_vspltb() {
    assert_asm!(0x115C620C, "vspltb v10, v12, 0x1c");
}

#[test]
fn test_vec_vsplth() {
    assert_asm!(0x11947A4C, "vsplth v12, v15, 0x14");
}

#[test]
fn test_vec_vspltisb() {
    assert_asm!(0x1076030C, "vspltisb v3, -0xa");
}

#[test]
fn test_vec_vspltish() {
    assert_asm!(0x11CE034C, "vspltish v14, 0xe");
}

#[test]
fn test_vec_vspltisw() {
    assert_asm!(0x124C038C, "vspltisw v18, 0xc");
}

#[test]
fn test_vec_vspltw() {
    assert_asm!(0x1018528C, "vspltw v0, v10, 0x18");
}

#[test]
fn test_vec_vsr() {
    assert_asm!(0x116C6AC4, "vsr v11, v12, v13");
}

#[test]
fn test_vec_vsrab() {
    assert_asm!(0x11D09304, "vsrab v14, v16, v18");
}

#[test]
fn test_vec_vsrah() {
    assert_asm!(0x10E8C344, "vsrah v7, v8, v24");
}

#[test]
fn test_vec_vsraw() {
    assert_asm!(0x112CAB84, "vsraw v9, v12, v21");
}

#[test]
fn test_vec_vsrb() {
    assert_asm!(0x1112D204, "vsrb v8, v18, v26");
}

#[test]
fn test_vec_vsrh() {
    assert_asm!(0x114C8244, "vsrh v10, v12, v16");
}

#[test]
fn test_vec_vsro() {
    assert_asm!(0x118F9C4C, "vsro v12, v15, v19");
}

#[test]
fn test_vec_vsrw() {
    assert_asm!(0x100EA284, "vsrw v0, v14, v20");
}

#[test]
fn test_vec_vsubcuw() {
    assert_asm!(0x10AF8580, "vsubcuw v5, v15, v16");
}

#[test]
fn test_vec_vsubfp() {
    assert_asm!(0x1080584A, "vsubfp v4, v0, v11");
}

#[test]
fn test_vec_vsubsbs() {
    assert_asm!(0x10D2BF00, "vsubsbs v6, v18, v23");
}

#[test]
fn test_vec_vsubshs() {
    assert_asm!(0x10F16740, "vsubshs v7, v17, v12");
}

#[test]
fn test_vec_vsubsws() {
    assert_asm!(0x118D5780, "vsubsws v12, v13, v10");
}

#[test]
fn test_vec_vsububm() {
    assert_asm!(0x11402C00, "vsububm v10, v0, v5");
}

#[test]
fn test_vec_vsububs() {
    assert_asm!(0x10033600, "vsububs v0, v3, v6");
}

#[test]
fn test_vec_vsubuhm() {
    assert_asm!(0x10EB6C40, "vsubuhm v7, v11, v13");
}

#[test]
fn test_vec_vsubuhs() {
    assert_asm!(0x110A6640, "vsubuhs v8, v10, v12");
}

#[test]
fn test_vec_vsubuwm() {
    assert_asm!(0x112BDC80, "vsubuwm v9, v11, v27");
}

#[test]
fn test_vec_vsubuws() {
    assert_asm!(0x1149AE80, "vsubuws v10, v9, v21");
}

#[test]
fn test_vec_vsumsws() {
    assert_asm!(0x116C6F88, "vsumsws v11, v12, v13");
}

#[test]
fn test_vec_vsum2sws() {
    assert_asm!(0x11909688, "vsum2sws v12, v16, v18");
}

#[test]
fn test_vec_vsum4sbs() {
    assert_asm!(0x11B19708, "vsum4sbs v13, v17, v18");
}

#[test]
fn test_vec_vsum4shs() {
    assert_asm!(0x1296C648, "vsum4shs v20, v22, v24");
}

#[test]
fn test_vec_vsum4ubs() {
    assert_asm!(0x12F8CE08, "vsum4ubs v23, v24, v25");
}

#[test]
fn test_vec_vupkhpx() {
    assert_asm!(0x10A0434E, "vupkhpx v5, v8");
}

#[test]
fn test_vec_vupkhsb() {
    assert_asm!(0x10001A0E, "vupkhsb v0, v3");
}

#[test]
fn test_vec_vupkhsh() {
    assert_asm!(0x11806A4E, "vupkhsh v12, v13");
}

#[test]
fn test_vec_vupklpx() {
    assert_asm!(0x108083CE, "vupklpx v4, v16");
}

#[test]
fn test_vec_vupklsb() {
    assert_asm!(0x11407A8E, "vupklsb v10, v15");
}

#[test]
fn test_vec_vupklsh() {
    assert_asm!(0x1180C2CE, "vupklsh v12, v24");
}

#[test]
fn test_vec_vxor() {
    assert_asm!(0x10654CC4, "vxor v3, v5, v9");
}
