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
fn test_vec_dss(){
    assert_asm!(0x7C60066C, "dss 3");
    assert_asm!(0x7E60066C, "dssall");
}

#[test]
fn test_vec_dst(){
    assert_asm!(0x7C6742AC, "dst r7, r8, 3");
    assert_asm!(0x7E232AAC, "dstt r3, r5, 1");
}

#[test]
fn test_vec_dstst(){
    assert_asm!(0x7C44FAEC, "dstst r4, r31, 2");
    assert_asm!(0x7E63DAEC, "dststt r3, r27, 3");
}

#[test]
fn test_vec_lvebx(){
    assert_asm!(0x7C64380E, "lvebx vr3, r4, r7");
}

#[test]
fn test_vec_lvehx(){
    assert_asm!(0x7CA8F84E, "lvehx vr5, r8, r31");
}

#[test]
fn test_vec_lvewx(){
    assert_asm!(0x7D09508E, "lvewx vr8, r9, r10");
}

#[test]
fn test_vec_lvsl(){
    assert_asm!(0x7CA6480C, "lvsl vr5, r6, r9");
}

#[test]
fn test_vec_lvsr(){
    assert_asm!(0x7C60284C, "lvsr vr3, r0, r5");
}

#[test]
fn test_vec_lvx(){
    assert_asm!(0x7CF2E8CE, "lvx vr7, r18, r29");
}

#[test]
fn test_vec_lvxl(){
    assert_asm!(0x7D17FACE, "lvxl vr8, r23, r31");
}

#[test]
fn test_vec_mfvscr(){
    assert_asm!(0x13E00604, "mfvscr vr31");
}

#[test]
fn test_vec_mtvscr(){
    assert_asm!(0x1000CE44, "mtvscr vr25");
}

#[test]
fn test_vec_stvebx(){
    assert_asm!(0x7CE3210E, "stvebx vr7, r3, r4");
}

#[test]
fn test_vec_stvehx(){
    assert_asm!(0x7F25514E, "stvehx vr25, r5, r10");
}

#[test]
fn test_vec_stvewx(){
    assert_asm!(0x7E08498E, "stvewx vr16, r8, r9");
}

#[test]
fn test_vec_stvx(){
    assert_asm!(0x7FE039CE, "stvx vr31, r0, r7");
}

#[test]
fn test_vec_stvxl(){
    assert_asm!(0x7E8EF3CE, "stvxl vr20, r14, r30");
}

#[test]
fn test_vec_vaddcuw(){
    assert_asm!(0x10A63980, "vaddcuw vr5, vr6, vr7");
}

#[test]
fn test_vec_vaddfp(){
    assert_asm!(0x13BEF80A, "vaddfp vr29, vr30, vr31");
}

#[test]
fn test_vec_vaddsbs(){
    assert_asm!(0x10035300, "vaddsbs vr0, vr3, vr10");
}

#[test]
fn test_vec_vaddsws(){
    assert_asm!(0x11043B80, "vaddsws vr8, vr4, vr7");
}

#[test]
fn test_vec_vaddubm(){
    assert_asm!(0x100CE000, "vaddubm vr0, vr12, vr28");
}

#[test]
fn test_vec_vaddubs(){
    assert_asm!(0x10AACA00, "vaddubs vr5, vr10, vr25");
}

#[test]
fn test_vec_vadduhm(){
    assert_asm!(0x1112E040, "vadduhm vr8, vr18, vr28");
}

#[test]
fn test_vec_vadduhs(){
    assert_asm!(0x1071EA40, "vadduhs vr3, vr17, vr29");
}

#[test]
fn test_vec_vadduwm(){
    assert_asm!(0x10D6F080, "vadduwm vr6, vr22, vr30");
}

#[test]
fn test_vec_vadduws(){
    assert_asm!(0x1109B280, "vadduws vr8, vr9, vr22");
}

#[test]
fn test_vec_vand(){
    assert_asm!(0x1156BC04, "vand vr10, vr22, vr23");
}

#[test]
fn test_vec_vandc(){
    assert_asm!(0x10F4F444, "vandc vr7, vr20, vr30");
}

#[test]
fn test_vec_vavgsb(){
    assert_asm!(0x10BC1D02, "vavgsb vr5, vr28, vr3");
}

#[test]
fn test_vec_vavgsh(){
    assert_asm!(0x106DBD42, "vavgsh vr3, vr13, vr23");
}

#[test]
fn test_vec_vavgsw(){
    assert_asm!(0x112CAD82, "vavgsw vr9, vr12, vr21");
}

#[test]
fn test_vec_vavgub(){
    assert_asm!(0x100FF402, "vavgub vr0, vr15, vr30");
}

#[test]
fn test_vec_vavguh(){
    assert_asm!(0x108EC442, "vavguh vr4, vr14, vr24");
}

#[test]
fn test_vec_vavguw(){
    assert_asm!(0x10674482, "vavguw vr3, vr7, vr8");
}

#[test]
fn test_vec_vcfsx(){
    assert_asm!(0x101D534A, "vcfsx vr0, vr10, 0x1d");
}

#[test]
fn test_vec_vcfux(){
    assert_asm!(0x10B03B0A, "vcfux vr5, vr7, 0x10");
}

#[test]
fn test_vec_vcmpbfp(){
    assert_asm!(0x106963C6, "vcmpbfp vr3, vr9, vr12");
    assert_asm!(0x10E84FC6, "vcmpbfp. vr7, vr8, vr9");
}

#[test]
fn test_vec_vcmpeqfp(){
    assert_asm!(0x108640C6, "vcmpeqfp vr4, vr6, vr8");
    assert_asm!(0x10A304C6, "vcmpeqfp. vr5, vr3, vr0");
}

#[test]
fn test_vec_vcmpequb(){
    assert_asm!(0x1011D806, "vcmpequb vr0, vr17, vr27");
    assert_asm!(0x10649C06, "vcmpequb. vr3, vr4, vr19");
}

#[test]
fn test_vec_vcmpequh(){
    assert_asm!(0x10A86046, "vcmpequh vr5, vr8, vr12");
    assert_asm!(0x10E60446, "vcmpequh. vr7, vr6, vr0");
}

#[test]
fn test_vec_vcmpequw(){
    assert_asm!(0x10664086, "vcmpequw vr3, vr6, vr8");
    assert_asm!(0x10A85486, "vcmpequw. vr5, vr8, vr10");
}

#[test]
fn test_vec_vcmpgefp(){
    assert_asm!(0x100329C6, "vcmpgefp vr0, vr3, vr5");
    assert_asm!(0x108545C6, "vcmpgefp. vr4, vr5, vr8");
}

#[test]
fn test_vec_vcmpgtfp(){
    assert_asm!(0x10A0CAC6, "vcmpgtfp vr5, vr0, vr25");
    assert_asm!(0x10E3A6C6, "vcmpgtfp. vr7, vr3, vr20");
}

#[test]
fn test_vec_vcmpgtsb(){
    assert_asm!(0x10602306, "vcmpgtsb vr3, vr0, vr4");
    assert_asm!(0x10E88706, "vcmpgtsb. vr7, vr8, vr16");
}

#[test]
fn test_vec_vcmpgtsh(){
    assert_asm!(0x10A69B46, "vcmpgtsh vr5, vr6, vr19");
    assert_asm!(0x1192C746, "vcmpgtsh. vr12, vr18, vr24");
}

#[test]
fn test_vec_vcmpgtsw(){
    assert_asm!(0x1140F386, "vcmpgtsw vr10, vr0, vr30");
    assert_asm!(0x1297DF86, "vcmpgtsw. vr20, vr23, vr27");
}

#[test]
fn test_vec_vcmpgtub(){
    assert_asm!(0x10A88206, "vcmpgtub vr5, vr8, vr16");
    assert_asm!(0x13CAA606, "vcmpgtub. vr30, vr10, vr20");
}

#[test]
fn test_vec_vcmpgtuh(){
    assert_asm!(0x101BFA46, "vcmpgtuh vr0, vr27, vr31");
    assert_asm!(0x10853646, "vcmpgtuh. vr4, vr5, vr6");
}

#[test]
fn test_vec_vcmpgtuw(){
    assert_asm!(0x1070D286, "vcmpgtuw vr3, vr16, vr26");
    assert_asm!(0x10FAFE86, "vcmpgtuw. vr7, vr26, vr31");
}

#[test]
fn test_vec_vctsxs(){
    assert_asm!(0x10743BCA, "vctsxs vr3, vr7, 0x14");
}

#[test]
fn test_vec_vctuxs(){
    assert_asm!(0x10AB638A, "vctuxs vr5, vr12, 0xb");
}

#[test]
fn test_vec_vexptefp(){
    assert_asm!(0x10E0518A, "vexptefp vr7, vr10");
}

#[test]
fn test_vec_vlogefp(){
    assert_asm!(0x100031CA, "vlogefp vr0, vr6");
}

#[test]
fn test_vec_vmaddfp(){
    assert_asm!(0x1003396E, "vmaddfp vr0, vr3, vr5, vr7");
}

#[test]
fn test_vec_vmaxfp(){
    assert_asm!(0x10C84C0A, "vmaxfp vr6, vr8, vr9");
}

#[test]
fn test_vec_vmaxsb(){
    assert_asm!(0x100AB102, "vmaxsb vr0, vr10, vr22");
}

#[test]
fn test_vec_vmaxsh(){
    assert_asm!(0x1298E142, "vmaxsh vr20, vr24, vr28");
}

#[test]
fn test_vec_vmaxsw(){
    assert_asm!(0x13DF6182, "vmaxsw vr30, vr31, vr12");
}

#[test]
fn test_vec_vmaxub(){
    assert_asm!(0x1198F002, "vmaxub vr12, vr24, vr30");
}

#[test]
fn test_vec_vmaxuh(){
    assert_asm!(0x1236D842, "vmaxuh vr17, vr22, vr27");
}

#[test]
fn test_vec_vmaxuw(){
    assert_asm!(0x114CC082, "vmaxuw vr10, vr12, vr24");
}

#[test]
fn test_vec_vmhaddshs(){
    assert_asm!(0x10A63A20, "vmhaddshs vr5, vr6, vr7, vr8");
}

#[test]
fn test_vec_vmhraddshs(){
    assert_asm!(0x112A63A1, "vmhraddshs vr9, vr10, vr12, vr14");
}

#[test]
fn test_vec_vminfp(){
    assert_asm!(0x106AAC4A, "vminfp vr3, vr10, vr21");
}

#[test]
fn test_vec_vminsb(){
    assert_asm!(0x10643B02, "vminsb vr3, vr4, vr7");
}

#[test]
fn test_vec_vminsh(){
    assert_asm!(0x10E9B342, "vminsh vr7, vr9, vr22");
}

#[test]
fn test_vec_vminsw(){
    assert_asm!(0x118F9382, "vminsw vr12, vr15, vr18");
}

#[test]
fn test_vec_vminub(){
    assert_asm!(0x108ED202, "vminub vr4, vr14, vr26");
}

#[test]
fn test_vec_vminuh(){
    assert_asm!(0x11F19A42, "vminuh vr15, vr17, vr19");
}

#[test]
fn test_vec_vminuw(){
    assert_asm!(0x1254F282, "vminuw vr18, vr20, vr30");
}

#[test]
fn test_vec_vmladduhm(){
    assert_asm!(0x10608762, "vmladduhm vr3, vr0, vr16, vr29");
}

#[test]
fn test_vec_vmrghb(){
    assert_asm!(0x10F4A80C, "vmrghb vr7, vr20, vr21");
}

#[test]
fn test_vec_vmrghh(){
    assert_asm!(0x110AC84C, "vmrghh vr8, vr10, vr25");
}

#[test]
fn test_vec_vmrghw(){
    assert_asm!(0x1198E08C, "vmrghw vr12, vr24, vr28");
}

#[test]
fn test_vec_vmrglb(){
    assert_asm!(0x1299F10C, "vmrglb vr20, vr25, vr30");
}

#[test]
fn test_vec_vmrglh(){
    assert_asm!(0x131CF94C, "vmrglh vr24, vr28, vr31");
}

#[test]
fn test_vec_vmrglw(){
    assert_asm!(0x13DF018C, "vmrglw vr30, vr31, vr0");
}

#[test]
fn test_vec_vmsummbm(){
    assert_asm!(0x10044325, "vmsummbm vr0, vr4, vr8, vr12");
}

#[test]
fn test_vec_vmsumshm(){
    assert_asm!(0x1114DFE8, "vmsumshm vr8, vr20, vr27, vr31");
}

#[test]
fn test_vec_vmsumshs(){
    assert_asm!(0x1150ADE9, "vmsumshs vr10, vr16, vr21, vr23");
}

#[test]
fn test_vec_vmsumubm(){
    assert_asm!(0x1198D7A4, "vmsumubm vr12, vr24, vr26, vr30");
}

#[test]
fn test_vec_vmsumuhm(){
    assert_asm!(0x13C503E6, "vmsumuhm vr30, vr5, vr0, vr15");
}

#[test]
fn test_vec_vmsumuhs(){
    assert_asm!(0x10032167, "vmsumuhs vr0, vr3, vr4, vr5");
}

#[test]
fn test_vec_vmulesb(){
    assert_asm!(0x110EC308, "vmulesb vr8, vr14, vr24");
}

#[test]
fn test_vec_vmulesh(){
    assert_asm!(0x10602B48, "vmulesh vr3, vr0, vr5");
}

#[test]
fn test_vec_vmuleub(){
    assert_asm!(0x10076208, "vmuleub vr0, vr7, vr12");
}

#[test]
fn test_vec_vmuleuh(){
    assert_asm!(0x1200FA48, "vmuleuh vr16, vr0, vr31");
}

#[test]
fn test_vec_vmulosb(){
    assert_asm!(0x11E01908, "vmulosb vr15, vr0, vr3");
}

#[test]
fn test_vec_vmulosh(){
    assert_asm!(0x10685148, "vmulosh vr3, vr8, vr10");
}

#[test]
fn test_vec_vmuloub(){
    assert_asm!(0x10854008, "vmuloub vr4, vr5, vr8");
}

#[test]
fn test_vec_vmulouh(){
    assert_asm!(0x10A70048, "vmulouh vr5, vr7, vr0");
}

#[test]
fn test_vec_vnmsubfp(){
    assert_asm!(0x1060F42F, "vnmsubfp vr3, vr0, vr16, vr30");
}

#[test]
fn test_vec_vnor(){
    assert_asm!(0x10605504, "vnor vr3, vr0, vr10");
    assert_asm!(0x10884504, "vnot vr4, vr8");
}

#[test]
fn test_vec_vor(){
    assert_asm!(0x100D7C84, "vor vr0, vr13, vr15");
    assert_asm!(0x1077BC84, "vmr vr3, vr23");
}

#[test]
fn test_vec_vperm(){
    assert_asm!(0x10a5302b, "vperm vr5, vr5, vr6, vr0");
}

#[test]
fn test_vec_vpkpx(){
    assert_asm!(0x10AFE30E, "vpkpx vr5, vr15, vr28");
}

#[test]
fn test_vec_vpkshss(){
    assert_asm!(0x1006498E, "vpkshss vr0, vr6, vr9");
}

#[test]
fn test_vec_vpkshus(){
    assert_asm!(0x1220990E, "vpkshus vr17, vr0, vr19");
}

#[test]
fn test_vec_vpkswss(){
    assert_asm!(0x1253A1CE, "vpkswss vr18, vr19, vr20");
}

#[test]
fn test_vec_vpkswus(){
    assert_asm!(0x128AF14E, "vpkswus vr20, vr10, vr30");
}

#[test]
fn test_vec_vpkuhum(){
    assert_asm!(0x10BBA00E, "vpkuhum vr5, vr27, vr20");
}

#[test]
fn test_vec_vpkuhus(){
    assert_asm!(0x11AE788E, "vpkuhus vr13, vr14, vr15");
}

#[test]
fn test_vec_vpkuwum(){
    assert_asm!(0x114B604E, "vpkuwum vr10, vr11, vr12");
}

#[test]
fn test_vec_vpkuwus(){
    assert_asm!(0x1176F8CE, "vpkuwus vr11, vr22, vr31");
}

#[test]
fn test_vec_vrefp(){
    assert_asm!(0x1180C10A, "vrefp vr12, vr24");
}

#[test]
fn test_vec_vrfim(){
    assert_asm!(0x1240F2CA, "vrfim vr18, vr30");
}

#[test]
fn test_vec_vrfin(){
    assert_asm!(0x1140620A, "vrfin vr10, vr12");
}

#[test]
fn test_vec_vrfip(){
    assert_asm!(0x10E08A8A, "vrfip vr7, vr17");
}

#[test]
fn test_vec_vrfiz(){
    assert_asm!(0x1000A24A, "vrfiz vr0, vr20");
}

#[test]
fn test_vec_vrlb(){
    assert_asm!(0x10EF8804, "vrlb vr7, vr15, vr17");
}

#[test]
fn test_vec_vrlh(){
    assert_asm!(0x12129844, "vrlh vr16, vr18, vr19");
}

#[test]
fn test_vec_vrlw(){
    assert_asm!(0x11540084, "vrlw vr10, vr20, vr0");
}

#[test]
fn test_vec_vrsqrtefp(){
    assert_asm!(0x1060794A, "vrsqrtefp vr3, vr15");
}

#[test]
fn test_vec_vsel(){
    assert_asm!(0x100329AA, "vsel vr0, vr3, vr5, vr6");
}

#[test]
fn test_vec_vsl(){
    assert_asm!(0x108CC1C4, "vsl vr4, vr12, vr24");
}

#[test]
fn test_vec_vslb(){
    assert_asm!(0x114E9104, "vslb vr10, vr14, vr18");
}

#[test]
fn test_vec_vsldoi(){
    assert_asm!(0x10601B6C, "vsldoi vr3, vr0, vr3, 13");
}

#[test]
fn test_vec_vslh(){
    assert_asm!(0x10AFC144, "vslh vr5, vr15, vr24");
}

#[test]
fn test_vec_vslo(){
    assert_asm!(0x10F1DC0C, "vslo vr7, vr17, vr27");
}

#[test]
fn test_vec_vslw(){
    assert_asm!(0x11128184, "vslw vr8, vr18, vr16");
}

#[test]
fn test_vec_vspltb(){
    assert_asm!(0x115C620C, "vspltb vr10, vr12, 0x1c");
}

#[test]
fn test_vec_vsplth(){
    assert_asm!(0x11947A4C, "vsplth vr12, vr15, 0x14");
}

#[test]
fn test_vec_vspltisb(){
    assert_asm!(0x1076030C, "vspltisb vr3, -0xa");
}

#[test]
fn test_vec_vspltish(){
    assert_asm!(0x11CE034C, "vspltish vr14, 0xe");
}

#[test]
fn test_vec_vspltisw(){
    assert_asm!(0x124C038C, "vspltisw vr18, 0xc");
}

#[test]
fn test_vec_vspltw(){
    assert_asm!(0x1018528C, "vspltw vr0, vr10, 0x18");
}

#[test]
fn test_vec_vsr(){
    assert_asm!(0x116C6AC4, "vsr vr11, vr12, vr13");
}

#[test]
fn test_vec_vsrab(){
    assert_asm!(0x11D09304, "vsrab vr14, vr16, vr18");
}

#[test]
fn test_vec_vsrah(){
    assert_asm!(0x10E8C344, "vsrah vr7, vr8, vr24");
}

#[test]
fn test_vec_vsraw(){
    assert_asm!(0x112CAB84, "vsraw vr9, vr12, vr21");
}

#[test]
fn test_vec_vsrb(){
    assert_asm!(0x1112D204, "vsrb vr8, vr18, vr26");
}

#[test]
fn test_vec_vsrh(){
    assert_asm!(0x114C8244, "vsrh vr10, vr12, vr16");
}

#[test]
fn test_vec_vsro(){
    assert_asm!(0x118F9C4C, "vsro vr12, vr15, vr19");
}

#[test]
fn test_vec_vsrw(){
    assert_asm!(0x100EA284, "vsrw vr0, vr14, vr20");
}

#[test]
fn test_vec_vsubcuw(){
    assert_asm!(0x10AF8580, "vsubcuw vr5, vr15, vr16");
}

#[test]
fn test_vec_vsubfp(){
    assert_asm!(0x1080584A, "vsubfp vr4, vr0, vr11");
}

#[test]
fn test_vec_vsubsbs(){
    assert_asm!(0x10D2BF00, "vsubsbs vr6, vr18, vr23");
}

#[test]
fn test_vec_vsubshs(){
    assert_asm!(0x10F16740, "vsubshs vr7, vr17, vr12");
}

#[test]
fn test_vec_vsubsws(){
    assert_asm!(0x118D5780, "vsubsws vr12, vr13, vr10");
}

#[test]
fn test_vec_vsububm(){
    assert_asm!(0x11402C00, "vsububm vr10, vr0, vr5");
}

#[test]
fn test_vec_vsububs(){
    assert_asm!(0x10033600, "vsububs vr0, vr3, vr6");
}

#[test]
fn test_vec_vsubuhm(){
    assert_asm!(0x10EB6C40, "vsubuhm vr7, vr11, vr13");
}

#[test]
fn test_vec_vsubuhs(){
    assert_asm!(0x110A6640, "vsubuhs vr8, vr10, vr12");
}

#[test]
fn test_vec_vsubuwm(){
    assert_asm!(0x112BDC80, "vsubuwm vr9, vr11, vr27");
}

#[test]
fn test_vec_vsubuws(){
    assert_asm!(0x1149AE80, "vsubuws vr10, vr9, vr21");
}

#[test]
fn test_vec_vsumsws(){
    assert_asm!(0x116C6F88, "vsumsws vr11, vr12, vr13");
}

#[test]
fn test_vec_vsum2sws(){
    assert_asm!(0x11909688, "vsum2sws vr12, vr16, vr18");
}

#[test]
fn test_vec_vsum4sbs(){
    assert_asm!(0x11B19708, "vsum4sbs vr13, vr17, vr18");
}

#[test]
fn test_vec_vsum4shs(){
    assert_asm!(0x1296C648, "vsum4shs vr20, vr22, vr24");
}

#[test]
fn test_vec_vsum4ubs(){
    assert_asm!(0x12F8CE08, "vsum4ubs vr23, vr24, vr25");
}

#[test]
fn test_vec_vupkhpx(){
    assert_asm!(0x10A0434E, "vupkhpx vr5, vr8");
}

#[test]
fn test_vec_vupkhsb(){
    assert_asm!(0x10001A0E, "vupkhsb vr0, vr3");
}

#[test]
fn test_vec_vupkhsh(){
    assert_asm!(0x11806A4E, "vupkhsh vr12, vr13");
}

#[test]
fn test_vec_vupklpx(){
    assert_asm!(0x108083CE, "vupklpx vr4, vr16");
}

#[test]
fn test_vec_vupklsb(){
    assert_asm!(0x11407A8E, "vupklsb vr10, vr15");
}

#[test]
fn test_vec_vupklsh(){
    assert_asm!(0x1180C2CE, "vupklsh vr12, vr24");
}

#[test]
fn test_vec_vxor(){
    assert_asm!(0x10654CC4, "vxor vr3, vr5, vr9");
}