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
fn test_vmx_lvewx128(){
    assert_asm!(0x1243388F, "lvewx128 vr114, r3, r7");
}

#[test]
fn test_vmx_lvlx128(){
    assert_asm!(0x1085440F, "lvlx128 vr100, r5, r8");
}

#[test]
fn test_vmx_lvrx128(){
    assert_asm!(0x108EE44B, "lvrx128 vr68, r14, r28");
}

#[test]
fn test_vmx_lvlxl128(){
    assert_asm!(0x1105FE0B, "lvlxl128 vr72, r5, r31");
}

#[test]
fn test_vmx_lvrxl128(){
    assert_asm!(0x12A01E4B, "lvrxl128 vr85, r0, r3");
}

#[test]
fn test_vmx_lvsl128(){
    assert_asm!(0x138AF00B, "lvsl128 vr92, r10, r30");
}

#[test]
fn test_vmx_lvsr128(){
    assert_asm!(0x1016C04F, "lvsr128 vr96, r22, r24");
}

#[test]
fn test_vmx_lvx128(){
    assert_asm!(0x120938CF, "lvx128 vr112, r9, r7");
}

#[test]
fn test_vmx_lvxl128(){
    assert_asm!(0x12C322CF, "lvxl128 vr118, r3, r4");
}

#[test]
fn test_vmx_stvewx128(){
    assert_asm!(0x131BF98F, "stvewx128 vr120, r27, r31");
}

#[test]
fn test_vmx_stvlx128(){
    assert_asm!(0x12602D0B, "stvlx128 vr83, r0, r5");
}

#[test]
fn test_vmx_stvlxl128(){
    assert_asm!(0x12C3A70B, "stvlxl128 vr86, r3, r20");
}

#[test]
fn test_vmx_stvrx128(){
    assert_asm!(0x10B8F54B, "stvrx128 vr69, r24, r30");
}

#[test]
fn test_vmx_stvrxl128(){
    assert_asm!(0x10C7074B, "stvrxl128 vr70, r7, r0");
}

#[test]
fn test_vmx_stvx128(){
    assert_asm!(0x130341C3, "stvx128 vr24, r3, r8");
}

#[test]
fn test_vmx_stvxl128(){
    assert_asm!(0x13E553C3, "stvxl128 vr31, r5, r10");
}

#[test]
fn test_vmx_vaddfp128(){
    assert_asm!(0x151E301B, "vaddfp128 vr72, vr30, vr102");
}

#[test]
fn test_vmx_vand128(){
    assert_asm!(0x16900E12, "vand128 vr20, vr80, vr65");
}

#[test]
fn test_vmx_vandc128(){
    assert_asm!(0x15EBFE52, "vandc128 vr15, vr75, vr95");
}

#[test]
fn test_vmx_vcfpsxws128(){
    assert_asm!(0x1A42D23B, "vcfpsxws128 vr82, vr122, 0x2");
}

#[test]
fn test_vmx_vcfpuxws128(){
    assert_asm!(0x1BEACA78, "vcfpuxws128 vr95, vr25, 0xa");
}

#[test]
fn test_vmx_vcmpbfp128(){
    assert_asm!(0x1BA5598E, "vcmpbfp128 vr125, vr5, vr75");
    assert_asm!(0x198D79C2, "vcmpbfp128. vr12, vr13, vr79");
}

#[test]
fn test_vmx_vcmpeqfp128(){
    assert_asm!(0x1800D80B, "vcmpeqfp128 vr64, vr0, vr123");
    assert_asm!(0x1ACD1C43, "vcmpeqfp128. vr22, vr77, vr99");
}

#[test]
fn test_vmx_vcmpequw128(){
    assert_asm!(0x18D0D60A, "vcmpequw128 vr70, vr80, vr90");
    assert_asm!(0x18800A40, "vcmpequw128. vr4, vr0, vr1");
}

#[test]
fn test_vmx_vcmpgefp128(){
    assert_asm!(0x1A8A1483, "vcmpgefp128 vr20, vr74, vr98");
    assert_asm!(0x18EB7CEF, "vcmpgefp128. vr103, vr107, vr111");
}

#[test]
fn test_vmx_vcmpgtfp128(){
    assert_asm!(0x1BD48102, "vcmpgtfp128 vr30, vr20, vr80");
    assert_asm!(0x1B586D68, "vcmpgtfp128. vr90, vr120, vr13");
}

#[test]
fn test_vmx_vcsxwfp128(){
    assert_asm!(0x18749ABC, "vcsxwfp128 vr99, vr19, -0xc");
}

#[test]
fn test_vmx_vcuxwfp128(){
    assert_asm!(0x1A6D1AF8, "vcuxwfp128 vr83, vr3, 0xd");
}

#[test]
fn test_vmx_vexptefp128(){
    assert_asm!(0x198056B0, "vexptefp128 vr12, vr10");
}

#[test]
fn test_vmx_vlogefp128(){
    assert_asm!(0x1900FEFB, "vlogefp128 vr72, vr127");
}

#[test]
fn test_vmx_vmaddcfp128(){
    assert_asm!(0x163B1912, "vmaddcfp128 vr17, vr27, vr67");
}

#[test]
fn test_vmx_vmaddfp128(){
    assert_asm!(0x16B3ECFB, "vmaddfp128 vr85, vr115, vr125");
}

#[test]
fn test_vmx_vmaxfp128(){
    assert_asm!(0x1B274683, "vmaxfp128 vr25, vr71, vr104");
}

#[test]
fn test_vmx_vminfp128(){
    assert_asm!(0x1BE012C0, "vminfp128 vr31, vr0, vr2");
}

#[test]
fn test_vmx_vmrghw128(){
    assert_asm!(0x18CA730B, "vmrghw128 vr70, vr10, vr110");
}

#[test]
fn test_vmx_vmrglw128(){
    assert_asm!(0x1BD2D743, "vmrglw128 vr30, vr82, vr122");
}

#[test]
fn test_vmx_vmsum3fp128(){
    assert_asm!(0x14FBF993, "vmsum3fp128 vr7, vr27, vr127");
}

#[test]
fn test_vmx_vmsum4fp128(){
    assert_asm!(0x14A869D0, "vmsum4fp128 vr5, vr8, vr13");
}

#[test]
fn test_vmx_vmulfp128(){
    assert_asm!(0x1498DCBF, "vmulfp128 vr100, vr120, vr123");
}

#[test]
fn test_vmx_vnmsubfp128(){
    assert_asm!(0x17DBCD53, "vnmsubfp128 vr30, vr91, vr121");
}

#[test]
fn test_vmx_vnor128(){
    assert_asm!(0x176A6290, "vnor128 vr27, vr10, vr12");
}

#[test]
fn test_vmx_vor128(){
    assert_asm!(0x17EC3ADC, "vor128 vr127, vr12, vr7");
}

#[test]
fn test_vmx_vperm128(){
    assert_asm!(0x1661158F, "vperm128 vr115, vr65, vr98, vr6");
}

#[test]
fn test_vmx_vpermwi128(){
    assert_asm!(0x19C342DE, "vpermwi128 vr110, vr72, 99");
}

#[test]
fn test_vmx_vpkd3d128(){
    assert_asm!(0x1935DEDC, "vpkd3d128 vr105, vr27, 5, 1, 3");
}

#[test]
fn test_vmx_vpkshss128(){
    assert_asm!(0x16C0F62B, "vpkshss128 vr86, vr96, vr126");
}

#[test]
fn test_vmx_vpkshus128(){
    assert_asm!(0x153D6E48, "vpkshus128 vr73, vr93, vr13");
}

#[test]
fn test_vmx_vpkswss128(){
    assert_asm!(0x16FE7280, "vpkswss128 vr23, vr30, vr14");
}

#[test]
fn test_vmx_vpkswus128(){
    assert_asm!(0x161836C3, "vpkswus128 vr16, vr88, vr102");
}

#[test]
fn test_vmx_vpkuhum128(){
    assert_asm!(0x14E3BF02, "vpkuhum128 vr7, vr67, vr87");
}

#[test]
fn test_vmx_vpkuhus128(){
    assert_asm!(0x1600A348, "vpkuhus128 vr80, vr0, vr20");
}

#[test]
fn test_vmx_vpkuwum128(){
    assert_asm!(0x16EACB83, "vpkuwum128 vr23, vr10, vr121");
}

#[test]
fn test_vmx_vpkuwus128(){
    assert_asm!(0x17E72FC3, "vpkuwus128 vr31, vr71, vr101");
}

#[test]
fn test_vmx_vrefp128(){
    assert_asm!(0x1800F638, "vrefp128 vr64, vr30");
}

#[test]
fn test_vmx_vrfim128(){
    assert_asm!(0x18802B30, "vrfim128 vr4, vr5");
}

#[test]
fn test_vmx_vrfin128(){
    assert_asm!(0x1A200B73, "vrfin128 vr17, vr97");
}

#[test]
fn test_vmx_vrfip128(){
    assert_asm!(0x1B605BB2, "vrfip128 vr27, vr75");
}

#[test]
fn test_vmx_vrfiz128(){
    assert_asm!(0x1A8053F0, "vrfiz128 vr20, vr10");
}

#[test]
fn test_vmx_vrlimi128(){
    assert_asm!(0x18796798, "vrlimi128 vr67, vr12, 0x19, 2")
}

#[test]
fn test_vmx_vrlw128(){
    assert_asm!(0x1B002050, "vrlw128 vr24, vr0, vr4");
}

#[test]
fn test_vmx_vrsqrtefp128(){
    assert_asm!(0x19800673, "vrsqrtefp128 vr12, vr96");
}

#[test]
fn test_vmx_vsel128(){
    assert_asm!(0x146CDF5A, "vsel128 vr67, vr76, vr91");
}

#[test]
fn test_vmx_vsldoi128(){
    assert_asm!(0x130BFF30, "vsldoi128 vr24, vr107, vr31, 12");
}

#[test]
fn test_vmx_vslo128(){
    assert_asm!(0x14E08B90, "vslo128 vr7, vr0, vr17");
}

#[test]
fn test_vmx_vslw128(){
    assert_asm!(0x1A1AC0D2, "vslw128 vr16, vr26, vr88");
}

#[test]
fn test_vmx_vspltisw128(){
    assert_asm!(0x1B68A772, "vspltisw128 vr27, vr84, 0x8");
}

#[test]
fn test_vmx_vspltw128(){
    assert_asm!(0x1996EF32, "vspltw128 vr12, vr93, 0x16");
}

#[test]
fn test_vmx_vsraw128(){
    assert_asm!(0x19B71950, "vsraw128 vr13, vr23, vr3");
}

#[test]
fn test_vmx_vsro128(){
    assert_asm!(0x17C3E3D3, "vsro128 vr30, vr3, vr124");
}

#[test]
fn test_vmx_vsrw128(){
    assert_asm!(0x1B9271D3, "vsrw128 vr28, vr18, vr110");
}

#[test]
fn test_vmx_vsubfp128(){
    assert_asm!(0x17692C50, "vsubfp128 vr27, vr73, vr5");
}

#[test]
fn test_vmx_vupkd3d128(){
    assert_asm!(0x19FECFF0, "vupkd3d128 vr15, vr25, 0x1e");
}

#[test]
fn test_vmx_vupkhsb128(){
    assert_asm!(0x1B60FB83, "vupkhsb128 vr27, vr127");
}

#[test]
fn test_vmx_vupklsb128(){
    assert_asm!(0x1A00A3C3, "vupklsb128 vr16, vr116");
}

#[test]
fn test_vmx_vxor128(){
    assert_asm!(0x17E3EF32, "vxor128 vr31, vr99, vr93");
}