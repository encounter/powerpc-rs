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
fn test_vmx_lvewx128() {
    assert_asm!(0x1243388F, "lvewx128 v114, r3, r7");
}

#[test]
fn test_vmx_lvlx128() {
    assert_asm!(0x1085440F, "lvlx128 v100, r5, r8");
}

#[test]
fn test_vmx_lvrx128() {
    assert_asm!(0x108EE44B, "lvrx128 v68, r14, r28");
}

#[test]
fn test_vmx_lvlxl128() {
    assert_asm!(0x1105FE0B, "lvlxl128 v72, r5, r31");
}

#[test]
fn test_vmx_lvrxl128() {
    assert_asm!(0x12A01E4B, "lvrxl128 v85, r0, r3");
}

#[test]
fn test_vmx_lvsl128() {
    assert_asm!(0x138AF00B, "lvsl128 v92, r10, r30");
}

#[test]
fn test_vmx_lvsr128() {
    assert_asm!(0x1016C04F, "lvsr128 v96, r22, r24");
}

#[test]
fn test_vmx_lvx128() {
    assert_asm!(0x120938CF, "lvx128 v112, r9, r7");
}

#[test]
fn test_vmx_lvxl128() {
    assert_asm!(0x12C322CF, "lvxl128 v118, r3, r4");
}

#[test]
fn test_vmx_stvewx128() {
    assert_asm!(0x131BF98F, "stvewx128 v120, r27, r31");
}

#[test]
fn test_vmx_stvlx128() {
    assert_asm!(0x12602D0B, "stvlx128 v83, r0, r5");
}

#[test]
fn test_vmx_stvlxl128() {
    assert_asm!(0x12C3A70B, "stvlxl128 v86, r3, r20");
}

#[test]
fn test_vmx_stvrx128() {
    assert_asm!(0x10B8F54B, "stvrx128 v69, r24, r30");
}

#[test]
fn test_vmx_stvrxl128() {
    assert_asm!(0x10C7074B, "stvrxl128 v70, r7, r0");
}

#[test]
fn test_vmx_stvx128() {
    assert_asm!(0x130341C3, "stvx128 v24, r3, r8");
}

#[test]
fn test_vmx_stvxl128() {
    assert_asm!(0x13E553C3, "stvxl128 v31, r5, r10");
}

#[test]
fn test_vmx_vaddfp128() {
    assert_asm!(0x151E301B, "vaddfp128 v72, v30, v102");
}

#[test]
fn test_vmx_vand128() {
    assert_asm!(0x16900E12, "vand128 v20, v80, v65");
}

#[test]
fn test_vmx_vandc128() {
    assert_asm!(0x15EBFE52, "vandc128 v15, v75, v95");
}

#[test]
fn test_vmx_vctsxs128() {
    assert_asm!(0x1A42D23B, "vctsxs128 v82, v122, 0x2");
}

#[test]
fn test_vmx_vctuxs128() {
    assert_asm!(0x1BEACA78, "vctuxs128 v95, v25, 0xa");
}

#[test]
fn test_vmx_vcmpbfp128() {
    assert_asm!(0x1BA5598E, "vcmpbfp128 v125, v5, v75");
    assert_asm!(0x198D79C2, "vcmpbfp128. v12, v13, v79");
}

#[test]
fn test_vmx_vcmpeqfp128() {
    assert_asm!(0x1800D80B, "vcmpeqfp128 v64, v0, v123");
    assert_asm!(0x1ACD1C43, "vcmpeqfp128. v22, v77, v99");
}

#[test]
fn test_vmx_vcmpequw128() {
    assert_asm!(0x18D0D60A, "vcmpequw128 v70, v80, v90");
    assert_asm!(0x18800A40, "vcmpequw128. v4, v0, v1");
}

#[test]
fn test_vmx_vcmpgefp128() {
    assert_asm!(0x1A8A1483, "vcmpgefp128 v20, v74, v98");
    assert_asm!(0x18EB7CEF, "vcmpgefp128. v103, v107, v111");
}

#[test]
fn test_vmx_vcmpgtfp128() {
    assert_asm!(0x1BD48102, "vcmpgtfp128 v30, v20, v80");
    assert_asm!(0x1B586D68, "vcmpgtfp128. v90, v120, v13");
}

#[test]
fn test_vmx_vcfsx128() {
    assert_asm!(0x18749ABC, "vcfsx128 v99, v19, -0xc");
}

#[test]
fn test_vmx_vcfux128() {
    assert_asm!(0x1A6D1AF8, "vcfux128 v83, v3, 0xd");
}

#[test]
fn test_vmx_vexptefp128() {
    assert_asm!(0x198056B0, "vexptefp128 v12, v10");
}

#[test]
fn test_vmx_vlogefp128() {
    assert_asm!(0x1900FEFB, "vlogefp128 v72, v127");
}

#[test]
fn test_vmx_vmaddcfp128() {
    assert_asm!(0x163B1912, "vmaddcfp128 v17, v27, v67");
}

#[test]
fn test_vmx_vmaddfp128() {
    assert_asm!(0x16B3ECFB, "vmaddfp128 v85, v115, v125");
}

#[test]
fn test_vmx_vmaxfp128() {
    assert_asm!(0x1B274683, "vmaxfp128 v25, v71, v104");
}

#[test]
fn test_vmx_vminfp128() {
    assert_asm!(0x1BE012C0, "vminfp128 v31, v0, v2");
}

#[test]
fn test_vmx_vmrghw128() {
    assert_asm!(0x18CA730B, "vmrghw128 v70, v10, v110");
}

#[test]
fn test_vmx_vmrglw128() {
    assert_asm!(0x1BD2D743, "vmrglw128 v30, v82, v122");
}

#[test]
fn test_vmx_vmsum3fp128() {
    assert_asm!(0x14FBF993, "vmsum3fp128 v7, v27, v127");
}

#[test]
fn test_vmx_vmsum4fp128() {
    assert_asm!(0x14A869D0, "vmsum4fp128 v5, v8, v13");
}

#[test]
fn test_vmx_vmulfp128() {
    assert_asm!(0x1498DCBF, "vmulfp128 v100, v120, v123");
}

#[test]
fn test_vmx_vnmsubfp128() {
    assert_asm!(0x17DBCD53, "vnmsubfp128 v30, v91, v121");
}

#[test]
fn test_vmx_vnor128() {
    assert_asm!(0x176A6290, "vnor128 v27, v10, v12");
}

#[test]
fn test_vmx_vor128() {
    assert_asm!(0x17EC3ADC, "vor128 v127, v12, v7");
}

#[test]
fn test_vmx_vperm128() {
    assert_asm!(0x1661158F, "vperm128 v115, v65, v98, v6");
}

#[test]
fn test_vmx_vpermwi128() {
    assert_asm!(0x19C342DE, "vpermwi128 v110, v72, 99");
}

#[test]
fn test_vmx_vpkd3d128() {
    assert_asm!(0x1935DEDC, "vpkd3d128 v105, v27, 5, 1, 3");
}

#[test]
fn test_vmx_vpkshss128() {
    assert_asm!(0x16C0F62B, "vpkshss128 v86, v96, v126");
}

#[test]
fn test_vmx_vpkshus128() {
    assert_asm!(0x153D6E48, "vpkshus128 v73, v93, v13");
}

#[test]
fn test_vmx_vpkswss128() {
    assert_asm!(0x16FE7280, "vpkswss128 v23, v30, v14");
}

#[test]
fn test_vmx_vpkswus128() {
    assert_asm!(0x161836C3, "vpkswus128 v16, v88, v102");
}

#[test]
fn test_vmx_vpkuhum128() {
    assert_asm!(0x14E3BF02, "vpkuhum128 v7, v67, v87");
}

#[test]
fn test_vmx_vpkuhus128() {
    assert_asm!(0x1600A348, "vpkuhus128 v80, v0, v20");
}

#[test]
fn test_vmx_vpkuwum128() {
    assert_asm!(0x16EACB83, "vpkuwum128 v23, v10, v121");
}

#[test]
fn test_vmx_vpkuwus128() {
    assert_asm!(0x17E72FC3, "vpkuwus128 v31, v71, v101");
}

#[test]
fn test_vmx_vrefp128() {
    assert_asm!(0x1800F638, "vrefp128 v64, v30");
}

#[test]
fn test_vmx_vrfim128() {
    assert_asm!(0x18802B30, "vrfim128 v4, v5");
}

#[test]
fn test_vmx_vrfin128() {
    assert_asm!(0x1A200B73, "vrfin128 v17, v97");
}

#[test]
fn test_vmx_vrfip128() {
    assert_asm!(0x1B605BB2, "vrfip128 v27, v75");
}

#[test]
fn test_vmx_vrfiz128() {
    assert_asm!(0x1A8053F0, "vrfiz128 v20, v10");
}

#[test]
fn test_vmx_vrlimi128() {
    assert_asm!(0x18796798, "vrlimi128 v67, v12, 0x19, 2")
}

#[test]
fn test_vmx_vrlw128() {
    assert_asm!(0x1B002050, "vrlw128 v24, v0, v4");
}

#[test]
fn test_vmx_vrsqrtefp128() {
    assert_asm!(0x19800673, "vrsqrtefp128 v12, v96");
}

#[test]
fn test_vmx_vsel128() {
    assert_asm!(0x146CDF5A, "vsel128 v67, v76, v91");
}

#[test]
fn test_vmx_vsldoi128() {
    assert_asm!(0x130BFF30, "vsldoi128 v24, v107, v31, 12");
}

#[test]
fn test_vmx_vslo128() {
    assert_asm!(0x14E08B90, "vslo128 v7, v0, v17");
}

#[test]
fn test_vmx_vslw128() {
    assert_asm!(0x1A1AC0D2, "vslw128 v16, v26, v88");
}

#[test]
fn test_vmx_vspltisw128() {
    assert_asm!(0x1B68A772, "vspltisw128 v27, v84, 0x8");
}

#[test]
fn test_vmx_vspltw128() {
    assert_asm!(0x1996EF32, "vspltw128 v12, v93, 0x16");
}

#[test]
fn test_vmx_vsraw128() {
    assert_asm!(0x19B71950, "vsraw128 v13, v23, v3");
}

#[test]
fn test_vmx_vsro128() {
    assert_asm!(0x17C3E3D3, "vsro128 v30, v3, v124");
}

#[test]
fn test_vmx_vsrw128() {
    assert_asm!(0x1B9271D3, "vsrw128 v28, v18, v110");
}

#[test]
fn test_vmx_vsubfp128() {
    assert_asm!(0x17692C50, "vsubfp128 v27, v73, v5");
}

#[test]
fn test_vmx_vupkd3d128() {
    assert_asm!(0x19FECFF0, "vupkd3d128 v15, v25, 0x1e");
}

#[test]
fn test_vmx_vupkhsb128() {
    assert_asm!(0x1B60FB83, "vupkhsb128 v27, v127");
}

#[test]
fn test_vmx_vupkhsh128() {
    assert_asm!(0x186017a0, "vupkhsh128 v3, v2");
}

#[test]
fn test_vmx_vupklsb128() {
    assert_asm!(0x1A00A3C3, "vupklsb128 v16, v116");
}

#[test]
fn test_vmx_vupklsh128() {
    assert_asm!(0x186017e0, "vupklsh128 v3, v2");
}

#[test]
fn test_vmx_vxor128() {
    assert_asm!(0x17E3EF32, "vxor128 v31, v99, v93");
}
