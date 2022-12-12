use crate::prelude::*;
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum Opcode {
    Illegal = -1,
    Add,
    Addc,
    Adde,
    Addi,
    Addic,
    Addic_,
    Addis,
    Addme,
    Addze,
    And,
    Andc,
    Andi_,
    Andis_,
    B,
    Bc,
    Bcctr,
    Bclr,
    Cmp,
    Cmpi,
    Cmpl,
    Cmpli,
    Cntlzw,
    Crand,
    Crandc,
    Creqv,
    Crnand,
    Crnor,
    Cror,
    Crorc,
    Crxor,
    Dcbf,
    Dcbi,
    Dcbst,
    Dcbt,
    Dcbtst,
    Dcbz,
    DcbzL,
    Divw,
    Divwu,
    Eciwx,
    Ecowx,
    Eieio,
    Eqv,
    Extsb,
    Extsh,
    Fabs,
    Fadd,
    Fadds,
    Fcmpo,
    Fcmpu,
    Fctiw,
    Fctiwz,
    Fdiv,
    Fdivs,
    Fmadd,
    Fmadds,
    Fmr,
    Fmsub,
    Fmsubs,
    Fmul,
    Fmuls,
    Fnabs,
    Fneg,
    Fnmadd,
    Fnmadds,
    Fnmsub,
    Fnmsubs,
    Fres,
    Frsp,
    Frsqrte,
    Fsel,
    Fsub,
    Fsubs,
    Icbi,
    Isync,
    Lbz,
    Lbzu,
    Lbzux,
    Lbzx,
    Lfd,
    Lfdu,
    Lfdux,
    Lfdx,
    Lfs,
    Lfsu,
    Lfsux,
    Lfsx,
    Lha,
    Lhau,
    Lhaux,
    Lhax,
    Lhbrx,
    Lhz,
    Lhzu,
    Lhzux,
    Lhzx,
    Lmw,
    Lswi,
    Lswx,
    Lwarx,
    Lwbrx,
    Lwz,
    Lwzu,
    Lwzux,
    Lwzx,
    Mcrf,
    Mcrfs,
    Mcrxr,
    Mfcr,
    Mffs,
    Mfmsr,
    Mfspr,
    Mfsr,
    Mfsrin,
    Mftb,
    Mtcrf,
    Mtfsb0,
    Mtfsb1,
    Mtfsf,
    Mtfsfi,
    Mtmsr,
    Mtspr,
    Mtsr,
    Mtsrin,
    Mulhw,
    Mulhwu,
    Mulli,
    Mullw,
    Nand,
    Neg,
    Nor,
    Or,
    Orc,
    Ori,
    Oris,
    PsqL,
    PsqLu,
    PsqLux,
    PsqLx,
    PsqSt,
    PsqStu,
    PsqStux,
    PsqStx,
    PsAbs,
    PsAdd,
    PsCmpo0,
    PsCmpo1,
    PsCmpu0,
    PsCmpu1,
    PsDiv,
    PsMadd,
    PsMadds0,
    PsMadds1,
    PsMerge00,
    PsMerge01,
    PsMerge10,
    PsMerge11,
    PsMr,
    PsMsub,
    PsMul,
    PsMuls0,
    PsMuls1,
    PsNabs,
    PsNeg,
    PsNmadd,
    PsNmsub,
    PsRes,
    PsRsqrte,
    PsSel,
    PsSub,
    PsSum0,
    PsSum1,
    Rfi,
    Rlwimi,
    Rlwinm,
    Rlwnm,
    Sc,
    Slw,
    Sraw,
    Srawi,
    Srw,
    Stb,
    Stbu,
    Stbux,
    Stbx,
    Stfd,
    Stfdu,
    Stfdux,
    Stfdx,
    Stfiwx,
    Stfs,
    Stfsu,
    Stfsux,
    Stfsx,
    Sth,
    Sthbrx,
    Sthu,
    Sthux,
    Sthx,
    Stmw,
    Stswi,
    Stswx,
    Stw,
    Stwbrx,
    Stwcx_,
    Stwu,
    Stwux,
    Stwx,
    Subf,
    Subfc,
    Subfe,
    Subfic,
    Subfme,
    Subfze,
    Sync,
    Tlbie,
    Tlbsync,
    Tw,
    Twi,
    Xor,
    Xori,
    Xoris,
}
#[allow(clippy::all)]
impl Opcode {
    pub(crate) fn _mnemonic(self) -> &'static str {
        match self {
            Opcode::Illegal => "<illegal>",
            Opcode::Add => "add",
            Opcode::Addc => "addc",
            Opcode::Adde => "adde",
            Opcode::Addi => "addi",
            Opcode::Addic => "addic",
            Opcode::Addic_ => "addic.",
            Opcode::Addis => "addis",
            Opcode::Addme => "addme",
            Opcode::Addze => "addze",
            Opcode::And => "and",
            Opcode::Andc => "andc",
            Opcode::Andi_ => "andi.",
            Opcode::Andis_ => "andis.",
            Opcode::B => "b",
            Opcode::Bc => "bc",
            Opcode::Bcctr => "bcctr",
            Opcode::Bclr => "bclr",
            Opcode::Cmp => "cmp",
            Opcode::Cmpi => "cmpi",
            Opcode::Cmpl => "cmpl",
            Opcode::Cmpli => "cmpli",
            Opcode::Cntlzw => "cntlzw",
            Opcode::Crand => "crand",
            Opcode::Crandc => "crandc",
            Opcode::Creqv => "creqv",
            Opcode::Crnand => "crnand",
            Opcode::Crnor => "crnor",
            Opcode::Cror => "cror",
            Opcode::Crorc => "crorc",
            Opcode::Crxor => "crxor",
            Opcode::Dcbf => "dcbf",
            Opcode::Dcbi => "dcbi",
            Opcode::Dcbst => "dcbst",
            Opcode::Dcbt => "dcbt",
            Opcode::Dcbtst => "dcbtst",
            Opcode::Dcbz => "dcbz",
            Opcode::DcbzL => "dcbz_l",
            Opcode::Divw => "divw",
            Opcode::Divwu => "divwu",
            Opcode::Eciwx => "eciwx",
            Opcode::Ecowx => "ecowx",
            Opcode::Eieio => "eieio",
            Opcode::Eqv => "eqv",
            Opcode::Extsb => "extsb",
            Opcode::Extsh => "extsh",
            Opcode::Fabs => "fabs",
            Opcode::Fadd => "fadd",
            Opcode::Fadds => "fadds",
            Opcode::Fcmpo => "fcmpo",
            Opcode::Fcmpu => "fcmpu",
            Opcode::Fctiw => "fctiw",
            Opcode::Fctiwz => "fctiwz",
            Opcode::Fdiv => "fdiv",
            Opcode::Fdivs => "fdivs",
            Opcode::Fmadd => "fmadd",
            Opcode::Fmadds => "fmadds",
            Opcode::Fmr => "fmr",
            Opcode::Fmsub => "fmsub",
            Opcode::Fmsubs => "fmsubs",
            Opcode::Fmul => "fmul",
            Opcode::Fmuls => "fmuls",
            Opcode::Fnabs => "fnabs",
            Opcode::Fneg => "fneg",
            Opcode::Fnmadd => "fnmadd",
            Opcode::Fnmadds => "fnmadds",
            Opcode::Fnmsub => "fnmsub",
            Opcode::Fnmsubs => "fnmsubs",
            Opcode::Fres => "fres",
            Opcode::Frsp => "frsp",
            Opcode::Frsqrte => "frsqrte",
            Opcode::Fsel => "fsel",
            Opcode::Fsub => "fsub",
            Opcode::Fsubs => "fsubs",
            Opcode::Icbi => "icbi",
            Opcode::Isync => "isync",
            Opcode::Lbz => "lbz",
            Opcode::Lbzu => "lbzu",
            Opcode::Lbzux => "lbzux",
            Opcode::Lbzx => "lbzx",
            Opcode::Lfd => "lfd",
            Opcode::Lfdu => "lfdu",
            Opcode::Lfdux => "lfdux",
            Opcode::Lfdx => "lfdx",
            Opcode::Lfs => "lfs",
            Opcode::Lfsu => "lfsu",
            Opcode::Lfsux => "lfsux",
            Opcode::Lfsx => "lfsx",
            Opcode::Lha => "lha",
            Opcode::Lhau => "lhau",
            Opcode::Lhaux => "lhaux",
            Opcode::Lhax => "lhax",
            Opcode::Lhbrx => "lhbrx",
            Opcode::Lhz => "lhz",
            Opcode::Lhzu => "lhzu",
            Opcode::Lhzux => "lhzux",
            Opcode::Lhzx => "lhzx",
            Opcode::Lmw => "lmw",
            Opcode::Lswi => "lswi",
            Opcode::Lswx => "lswx",
            Opcode::Lwarx => "lwarx",
            Opcode::Lwbrx => "lwbrx",
            Opcode::Lwz => "lwz",
            Opcode::Lwzu => "lwzu",
            Opcode::Lwzux => "lwzux",
            Opcode::Lwzx => "lwzx",
            Opcode::Mcrf => "mcrf",
            Opcode::Mcrfs => "mcrfs",
            Opcode::Mcrxr => "mcrxr",
            Opcode::Mfcr => "mfcr",
            Opcode::Mffs => "mffs",
            Opcode::Mfmsr => "mfmsr",
            Opcode::Mfspr => "mfspr",
            Opcode::Mfsr => "mfsr",
            Opcode::Mfsrin => "mfsrin",
            Opcode::Mftb => "mftb",
            Opcode::Mtcrf => "mtcrf",
            Opcode::Mtfsb0 => "mtfsb0",
            Opcode::Mtfsb1 => "mtfsb1",
            Opcode::Mtfsf => "mtfsf",
            Opcode::Mtfsfi => "mtfsfi",
            Opcode::Mtmsr => "mtmsr",
            Opcode::Mtspr => "mtspr",
            Opcode::Mtsr => "mtsr",
            Opcode::Mtsrin => "mtsrin",
            Opcode::Mulhw => "mulhw",
            Opcode::Mulhwu => "mulhwu",
            Opcode::Mulli => "mulli",
            Opcode::Mullw => "mullw",
            Opcode::Nand => "nand",
            Opcode::Neg => "neg",
            Opcode::Nor => "nor",
            Opcode::Or => "or",
            Opcode::Orc => "orc",
            Opcode::Ori => "ori",
            Opcode::Oris => "oris",
            Opcode::PsqL => "psq_l",
            Opcode::PsqLu => "psq_lu",
            Opcode::PsqLux => "psq_lux",
            Opcode::PsqLx => "psq_lx",
            Opcode::PsqSt => "psq_st",
            Opcode::PsqStu => "psq_stu",
            Opcode::PsqStux => "psq_stux",
            Opcode::PsqStx => "psq_stx",
            Opcode::PsAbs => "ps_abs",
            Opcode::PsAdd => "ps_add",
            Opcode::PsCmpo0 => "ps_cmpo0",
            Opcode::PsCmpo1 => "ps_cmpo1",
            Opcode::PsCmpu0 => "ps_cmpu0",
            Opcode::PsCmpu1 => "ps_cmpu1",
            Opcode::PsDiv => "ps_div",
            Opcode::PsMadd => "ps_madd",
            Opcode::PsMadds0 => "ps_madds0",
            Opcode::PsMadds1 => "ps_madds1",
            Opcode::PsMerge00 => "ps_merge00",
            Opcode::PsMerge01 => "ps_merge01",
            Opcode::PsMerge10 => "ps_merge10",
            Opcode::PsMerge11 => "ps_merge11",
            Opcode::PsMr => "ps_mr",
            Opcode::PsMsub => "ps_msub",
            Opcode::PsMul => "ps_mul",
            Opcode::PsMuls0 => "ps_muls0",
            Opcode::PsMuls1 => "ps_muls1",
            Opcode::PsNabs => "ps_nabs",
            Opcode::PsNeg => "ps_neg",
            Opcode::PsNmadd => "ps_nmadd",
            Opcode::PsNmsub => "ps_nmsub",
            Opcode::PsRes => "ps_res",
            Opcode::PsRsqrte => "ps_rsqrte",
            Opcode::PsSel => "ps_sel",
            Opcode::PsSub => "ps_sub",
            Opcode::PsSum0 => "ps_sum0",
            Opcode::PsSum1 => "ps_sum1",
            Opcode::Rfi => "rfi",
            Opcode::Rlwimi => "rlwimi",
            Opcode::Rlwinm => "rlwinm",
            Opcode::Rlwnm => "rlwnm",
            Opcode::Sc => "sc",
            Opcode::Slw => "slw",
            Opcode::Sraw => "sraw",
            Opcode::Srawi => "srawi",
            Opcode::Srw => "srw",
            Opcode::Stb => "stb",
            Opcode::Stbu => "stbu",
            Opcode::Stbux => "stbux",
            Opcode::Stbx => "stbx",
            Opcode::Stfd => "stfd",
            Opcode::Stfdu => "stfdu",
            Opcode::Stfdux => "stfdux",
            Opcode::Stfdx => "stfdx",
            Opcode::Stfiwx => "stfiwx",
            Opcode::Stfs => "stfs",
            Opcode::Stfsu => "stfsu",
            Opcode::Stfsux => "stfsux",
            Opcode::Stfsx => "stfsx",
            Opcode::Sth => "sth",
            Opcode::Sthbrx => "sthbrx",
            Opcode::Sthu => "sthu",
            Opcode::Sthux => "sthux",
            Opcode::Sthx => "sthx",
            Opcode::Stmw => "stmw",
            Opcode::Stswi => "stswi",
            Opcode::Stswx => "stswx",
            Opcode::Stw => "stw",
            Opcode::Stwbrx => "stwbrx",
            Opcode::Stwcx_ => "stwcx.",
            Opcode::Stwu => "stwu",
            Opcode::Stwux => "stwux",
            Opcode::Stwx => "stwx",
            Opcode::Subf => "subf",
            Opcode::Subfc => "subfc",
            Opcode::Subfe => "subfe",
            Opcode::Subfic => "subfic",
            Opcode::Subfme => "subfme",
            Opcode::Subfze => "subfze",
            Opcode::Sync => "sync",
            Opcode::Tlbie => "tlbie",
            Opcode::Tlbsync => "tlbsync",
            Opcode::Tw => "tw",
            Opcode::Twi => "twi",
            Opcode::Xor => "xor",
            Opcode::Xori => "xori",
            Opcode::Xoris => "xoris",
        }
    }
    pub(crate) fn _detect(code: u32) -> Self {
        if code & 0xfc0007fe == 0x7c000214 {
            return Opcode::Add;
        }
        if code & 0xfc0007fe == 0x7c000014 {
            return Opcode::Addc;
        }
        if code & 0xfc0007fe == 0x7c000114 {
            return Opcode::Adde;
        }
        if code & 0xfc000000 == 0x38000000 {
            return Opcode::Addi;
        }
        if code & 0xfc000000 == 0x30000000 {
            return Opcode::Addic;
        }
        if code & 0xfc000000 == 0x34000000 {
            return Opcode::Addic_;
        }
        if code & 0xfc000000 == 0x3c000000 {
            return Opcode::Addis;
        }
        if code & 0xfc00fbfe == 0x7c0001d4 {
            return Opcode::Addme;
        }
        if code & 0xfc00fbfe == 0x7c000194 {
            return Opcode::Addze;
        }
        if code & 0xfc0007fe == 0x7c000038 {
            return Opcode::And;
        }
        if code & 0xfc0007fe == 0x7c000078 {
            return Opcode::Andc;
        }
        if code & 0xfc000000 == 0x70000000 {
            return Opcode::Andi_;
        }
        if code & 0xfc000000 == 0x74000000 {
            return Opcode::Andis_;
        }
        if code & 0xfc000000 == 0x48000000 {
            return Opcode::B;
        }
        if code & 0xfc000000 == 0x40000000 {
            return Opcode::Bc;
        }
        if code & 0xfc007ffe == 0x4c000420 {
            return Opcode::Bcctr;
        }
        if code & 0xfc007ffe == 0x4c000020 {
            return Opcode::Bclr;
        }
        if code & 0xfc4007ff == 0x7c000000 {
            return Opcode::Cmp;
        }
        if code & 0xfc400000 == 0x2c000000 {
            return Opcode::Cmpi;
        }
        if code & 0xfc4007ff == 0x7c000040 {
            return Opcode::Cmpl;
        }
        if code & 0xfc400000 == 0x28000000 {
            return Opcode::Cmpli;
        }
        if code & 0xfc00fffe == 0x7c000034 {
            return Opcode::Cntlzw;
        }
        if code & 0xfc0007ff == 0x4c000202 {
            return Opcode::Crand;
        }
        if code & 0xfc0007ff == 0x4c000102 {
            return Opcode::Crandc;
        }
        if code & 0xfc0007ff == 0x4c000242 {
            return Opcode::Creqv;
        }
        if code & 0xfc0007ff == 0x4c0001c2 {
            return Opcode::Crnand;
        }
        if code & 0xfc0007ff == 0x4c000042 {
            return Opcode::Crnor;
        }
        if code & 0xfc0007ff == 0x4c000382 {
            return Opcode::Cror;
        }
        if code & 0xfc0007ff == 0x4c000342 {
            return Opcode::Crorc;
        }
        if code & 0xfc0007ff == 0x4c000182 {
            return Opcode::Crxor;
        }
        if code & 0xffe007ff == 0x7c0000ac {
            return Opcode::Dcbf;
        }
        if code & 0xffe007ff == 0x7c0003ac {
            return Opcode::Dcbi;
        }
        if code & 0xffe007ff == 0x7c00006c {
            return Opcode::Dcbst;
        }
        if code & 0xffe007ff == 0x7c00022c {
            return Opcode::Dcbt;
        }
        if code & 0xffe007ff == 0x7c0001ec {
            return Opcode::Dcbtst;
        }
        if code & 0xffe007ff == 0x7c0007ec {
            return Opcode::Dcbz;
        }
        if code & 0xffe007ff == 0x100007ec {
            return Opcode::DcbzL;
        }
        if code & 0xfc0003fe == 0x7c0003d6 {
            return Opcode::Divw;
        }
        if code & 0xfc0003fe == 0x7c000396 {
            return Opcode::Divwu;
        }
        if code & 0xfc0007ff == 0x7c00026c {
            return Opcode::Eciwx;
        }
        if code & 0xfc0007ff == 0x7c00036c {
            return Opcode::Ecowx;
        }
        if code & 0xffffffff == 0x7c0006ac {
            return Opcode::Eieio;
        }
        if code & 0xfc0003fe == 0x7c000238 {
            return Opcode::Eqv;
        }
        if code & 0xfc00fffe == 0x7c000774 {
            return Opcode::Extsb;
        }
        if code & 0xfc00fffe == 0x7c000734 {
            return Opcode::Extsh;
        }
        if code & 0xfc1f07fe == 0xfc000210 {
            return Opcode::Fabs;
        }
        if code & 0xfc0007fe == 0xfc00002a {
            return Opcode::Fadd;
        }
        if code & 0xfc0007fe == 0xec00002a {
            return Opcode::Fadds;
        }
        if code & 0xfc6007ff == 0xfc000040 {
            return Opcode::Fcmpo;
        }
        if code & 0xfc6007ff == 0xfc000000 {
            return Opcode::Fcmpu;
        }
        if code & 0xfc1f07fe == 0xfc00001c {
            return Opcode::Fctiw;
        }
        if code & 0xfc1f07fe == 0xfc00001e {
            return Opcode::Fctiwz;
        }
        if code & 0xfc0007fe == 0xfc000024 {
            return Opcode::Fdiv;
        }
        if code & 0xfc0007fe == 0xec000024 {
            return Opcode::Fdivs;
        }
        if code & 0xfc00003e == 0xfc00003a {
            return Opcode::Fmadd;
        }
        if code & 0xfc00003e == 0xec00003a {
            return Opcode::Fmadds;
        }
        if code & 0xfc1f07fe == 0xfc000090 {
            return Opcode::Fmr;
        }
        if code & 0xfc00003e == 0xfc000038 {
            return Opcode::Fmsub;
        }
        if code & 0xfc00003e == 0xec000038 {
            return Opcode::Fmsubs;
        }
        if code & 0xfc00f83e == 0xfc000032 {
            return Opcode::Fmul;
        }
        if code & 0xfc00f83e == 0xec000032 {
            return Opcode::Fmuls;
        }
        if code & 0xfc1f07fe == 0xfc000110 {
            return Opcode::Fnabs;
        }
        if code & 0xfc1f07fe == 0xfc000050 {
            return Opcode::Fneg;
        }
        if code & 0xfc00003e == 0xfc00003e {
            return Opcode::Fnmadd;
        }
        if code & 0xfc00003e == 0xec00003e {
            return Opcode::Fnmadds;
        }
        if code & 0xfc00003e == 0xfc00003c {
            return Opcode::Fnmsub;
        }
        if code & 0xfc00003e == 0xec00003c {
            return Opcode::Fnmsubs;
        }
        if code & 0xfc1f07fe == 0xec000030 {
            return Opcode::Fres;
        }
        if code & 0xfc1f07fe == 0xfc000018 {
            return Opcode::Frsp;
        }
        if code & 0xfc1f07fe == 0xfc000034 {
            return Opcode::Frsqrte;
        }
        if code & 0xfc00003e == 0xfc00002e {
            return Opcode::Fsel;
        }
        if code & 0xfc0007fe == 0xfc000028 {
            return Opcode::Fsub;
        }
        if code & 0xfc0007fe == 0xec000028 {
            return Opcode::Fsubs;
        }
        if code & 0xffe007ff == 0x7c0007ac {
            return Opcode::Icbi;
        }
        if code & 0xffffffff == 0x4c00012c {
            return Opcode::Isync;
        }
        if code & 0xfc000000 == 0x88000000 {
            return Opcode::Lbz;
        }
        if code & 0xfc000000 == 0x8c000000 {
            return Opcode::Lbzu;
        }
        if code & 0xfc0007ff == 0x7c0000ee {
            return Opcode::Lbzux;
        }
        if code & 0xfc0007ff == 0x7c0000ae {
            return Opcode::Lbzx;
        }
        if code & 0xfc000000 == 0xc8000000 {
            return Opcode::Lfd;
        }
        if code & 0xfc000000 == 0xcc000000 {
            return Opcode::Lfdu;
        }
        if code & 0xfc0007ff == 0x7c0004ee {
            return Opcode::Lfdux;
        }
        if code & 0xfc0007ff == 0x7c0004ae {
            return Opcode::Lfdx;
        }
        if code & 0xfc000000 == 0xc0000000 {
            return Opcode::Lfs;
        }
        if code & 0xfc000000 == 0xc4000000 {
            return Opcode::Lfsu;
        }
        if code & 0xfc0007ff == 0x7c00046e {
            return Opcode::Lfsux;
        }
        if code & 0xfc0007ff == 0x7c00042e {
            return Opcode::Lfsx;
        }
        if code & 0xfc000000 == 0xa8000000 {
            return Opcode::Lha;
        }
        if code & 0xfc000000 == 0xac000000 {
            return Opcode::Lhau;
        }
        if code & 0xfc0007ff == 0x7c0002ee {
            return Opcode::Lhaux;
        }
        if code & 0xfc0007ff == 0x7c0002ae {
            return Opcode::Lhax;
        }
        if code & 0xfc0007ff == 0x7c00062c {
            return Opcode::Lhbrx;
        }
        if code & 0xfc000000 == 0xa0000000 {
            return Opcode::Lhz;
        }
        if code & 0xfc000000 == 0xa4000000 {
            return Opcode::Lhzu;
        }
        if code & 0xfc0007ff == 0x7c00026e {
            return Opcode::Lhzux;
        }
        if code & 0xfc0007ff == 0x7c00022e {
            return Opcode::Lhzx;
        }
        if code & 0xfc000000 == 0xb8000000 {
            return Opcode::Lmw;
        }
        if code & 0xfc0007ff == 0x7c0004aa {
            return Opcode::Lswi;
        }
        if code & 0xfc0007ff == 0x7c00042a {
            return Opcode::Lswx;
        }
        if code & 0xfc0007ff == 0x7c000028 {
            return Opcode::Lwarx;
        }
        if code & 0xfc0007ff == 0x7c00042c {
            return Opcode::Lwbrx;
        }
        if code & 0xfc000000 == 0x80000000 {
            return Opcode::Lwz;
        }
        if code & 0xfc000000 == 0x84000000 {
            return Opcode::Lwzu;
        }
        if code & 0xfc0007ff == 0x7c00006e {
            return Opcode::Lwzux;
        }
        if code & 0xfc0007ff == 0x7c00002e {
            return Opcode::Lwzx;
        }
        if code & 0xfc63ffff == 0x4c000000 {
            return Opcode::Mcrf;
        }
        if code & 0xfc63ffff == 0xfc000080 {
            return Opcode::Mcrfs;
        }
        if code & 0xfc7fffff == 0x7c000400 {
            return Opcode::Mcrxr;
        }
        if code & 0xfc1fffff == 0x7c000026 {
            return Opcode::Mfcr;
        }
        if code & 0xfc1ffffe == 0xfc00048e {
            return Opcode::Mffs;
        }
        if code & 0xfc1fffff == 0x7c0000a6 {
            return Opcode::Mfmsr;
        }
        if code & 0xfc0007ff == 0x7c0002a6 {
            return Opcode::Mfspr;
        }
        if code & 0xfc10ffff == 0x7c0004a6 {
            return Opcode::Mfsr;
        }
        if code & 0xfc1f07ff == 0x7c000526 {
            return Opcode::Mfsrin;
        }
        if code & 0xfc0007ff == 0x7c0002e6 {
            return Opcode::Mftb;
        }
        if code & 0xfc100fff == 0x7c000120 {
            return Opcode::Mtcrf;
        }
        if code & 0xfc1ffffe == 0xfc00008c {
            return Opcode::Mtfsb0;
        }
        if code & 0xfc1ffffe == 0xfc00004c {
            return Opcode::Mtfsb1;
        }
        if code & 0xfe0107fe == 0xfc00058e {
            return Opcode::Mtfsf;
        }
        if code & 0xfc7f0ffe == 0xfc00010c {
            return Opcode::Mtfsfi;
        }
        if code & 0xfc1fffff == 0x7c000124 {
            return Opcode::Mtmsr;
        }
        if code & 0xfc0007ff == 0x7c0003a6 {
            return Opcode::Mtspr;
        }
        if code & 0xfc10ffff == 0x7c0001a4 {
            return Opcode::Mtsr;
        }
        if code & 0xfc1f07ff == 0x7c0001e4 {
            return Opcode::Mtsrin;
        }
        if code & 0xfc0007fe == 0x7c000096 {
            return Opcode::Mulhw;
        }
        if code & 0xfc0007fe == 0x7c000016 {
            return Opcode::Mulhwu;
        }
        if code & 0xfc000000 == 0x1c000000 {
            return Opcode::Mulli;
        }
        if code & 0xfc0003fe == 0x7c0001d6 {
            return Opcode::Mullw;
        }
        if code & 0xfc0007fe == 0x7c0003b8 {
            return Opcode::Nand;
        }
        if code & 0xfc00fffe == 0x7c0000d0 {
            return Opcode::Neg;
        }
        if code & 0xfc0007fe == 0x7c0000f8 {
            return Opcode::Nor;
        }
        if code & 0xfc0007fe == 0x7c000378 {
            return Opcode::Or;
        }
        if code & 0xfc0007fe == 0x7c000338 {
            return Opcode::Orc;
        }
        if code & 0xfc000000 == 0x60000000 {
            return Opcode::Ori;
        }
        if code & 0xfc000000 == 0x64000000 {
            return Opcode::Oris;
        }
        if code & 0xfc000000 == 0xe0000000 {
            return Opcode::PsqL;
        }
        if code & 0xfc000000 == 0xe4000000 {
            return Opcode::PsqLu;
        }
        if code & 0xfc00007f == 0x1000004c {
            return Opcode::PsqLux;
        }
        if code & 0xfc00007f == 0x1000000c {
            return Opcode::PsqLx;
        }
        if code & 0xfc000000 == 0xf0000000 {
            return Opcode::PsqSt;
        }
        if code & 0xfc000000 == 0xf4000000 {
            return Opcode::PsqStu;
        }
        if code & 0xfc00007f == 0x1000004e {
            return Opcode::PsqStux;
        }
        if code & 0xfc00007f == 0x1000000e {
            return Opcode::PsqStx;
        }
        if code & 0xfc1f07fe == 0x10000210 {
            return Opcode::PsAbs;
        }
        if code & 0xfc0007fe == 0x1000002a {
            return Opcode::PsAdd;
        }
        if code & 0xfc6007ff == 0x10000040 {
            return Opcode::PsCmpo0;
        }
        if code & 0xfc6007ff == 0x100000c0 {
            return Opcode::PsCmpo1;
        }
        if code & 0xfc6007ff == 0x10000000 {
            return Opcode::PsCmpu0;
        }
        if code & 0xfc6007ff == 0x10000080 {
            return Opcode::PsCmpu1;
        }
        if code & 0xfc0007fe == 0x10000024 {
            return Opcode::PsDiv;
        }
        if code & 0xfc00003e == 0x1000003a {
            return Opcode::PsMadd;
        }
        if code & 0xfc00003e == 0x1000001c {
            return Opcode::PsMadds0;
        }
        if code & 0xfc00003e == 0x1000001e {
            return Opcode::PsMadds1;
        }
        if code & 0xfc0007fe == 0x10000420 {
            return Opcode::PsMerge00;
        }
        if code & 0xfc0007fe == 0x10000460 {
            return Opcode::PsMerge01;
        }
        if code & 0xfc0007fe == 0x100004a0 {
            return Opcode::PsMerge10;
        }
        if code & 0xfc0007fe == 0x100004e0 {
            return Opcode::PsMerge11;
        }
        if code & 0xfc1f07fe == 0x10000090 {
            return Opcode::PsMr;
        }
        if code & 0xfc00003e == 0x10000038 {
            return Opcode::PsMsub;
        }
        if code & 0xfc00f83e == 0x10000032 {
            return Opcode::PsMul;
        }
        if code & 0xfc00f83e == 0x10000018 {
            return Opcode::PsMuls0;
        }
        if code & 0xfc00f83e == 0x1000001a {
            return Opcode::PsMuls1;
        }
        if code & 0xfc1f07fe == 0x10000110 {
            return Opcode::PsNabs;
        }
        if code & 0xfc1f07fe == 0x10000050 {
            return Opcode::PsNeg;
        }
        if code & 0xfc00003e == 0x1000003e {
            return Opcode::PsNmadd;
        }
        if code & 0xfc00003e == 0x1000003c {
            return Opcode::PsNmsub;
        }
        if code & 0xfc1f07fe == 0x10000030 {
            return Opcode::PsRes;
        }
        if code & 0xfc1f07fe == 0x10000034 {
            return Opcode::PsRsqrte;
        }
        if code & 0xfc00003e == 0x1000002e {
            return Opcode::PsSel;
        }
        if code & 0xfc0007fe == 0x10000028 {
            return Opcode::PsSub;
        }
        if code & 0xfc00003e == 0x10000014 {
            return Opcode::PsSum0;
        }
        if code & 0xfc00003e == 0x10000016 {
            return Opcode::PsSum1;
        }
        if code & 0xfffff801 == 0x4c000000 {
            return Opcode::Rfi;
        }
        if code & 0xfc000000 == 0x50000000 {
            return Opcode::Rlwimi;
        }
        if code & 0xfc000000 == 0x54000000 {
            return Opcode::Rlwinm;
        }
        if code & 0xfc000000 == 0x5c000000 {
            return Opcode::Rlwnm;
        }
        if code & 0xffffffff == 0x44000002 {
            return Opcode::Sc;
        }
        if code & 0xfc0007fe == 0x7c000030 {
            return Opcode::Slw;
        }
        if code & 0xfc0007fe == 0x7c000630 {
            return Opcode::Sraw;
        }
        if code & 0xfc0007fe == 0x7c000670 {
            return Opcode::Srawi;
        }
        if code & 0xfc0007fe == 0x7c000430 {
            return Opcode::Srw;
        }
        if code & 0xfc000000 == 0x98000000 {
            return Opcode::Stb;
        }
        if code & 0xfc000000 == 0x9c000000 {
            return Opcode::Stbu;
        }
        if code & 0xfc0007ff == 0x7c0001ee {
            return Opcode::Stbux;
        }
        if code & 0xfc0007ff == 0x7c0001ae {
            return Opcode::Stbx;
        }
        if code & 0xfc000000 == 0xd8000000 {
            return Opcode::Stfd;
        }
        if code & 0xfc000000 == 0xdc000000 {
            return Opcode::Stfdu;
        }
        if code & 0xfc0007ff == 0x7c0005ee {
            return Opcode::Stfdux;
        }
        if code & 0xfc0007ff == 0x7c0005ae {
            return Opcode::Stfdx;
        }
        if code & 0xfc0007ff == 0x7c0007ae {
            return Opcode::Stfiwx;
        }
        if code & 0xfc000000 == 0xd0000000 {
            return Opcode::Stfs;
        }
        if code & 0xfc000000 == 0xd4000000 {
            return Opcode::Stfsu;
        }
        if code & 0xfc0007ff == 0x7c00056e {
            return Opcode::Stfsux;
        }
        if code & 0xfc0007ff == 0x7c00052e {
            return Opcode::Stfsx;
        }
        if code & 0xfc000000 == 0xb0000000 {
            return Opcode::Sth;
        }
        if code & 0xfc0007ff == 0x7c00072c {
            return Opcode::Sthbrx;
        }
        if code & 0xfc000000 == 0xb4000000 {
            return Opcode::Sthu;
        }
        if code & 0xfc0007ff == 0x7c00036e {
            return Opcode::Sthux;
        }
        if code & 0xfc0007ff == 0x7c00032e {
            return Opcode::Sthx;
        }
        if code & 0xfc000000 == 0xbc000000 {
            return Opcode::Stmw;
        }
        if code & 0xfc0007ff == 0x7c0005aa {
            return Opcode::Stswi;
        }
        if code & 0xfc0007ff == 0x7c00052a {
            return Opcode::Stswx;
        }
        if code & 0xfc000000 == 0x90000000 {
            return Opcode::Stw;
        }
        if code & 0xfc0007ff == 0x7c00052c {
            return Opcode::Stwbrx;
        }
        if code & 0xfc0007ff == 0x7c00012d {
            return Opcode::Stwcx_;
        }
        if code & 0xfc000000 == 0x94000000 {
            return Opcode::Stwu;
        }
        if code & 0xfc0007ff == 0x7c00016e {
            return Opcode::Stwux;
        }
        if code & 0xfc0007ff == 0x7c00012e {
            return Opcode::Stwx;
        }
        if code & 0xfc0003fe == 0x7c000050 {
            return Opcode::Subf;
        }
        if code & 0xfc0003fe == 0x7c000010 {
            return Opcode::Subfc;
        }
        if code & 0xfc0003fe == 0x7c000110 {
            return Opcode::Subfe;
        }
        if code & 0xfc000000 == 0x20000000 {
            return Opcode::Subfic;
        }
        if code & 0xfc00fbfe == 0x7c0001d0 {
            return Opcode::Subfme;
        }
        if code & 0xfc00fbfe == 0x7c000190 {
            return Opcode::Subfze;
        }
        if code & 0xffffffff == 0x7c0004ac {
            return Opcode::Sync;
        }
        if code & 0xffff07ff == 0x7c000264 {
            return Opcode::Tlbie;
        }
        if code & 0xffffffff == 0x7c00046c {
            return Opcode::Tlbsync;
        }
        if code & 0xfc0007ff == 0x7c000008 {
            return Opcode::Tw;
        }
        if code & 0xfc000000 == 0xc000000 {
            return Opcode::Twi;
        }
        if code & 0xfc0007fe == 0x7c000278 {
            return Opcode::Xor;
        }
        if code & 0xfc000000 == 0x68000000 {
            return Opcode::Xori;
        }
        if code & 0xfc000000 == 0x6c000000 {
            return Opcode::Xoris;
        }
        Opcode::Illegal
    }
}
#[allow(non_camel_case_types)]
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum Field {
    simm(Simm),
    uimm(Uimm),
    offset(Offset),
    ps_offset(Offset),
    BO(OpaqueU),
    BI(CRBit),
    BH(OpaqueU),
    BD(BranchDest),
    LI(BranchDest),
    SH(OpaqueU),
    MB(OpaqueU),
    ME(OpaqueU),
    rS(GPR),
    rD(GPR),
    rA(GPR),
    rB(GPR),
    rC(GPR),
    sr(SR),
    spr(SPR),
    frS(FPR),
    frD(FPR),
    frA(FPR),
    frB(FPR),
    frC(FPR),
    crbD(CRBit),
    crbA(CRBit),
    crbB(CRBit),
    crfD(CRField),
    crfS(CRField),
    crm(OpaqueU),
    ps_I(GQR),
    ps_IX(GQR),
    ps_W(OpaqueU),
    ps_WX(OpaqueU),
    NB(OpaqueU),
    tbr(OpaqueU),
    mtfsf_FM(OpaqueU),
    mtfsf_IMM(OpaqueU),
    spr_SPRG(OpaqueU),
    spr_BAT(OpaqueU),
    TO(OpaqueU),
    L(OpaqueU),
    xer,
    ctr,
    lr,
}
impl Field {
    pub fn argument(&self) -> Option<Argument> {
        match self {
            Field::simm(x) => Some(Argument::Simm(*x)),
            Field::uimm(x) => Some(Argument::Uimm(*x)),
            Field::offset(x) => Some(Argument::Offset(*x)),
            Field::ps_offset(x) => Some(Argument::Offset(*x)),
            Field::BO(x) => Some(Argument::OpaqueU(*x)),
            Field::BI(x) => Some(Argument::CRBit(*x)),
            Field::BH(x) => Some(Argument::OpaqueU(*x)),
            Field::BD(x) => Some(Argument::BranchDest(*x)),
            Field::LI(x) => Some(Argument::BranchDest(*x)),
            Field::SH(x) => Some(Argument::OpaqueU(*x)),
            Field::MB(x) => Some(Argument::OpaqueU(*x)),
            Field::ME(x) => Some(Argument::OpaqueU(*x)),
            Field::rS(x) => Some(Argument::GPR(*x)),
            Field::rD(x) => Some(Argument::GPR(*x)),
            Field::rA(x) => Some(Argument::GPR(*x)),
            Field::rB(x) => Some(Argument::GPR(*x)),
            Field::rC(x) => Some(Argument::GPR(*x)),
            Field::sr(x) => Some(Argument::SR(*x)),
            Field::spr(x) => Some(Argument::SPR(*x)),
            Field::frS(x) => Some(Argument::FPR(*x)),
            Field::frD(x) => Some(Argument::FPR(*x)),
            Field::frA(x) => Some(Argument::FPR(*x)),
            Field::frB(x) => Some(Argument::FPR(*x)),
            Field::frC(x) => Some(Argument::FPR(*x)),
            Field::crbD(x) => Some(Argument::CRBit(*x)),
            Field::crbA(x) => Some(Argument::CRBit(*x)),
            Field::crbB(x) => Some(Argument::CRBit(*x)),
            Field::crfD(x) => Some(Argument::CRField(*x)),
            Field::crfS(x) => Some(Argument::CRField(*x)),
            Field::crm(x) => Some(Argument::OpaqueU(*x)),
            Field::ps_I(x) => Some(Argument::GQR(*x)),
            Field::ps_IX(x) => Some(Argument::GQR(*x)),
            Field::ps_W(x) => Some(Argument::OpaqueU(*x)),
            Field::ps_WX(x) => Some(Argument::OpaqueU(*x)),
            Field::NB(x) => Some(Argument::OpaqueU(*x)),
            Field::tbr(x) => Some(Argument::OpaqueU(*x)),
            Field::mtfsf_FM(x) => Some(Argument::OpaqueU(*x)),
            Field::mtfsf_IMM(x) => Some(Argument::OpaqueU(*x)),
            Field::spr_SPRG(x) => Some(Argument::OpaqueU(*x)),
            Field::spr_BAT(x) => Some(Argument::OpaqueU(*x)),
            Field::TO(x) => Some(Argument::OpaqueU(*x)),
            Field::L(x) => Some(Argument::OpaqueU(*x)),
            _ => None,
        }
    }
    pub fn name(&self) -> &'static str {
        match self {
            Field::simm(_) => "simm",
            Field::uimm(_) => "uimm",
            Field::offset(_) => "offset",
            Field::ps_offset(_) => "ps_offset",
            Field::BO(_) => "BO",
            Field::BI(_) => "BI",
            Field::BH(_) => "BH",
            Field::BD(_) => "BD",
            Field::LI(_) => "LI",
            Field::SH(_) => "SH",
            Field::MB(_) => "MB",
            Field::ME(_) => "ME",
            Field::rS(_) => "rS",
            Field::rD(_) => "rD",
            Field::rA(_) => "rA",
            Field::rB(_) => "rB",
            Field::rC(_) => "rC",
            Field::sr(_) => "sr",
            Field::spr(_) => "spr",
            Field::frS(_) => "frS",
            Field::frD(_) => "frD",
            Field::frA(_) => "frA",
            Field::frB(_) => "frB",
            Field::frC(_) => "frC",
            Field::crbD(_) => "crbD",
            Field::crbA(_) => "crbA",
            Field::crbB(_) => "crbB",
            Field::crfD(_) => "crfD",
            Field::crfS(_) => "crfS",
            Field::crm(_) => "crm",
            Field::ps_I(_) => "ps_I",
            Field::ps_IX(_) => "ps_IX",
            Field::ps_W(_) => "ps_W",
            Field::ps_WX(_) => "ps_WX",
            Field::NB(_) => "NB",
            Field::tbr(_) => "tbr",
            Field::mtfsf_FM(_) => "mtfsf_FM",
            Field::mtfsf_IMM(_) => "mtfsf_IMM",
            Field::spr_SPRG(_) => "spr_SPRG",
            Field::spr_BAT(_) => "spr_BAT",
            Field::TO(_) => "TO",
            Field::L(_) => "L",
            Field::xer => "xer",
            Field::ctr => "ctr",
            Field::lr => "lr",
        }
    }
}
#[allow(clippy::all, unused_mut)]
impl Ins {
    pub(crate) fn _fields(&self) -> Vec<Field> {
        match self.op {
            Opcode::Illegal => vec![],
            Opcode::Add => vec![
                Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Addc => vec![
                Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Adde => vec![
                Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Addi => vec![
                Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::simm(Simm(
                    ((((self.code & 0xffff) ^ 0x8000).wrapping_sub(0x8000)) as i32) as _,
                )),
            ],
            Opcode::Addic => vec![
                Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::simm(Simm(
                    ((((self.code & 0xffff) ^ 0x8000).wrapping_sub(0x8000)) as i32) as _,
                )),
            ],
            Opcode::Addic_ => vec![
                Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::simm(Simm(
                    ((((self.code & 0xffff) ^ 0x8000).wrapping_sub(0x8000)) as i32) as _,
                )),
            ],
            Opcode::Addis => vec![
                Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::uimm(Uimm((self.code & 0xffff) as _)),
            ],
            Opcode::Addme => vec![
                Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
            ],
            Opcode::Addze => vec![
                Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
            ],
            Opcode::And => vec![
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Andc => vec![
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Andi_ => vec![
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::uimm(Uimm((self.code & 0xffff) as _)),
            ],
            Opcode::Andis_ => vec![
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::uimm(Uimm((self.code & 0xffff) as _)),
            ],
            Opcode::B => vec![Field::LI(BranchDest(
                ((((((self.code >> 2u8) & 0xffffff) ^ 0x800000).wrapping_sub(0x800000)) as i32)
                    << 2u8) as _,
            ))],
            Opcode::Bc => vec![
                Field::BO(OpaqueU(((self.code >> 21u8) & 0x1f) as _)),
                Field::BI(CRBit(((self.code >> 16u8) & 0x1f) as _)),
                Field::BD(BranchDest(
                    ((((((self.code >> 2u8) & 0x3fff) ^ 0x2000).wrapping_sub(0x2000)) as i32)
                        << 2u8) as _,
                )),
            ],
            Opcode::Bcctr => vec![
                Field::BO(OpaqueU(((self.code >> 21u8) & 0x1f) as _)),
                Field::BI(CRBit(((self.code >> 16u8) & 0x1f) as _)),
                Field::BH(OpaqueU(((self.code >> 11u8) & 0x3) as _)),
            ],
            Opcode::Bclr => vec![
                Field::BO(OpaqueU(((self.code >> 21u8) & 0x1f) as _)),
                Field::BI(CRBit(((self.code >> 16u8) & 0x1f) as _)),
                Field::BH(OpaqueU(((self.code >> 11u8) & 0x3) as _)),
            ],
            Opcode::Cmp => vec![
                Field::crfD(CRField(((self.code >> 23u8) & 0x7) as _)),
                Field::L(OpaqueU(((self.code >> 21u8) & 0x1) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Cmpi => vec![
                Field::crfD(CRField(((self.code >> 23u8) & 0x7) as _)),
                Field::L(OpaqueU(((self.code >> 21u8) & 0x1) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::simm(Simm(
                    ((((self.code & 0xffff) ^ 0x8000).wrapping_sub(0x8000)) as i32) as _,
                )),
            ],
            Opcode::Cmpl => vec![
                Field::crfD(CRField(((self.code >> 23u8) & 0x7) as _)),
                Field::L(OpaqueU(((self.code >> 21u8) & 0x1) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Cmpli => vec![
                Field::crfD(CRField(((self.code >> 23u8) & 0x7) as _)),
                Field::L(OpaqueU(((self.code >> 21u8) & 0x1) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::uimm(Uimm((self.code & 0xffff) as _)),
            ],
            Opcode::Cntlzw => vec![
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _)),
            ],
            Opcode::Crand => vec![
                Field::crbD(CRBit(((self.code >> 21u8) & 0x1f) as _)),
                Field::crbA(CRBit(((self.code >> 16u8) & 0x1f) as _)),
                Field::crbB(CRBit(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Crandc => vec![
                Field::crbD(CRBit(((self.code >> 21u8) & 0x1f) as _)),
                Field::crbA(CRBit(((self.code >> 16u8) & 0x1f) as _)),
                Field::crbB(CRBit(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Creqv => vec![
                Field::crbD(CRBit(((self.code >> 21u8) & 0x1f) as _)),
                Field::crbA(CRBit(((self.code >> 16u8) & 0x1f) as _)),
                Field::crbB(CRBit(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Crnand => vec![
                Field::crbD(CRBit(((self.code >> 21u8) & 0x1f) as _)),
                Field::crbA(CRBit(((self.code >> 16u8) & 0x1f) as _)),
                Field::crbB(CRBit(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Crnor => vec![
                Field::crbD(CRBit(((self.code >> 21u8) & 0x1f) as _)),
                Field::crbA(CRBit(((self.code >> 16u8) & 0x1f) as _)),
                Field::crbB(CRBit(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Cror => vec![
                Field::crbD(CRBit(((self.code >> 21u8) & 0x1f) as _)),
                Field::crbA(CRBit(((self.code >> 16u8) & 0x1f) as _)),
                Field::crbB(CRBit(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Crorc => vec![
                Field::crbD(CRBit(((self.code >> 21u8) & 0x1f) as _)),
                Field::crbA(CRBit(((self.code >> 16u8) & 0x1f) as _)),
                Field::crbB(CRBit(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Crxor => vec![
                Field::crbD(CRBit(((self.code >> 21u8) & 0x1f) as _)),
                Field::crbA(CRBit(((self.code >> 16u8) & 0x1f) as _)),
                Field::crbB(CRBit(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Dcbf => vec![
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Dcbi => vec![
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Dcbst => vec![
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Dcbt => vec![
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Dcbtst => vec![
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Dcbz => vec![
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::DcbzL => vec![
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Divw => vec![
                Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Divwu => vec![
                Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Eciwx => vec![
                Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Ecowx => vec![
                Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Eieio => vec![],
            Opcode::Eqv => vec![
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Extsb => vec![
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _)),
            ],
            Opcode::Extsh => vec![
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _)),
            ],
            Opcode::Fabs => vec![
                Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Fadd => vec![
                Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Fadds => vec![
                Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Fcmpo => vec![
                Field::crfD(CRField(((self.code >> 23u8) & 0x7) as _)),
                Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Fcmpu => vec![
                Field::crfD(CRField(((self.code >> 23u8) & 0x7) as _)),
                Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Fctiw => vec![
                Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Fctiwz => vec![
                Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Fdiv => vec![
                Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Fdivs => vec![
                Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Fmadd => vec![
                Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::frC(FPR(((self.code >> 6u8) & 0x1f) as _)),
                Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Fmadds => vec![
                Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::frC(FPR(((self.code >> 6u8) & 0x1f) as _)),
                Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Fmr => vec![
                Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Fmsub => vec![
                Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::frC(FPR(((self.code >> 6u8) & 0x1f) as _)),
                Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Fmsubs => vec![
                Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::frC(FPR(((self.code >> 6u8) & 0x1f) as _)),
                Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Fmul => vec![
                Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::frC(FPR(((self.code >> 6u8) & 0x1f) as _)),
            ],
            Opcode::Fmuls => vec![
                Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::frC(FPR(((self.code >> 6u8) & 0x1f) as _)),
            ],
            Opcode::Fnabs => vec![
                Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Fneg => vec![
                Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Fnmadd => vec![
                Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::frC(FPR(((self.code >> 6u8) & 0x1f) as _)),
                Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Fnmadds => vec![
                Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::frC(FPR(((self.code >> 6u8) & 0x1f) as _)),
                Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Fnmsub => vec![
                Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::frC(FPR(((self.code >> 6u8) & 0x1f) as _)),
                Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Fnmsubs => vec![
                Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::frC(FPR(((self.code >> 6u8) & 0x1f) as _)),
                Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Fres => vec![
                Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Frsp => vec![
                Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Frsqrte => vec![
                Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Fsel => vec![
                Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::frC(FPR(((self.code >> 6u8) & 0x1f) as _)),
                Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Fsub => vec![
                Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Fsubs => vec![
                Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Icbi => vec![
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Isync => vec![],
            Opcode::Lbz => vec![
                Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::offset(Offset(
                    ((((self.code & 0xffff) ^ 0x8000).wrapping_sub(0x8000)) as i32) as _,
                )),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
            ],
            Opcode::Lbzu => vec![
                Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::offset(Offset(
                    ((((self.code & 0xffff) ^ 0x8000).wrapping_sub(0x8000)) as i32) as _,
                )),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
            ],
            Opcode::Lbzux => vec![
                Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Lbzx => vec![
                Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Lfd => vec![
                Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::offset(Offset(
                    ((((self.code & 0xffff) ^ 0x8000).wrapping_sub(0x8000)) as i32) as _,
                )),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
            ],
            Opcode::Lfdu => vec![
                Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::offset(Offset(
                    ((((self.code & 0xffff) ^ 0x8000).wrapping_sub(0x8000)) as i32) as _,
                )),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
            ],
            Opcode::Lfdux => vec![
                Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Lfdx => vec![
                Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Lfs => vec![
                Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::offset(Offset(
                    ((((self.code & 0xffff) ^ 0x8000).wrapping_sub(0x8000)) as i32) as _,
                )),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
            ],
            Opcode::Lfsu => vec![
                Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::offset(Offset(
                    ((((self.code & 0xffff) ^ 0x8000).wrapping_sub(0x8000)) as i32) as _,
                )),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
            ],
            Opcode::Lfsux => vec![
                Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Lfsx => vec![
                Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Lha => vec![
                Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::offset(Offset(
                    ((((self.code & 0xffff) ^ 0x8000).wrapping_sub(0x8000)) as i32) as _,
                )),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
            ],
            Opcode::Lhau => vec![
                Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::offset(Offset(
                    ((((self.code & 0xffff) ^ 0x8000).wrapping_sub(0x8000)) as i32) as _,
                )),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
            ],
            Opcode::Lhaux => vec![
                Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Lhax => vec![
                Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Lhbrx => vec![
                Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Lhz => vec![
                Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::offset(Offset(
                    ((((self.code & 0xffff) ^ 0x8000).wrapping_sub(0x8000)) as i32) as _,
                )),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
            ],
            Opcode::Lhzu => vec![
                Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::offset(Offset(
                    ((((self.code & 0xffff) ^ 0x8000).wrapping_sub(0x8000)) as i32) as _,
                )),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
            ],
            Opcode::Lhzux => vec![
                Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Lhzx => vec![
                Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Lmw => vec![
                Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::offset(Offset(
                    ((((self.code & 0xffff) ^ 0x8000).wrapping_sub(0x8000)) as i32) as _,
                )),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
            ],
            Opcode::Lswi => vec![
                Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::NB(OpaqueU(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Lswx => vec![
                Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Lwarx => vec![
                Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Lwbrx => vec![
                Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Lwz => vec![
                Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::offset(Offset(
                    ((((self.code & 0xffff) ^ 0x8000).wrapping_sub(0x8000)) as i32) as _,
                )),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
            ],
            Opcode::Lwzu => vec![
                Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::offset(Offset(
                    ((((self.code & 0xffff) ^ 0x8000).wrapping_sub(0x8000)) as i32) as _,
                )),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
            ],
            Opcode::Lwzux => vec![
                Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Lwzx => vec![
                Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Mcrf => vec![
                Field::crfD(CRField(((self.code >> 23u8) & 0x7) as _)),
                Field::crfS(CRField(((self.code >> 18u8) & 0x7) as _)),
            ],
            Opcode::Mcrfs => vec![
                Field::crfD(CRField(((self.code >> 23u8) & 0x7) as _)),
                Field::crfS(CRField(((self.code >> 18u8) & 0x7) as _)),
            ],
            Opcode::Mcrxr => vec![Field::crfD(CRField(((self.code >> 23u8) & 0x7) as _))],
            Opcode::Mfcr => vec![Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Mffs => vec![Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Mfmsr => vec![Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Mfspr => vec![
                Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::spr(SPR(
                    (((((self.code >> 11u8) & 0x3ff) & 0b11111_00000u32) >> 5u32)
                        | ((((self.code >> 11u8) & 0x3ff) & 0b00000_11111u32) << 5u32))
                        as u32 as _,
                )),
            ],
            Opcode::Mfsr => vec![
                Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::sr(SR(((self.code >> 16u8) & 0xf) as _)),
            ],
            Opcode::Mfsrin => vec![
                Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Mftb => vec![
                Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::tbr(OpaqueU(
                    (((((self.code >> 11u8) & 0x3ff) & 0b11111_00000u32) >> 5u32)
                        | ((((self.code >> 11u8) & 0x3ff) & 0b00000_11111u32) << 5u32))
                        as u32 as _,
                )),
            ],
            Opcode::Mtcrf => vec![
                Field::crm(OpaqueU(((self.code >> 12u8) & 0xff) as _)),
                Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _)),
            ],
            Opcode::Mtfsb0 => vec![Field::crbD(CRBit(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Mtfsb1 => vec![Field::crbD(CRBit(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Mtfsf => vec![
                Field::mtfsf_FM(OpaqueU(((self.code >> 17u8) & 0xff) as _)),
                Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Mtfsfi => vec![
                Field::crfD(CRField(((self.code >> 23u8) & 0x7) as _)),
                Field::mtfsf_IMM(OpaqueU(((self.code >> 12u8) & 0xf) as _)),
            ],
            Opcode::Mtmsr => vec![Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Mtspr => vec![
                Field::spr(SPR(
                    (((((self.code >> 11u8) & 0x3ff) & 0b11111_00000u32) >> 5u32)
                        | ((((self.code >> 11u8) & 0x3ff) & 0b00000_11111u32) << 5u32))
                        as u32 as _,
                )),
                Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _)),
            ],
            Opcode::Mtsr => vec![
                Field::sr(SR(((self.code >> 16u8) & 0xf) as _)),
                Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _)),
            ],
            Opcode::Mtsrin => vec![
                Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Mulhw => vec![
                Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Mulhwu => vec![
                Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Mulli => vec![
                Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::simm(Simm(
                    ((((self.code & 0xffff) ^ 0x8000).wrapping_sub(0x8000)) as i32) as _,
                )),
            ],
            Opcode::Mullw => vec![
                Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Nand => vec![
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Neg => vec![
                Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
            ],
            Opcode::Nor => vec![
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Or => vec![
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Orc => vec![
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Ori => vec![
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::uimm(Uimm((self.code & 0xffff) as _)),
            ],
            Opcode::Oris => vec![
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::uimm(Uimm((self.code & 0xffff) as _)),
            ],
            Opcode::PsqL => vec![
                Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::ps_offset(Offset(
                    ((((self.code & 0xfff) ^ 0x800).wrapping_sub(0x800)) as i32) as _,
                )),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::ps_W(OpaqueU(((self.code >> 15u8) & 0x1) as _)),
                Field::ps_I(GQR(((self.code >> 12u8) & 0x7) as _)),
            ],
            Opcode::PsqLu => vec![
                Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::ps_offset(Offset(
                    ((((self.code & 0xfff) ^ 0x800).wrapping_sub(0x800)) as i32) as _,
                )),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::ps_W(OpaqueU(((self.code >> 15u8) & 0x1) as _)),
                Field::ps_I(GQR(((self.code >> 12u8) & 0x7) as _)),
            ],
            Opcode::PsqLux => vec![
                Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
                Field::ps_WX(OpaqueU(((self.code >> 10u8) & 0x1) as _)),
                Field::ps_IX(GQR(((self.code >> 7u8) & 0x7) as _)),
            ],
            Opcode::PsqLx => vec![
                Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
                Field::ps_WX(OpaqueU(((self.code >> 10u8) & 0x1) as _)),
                Field::ps_IX(GQR(((self.code >> 7u8) & 0x7) as _)),
            ],
            Opcode::PsqSt => vec![
                Field::frS(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::ps_offset(Offset(
                    ((((self.code & 0xfff) ^ 0x800).wrapping_sub(0x800)) as i32) as _,
                )),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::ps_W(OpaqueU(((self.code >> 15u8) & 0x1) as _)),
                Field::ps_I(GQR(((self.code >> 12u8) & 0x7) as _)),
            ],
            Opcode::PsqStu => vec![
                Field::frS(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::ps_offset(Offset(
                    ((((self.code & 0xfff) ^ 0x800).wrapping_sub(0x800)) as i32) as _,
                )),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::ps_W(OpaqueU(((self.code >> 15u8) & 0x1) as _)),
                Field::ps_I(GQR(((self.code >> 12u8) & 0x7) as _)),
            ],
            Opcode::PsqStux => vec![
                Field::frS(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
                Field::ps_WX(OpaqueU(((self.code >> 10u8) & 0x1) as _)),
                Field::ps_IX(GQR(((self.code >> 7u8) & 0x7) as _)),
            ],
            Opcode::PsqStx => vec![
                Field::frS(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
                Field::ps_WX(OpaqueU(((self.code >> 10u8) & 0x1) as _)),
                Field::ps_IX(GQR(((self.code >> 7u8) & 0x7) as _)),
            ],
            Opcode::PsAbs => vec![
                Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::PsAdd => vec![
                Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::PsCmpo0 => vec![
                Field::crfD(CRField(((self.code >> 23u8) & 0x7) as _)),
                Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::PsCmpo1 => vec![
                Field::crfD(CRField(((self.code >> 23u8) & 0x7) as _)),
                Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::PsCmpu0 => vec![
                Field::crfD(CRField(((self.code >> 23u8) & 0x7) as _)),
                Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::PsCmpu1 => vec![
                Field::crfD(CRField(((self.code >> 23u8) & 0x7) as _)),
                Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::PsDiv => vec![
                Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::PsMadd => vec![
                Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::frC(FPR(((self.code >> 6u8) & 0x1f) as _)),
                Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::PsMadds0 => vec![
                Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::frC(FPR(((self.code >> 6u8) & 0x1f) as _)),
                Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::PsMadds1 => vec![
                Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::frC(FPR(((self.code >> 6u8) & 0x1f) as _)),
                Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::PsMerge00 => vec![
                Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::PsMerge01 => vec![
                Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::PsMerge10 => vec![
                Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::PsMerge11 => vec![
                Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::PsMr => vec![
                Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::PsMsub => vec![
                Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::frC(FPR(((self.code >> 6u8) & 0x1f) as _)),
                Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::PsMul => vec![
                Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::frC(FPR(((self.code >> 6u8) & 0x1f) as _)),
            ],
            Opcode::PsMuls0 => vec![
                Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::frC(FPR(((self.code >> 6u8) & 0x1f) as _)),
            ],
            Opcode::PsMuls1 => vec![
                Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::frC(FPR(((self.code >> 6u8) & 0x1f) as _)),
            ],
            Opcode::PsNabs => vec![
                Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::PsNeg => vec![
                Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::PsNmadd => vec![
                Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::frC(FPR(((self.code >> 6u8) & 0x1f) as _)),
                Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::PsNmsub => vec![
                Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::frC(FPR(((self.code >> 6u8) & 0x1f) as _)),
                Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::PsRes => vec![
                Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::PsRsqrte => vec![
                Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::PsSel => vec![
                Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::frC(FPR(((self.code >> 6u8) & 0x1f) as _)),
                Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::PsSub => vec![
                Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::PsSum0 => vec![
                Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::frC(FPR(((self.code >> 6u8) & 0x1f) as _)),
                Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::PsSum1 => vec![
                Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::frC(FPR(((self.code >> 6u8) & 0x1f) as _)),
                Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Rfi => vec![],
            Opcode::Rlwimi => vec![
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::SH(OpaqueU(((self.code >> 11u8) & 0x1f) as _)),
                Field::MB(OpaqueU(((self.code >> 6u8) & 0x1f) as _)),
                Field::ME(OpaqueU(((self.code >> 1u8) & 0x1f) as _)),
            ],
            Opcode::Rlwinm => vec![
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::SH(OpaqueU(((self.code >> 11u8) & 0x1f) as _)),
                Field::MB(OpaqueU(((self.code >> 6u8) & 0x1f) as _)),
                Field::ME(OpaqueU(((self.code >> 1u8) & 0x1f) as _)),
            ],
            Opcode::Rlwnm => vec![
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
                Field::MB(OpaqueU(((self.code >> 6u8) & 0x1f) as _)),
                Field::ME(OpaqueU(((self.code >> 1u8) & 0x1f) as _)),
            ],
            Opcode::Sc => vec![],
            Opcode::Slw => vec![
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Sraw => vec![
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Srawi => vec![
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::SH(OpaqueU(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Srw => vec![
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Stb => vec![
                Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::offset(Offset(
                    ((((self.code & 0xffff) ^ 0x8000).wrapping_sub(0x8000)) as i32) as _,
                )),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
            ],
            Opcode::Stbu => vec![
                Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::offset(Offset(
                    ((((self.code & 0xffff) ^ 0x8000).wrapping_sub(0x8000)) as i32) as _,
                )),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
            ],
            Opcode::Stbux => vec![
                Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Stbx => vec![
                Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Stfd => vec![
                Field::frS(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::offset(Offset(
                    ((((self.code & 0xffff) ^ 0x8000).wrapping_sub(0x8000)) as i32) as _,
                )),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
            ],
            Opcode::Stfdu => vec![
                Field::frS(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::offset(Offset(
                    ((((self.code & 0xffff) ^ 0x8000).wrapping_sub(0x8000)) as i32) as _,
                )),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
            ],
            Opcode::Stfdux => vec![
                Field::frS(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Stfdx => vec![
                Field::frS(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Stfiwx => vec![
                Field::frS(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Stfs => vec![
                Field::frS(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::offset(Offset(
                    ((((self.code & 0xffff) ^ 0x8000).wrapping_sub(0x8000)) as i32) as _,
                )),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
            ],
            Opcode::Stfsu => vec![
                Field::frS(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::offset(Offset(
                    ((((self.code & 0xffff) ^ 0x8000).wrapping_sub(0x8000)) as i32) as _,
                )),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
            ],
            Opcode::Stfsux => vec![
                Field::frS(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Stfsx => vec![
                Field::frS(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Sth => vec![
                Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::offset(Offset(
                    ((((self.code & 0xffff) ^ 0x8000).wrapping_sub(0x8000)) as i32) as _,
                )),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
            ],
            Opcode::Sthbrx => vec![
                Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Sthu => vec![
                Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::offset(Offset(
                    ((((self.code & 0xffff) ^ 0x8000).wrapping_sub(0x8000)) as i32) as _,
                )),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
            ],
            Opcode::Sthux => vec![
                Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Sthx => vec![
                Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Stmw => vec![
                Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::offset(Offset(
                    ((((self.code & 0xffff) ^ 0x8000).wrapping_sub(0x8000)) as i32) as _,
                )),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
            ],
            Opcode::Stswi => vec![
                Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::NB(OpaqueU(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Stswx => vec![
                Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Stw => vec![
                Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::offset(Offset(
                    ((((self.code & 0xffff) ^ 0x8000).wrapping_sub(0x8000)) as i32) as _,
                )),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
            ],
            Opcode::Stwbrx => vec![
                Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Stwcx_ => vec![
                Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Stwu => vec![
                Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::offset(Offset(
                    ((((self.code & 0xffff) ^ 0x8000).wrapping_sub(0x8000)) as i32) as _,
                )),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
            ],
            Opcode::Stwux => vec![
                Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Stwx => vec![
                Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Subf => vec![
                Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Subfc => vec![
                Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Subfe => vec![
                Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Subfic => vec![
                Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::simm(Simm(
                    ((((self.code & 0xffff) ^ 0x8000).wrapping_sub(0x8000)) as i32) as _,
                )),
            ],
            Opcode::Subfme => vec![
                Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
            ],
            Opcode::Subfze => vec![
                Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
            ],
            Opcode::Sync => vec![],
            Opcode::Tlbie => vec![Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _))],
            Opcode::Tlbsync => vec![],
            Opcode::Tw => vec![
                Field::TO(OpaqueU(((self.code >> 21u8) & 0x1f) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Twi => vec![
                Field::TO(OpaqueU(((self.code >> 21u8) & 0x1f) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::simm(Simm(
                    ((((self.code & 0xffff) ^ 0x8000).wrapping_sub(0x8000)) as i32) as _,
                )),
            ],
            Opcode::Xor => vec![
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
            ],
            Opcode::Xori => vec![
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::uimm(Uimm((self.code & 0xffff) as _)),
            ],
            Opcode::Xoris => vec![
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::uimm(Uimm((self.code & 0xffff) as _)),
            ],
        }
    }
    pub(crate) fn _defs(&self) -> Vec<Field> {
        match self.op {
            Opcode::Illegal => vec![],
            Opcode::Add => vec![Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Addc => vec![Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Adde => vec![Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Addi => vec![Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Addic => vec![Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Addic_ => vec![Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Addis => vec![Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Addme => vec![Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Addze => vec![Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::And => vec![Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _))],
            Opcode::Andc => vec![Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _))],
            Opcode::Andi_ => vec![Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _))],
            Opcode::Andis_ => vec![Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _))],
            Opcode::B => vec![],
            Opcode::Bc => vec![],
            Opcode::Bcctr => vec![],
            Opcode::Bclr => vec![],
            Opcode::Cmp => vec![Field::crfD(CRField(((self.code >> 23u8) & 0x7) as _))],
            Opcode::Cmpi => vec![Field::crfD(CRField(((self.code >> 23u8) & 0x7) as _))],
            Opcode::Cmpl => vec![Field::crfD(CRField(((self.code >> 23u8) & 0x7) as _))],
            Opcode::Cmpli => vec![Field::crfD(CRField(((self.code >> 23u8) & 0x7) as _))],
            Opcode::Cntlzw => vec![Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _))],
            Opcode::Crand => vec![Field::crbD(CRBit(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Crandc => vec![Field::crbD(CRBit(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Creqv => vec![Field::crbD(CRBit(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Crnand => vec![Field::crbD(CRBit(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Crnor => vec![Field::crbD(CRBit(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Cror => vec![Field::crbD(CRBit(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Crorc => vec![Field::crbD(CRBit(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Crxor => vec![Field::crbD(CRBit(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Dcbf => vec![],
            Opcode::Dcbi => vec![],
            Opcode::Dcbst => vec![],
            Opcode::Dcbt => vec![],
            Opcode::Dcbtst => vec![],
            Opcode::Dcbz => vec![],
            Opcode::DcbzL => vec![],
            Opcode::Divw => vec![Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Divwu => vec![Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Eciwx => vec![Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Ecowx => vec![],
            Opcode::Eieio => vec![],
            Opcode::Eqv => vec![Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _))],
            Opcode::Extsb => vec![Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _))],
            Opcode::Extsh => vec![Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _))],
            Opcode::Fabs => vec![Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Fadd => vec![Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Fadds => vec![Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Fcmpo => vec![Field::crfD(CRField(((self.code >> 23u8) & 0x7) as _))],
            Opcode::Fcmpu => vec![Field::crfD(CRField(((self.code >> 23u8) & 0x7) as _))],
            Opcode::Fctiw => vec![Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Fctiwz => vec![Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Fdiv => vec![Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Fdivs => vec![Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Fmadd => vec![Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Fmadds => vec![Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Fmr => vec![Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Fmsub => vec![Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Fmsubs => vec![Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Fmul => vec![Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Fmuls => vec![Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Fnabs => vec![Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Fneg => vec![Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Fnmadd => vec![Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Fnmadds => vec![Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Fnmsub => vec![Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Fnmsubs => vec![Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Fres => vec![Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Frsp => vec![Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Frsqrte => vec![Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Fsel => vec![Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Fsub => vec![Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Fsubs => vec![Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Icbi => vec![],
            Opcode::Isync => vec![],
            Opcode::Lbz => vec![Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Lbzu => vec![
                Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
            ],
            Opcode::Lbzux => vec![
                Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
            ],
            Opcode::Lbzx => vec![Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Lfd => vec![Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Lfdu => vec![
                Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
            ],
            Opcode::Lfdux => vec![
                Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
            ],
            Opcode::Lfdx => vec![Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Lfs => vec![Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Lfsu => vec![
                Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
            ],
            Opcode::Lfsux => vec![
                Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
            ],
            Opcode::Lfsx => vec![Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Lha => vec![Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Lhau => vec![
                Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
            ],
            Opcode::Lhaux => vec![
                Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
            ],
            Opcode::Lhax => vec![Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Lhbrx => vec![Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Lhz => vec![Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Lhzu => vec![
                Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
            ],
            Opcode::Lhzux => vec![
                Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
            ],
            Opcode::Lhzx => vec![Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Lmw => vec![Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Lswi => vec![Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Lswx => vec![Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Lwarx => vec![Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Lwbrx => vec![Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Lwz => vec![Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Lwzu => vec![
                Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
            ],
            Opcode::Lwzux => vec![
                Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
            ],
            Opcode::Lwzx => vec![Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Mcrf => vec![Field::crfD(CRField(((self.code >> 23u8) & 0x7) as _))],
            Opcode::Mcrfs => vec![Field::crfD(CRField(((self.code >> 23u8) & 0x7) as _))],
            Opcode::Mcrxr => vec![
                Field::crfD(CRField(((self.code >> 23u8) & 0x7) as _)),
                Field::xer,
            ],
            Opcode::Mfcr => vec![Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Mffs => vec![Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Mfmsr => vec![Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Mfspr => vec![Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Mfsr => vec![Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Mfsrin => vec![Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Mftb => vec![Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Mtcrf => vec![],
            Opcode::Mtfsb0 => vec![Field::crbD(CRBit(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Mtfsb1 => vec![Field::crbD(CRBit(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Mtfsf => vec![],
            Opcode::Mtfsfi => vec![Field::crfD(CRField(((self.code >> 23u8) & 0x7) as _))],
            Opcode::Mtmsr => vec![],
            Opcode::Mtspr => vec![],
            Opcode::Mtsr => vec![],
            Opcode::Mtsrin => vec![],
            Opcode::Mulhw => vec![Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Mulhwu => vec![Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Mulli => vec![Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Mullw => vec![Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Nand => vec![Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _))],
            Opcode::Neg => vec![Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Nor => vec![Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _))],
            Opcode::Or => vec![Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _))],
            Opcode::Orc => vec![Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _))],
            Opcode::Ori => vec![Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _))],
            Opcode::Oris => vec![Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _))],
            Opcode::PsqL => vec![Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::PsqLu => vec![
                Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
            ],
            Opcode::PsqLux => vec![
                Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _)),
                Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
            ],
            Opcode::PsqLx => vec![Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::PsqSt => vec![],
            Opcode::PsqStu => vec![Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _))],
            Opcode::PsqStux => vec![Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _))],
            Opcode::PsqStx => vec![],
            Opcode::PsAbs => vec![Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::PsAdd => vec![Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::PsCmpo0 => vec![Field::crfD(CRField(((self.code >> 23u8) & 0x7) as _))],
            Opcode::PsCmpo1 => vec![Field::crfD(CRField(((self.code >> 23u8) & 0x7) as _))],
            Opcode::PsCmpu0 => vec![Field::crfD(CRField(((self.code >> 23u8) & 0x7) as _))],
            Opcode::PsCmpu1 => vec![Field::crfD(CRField(((self.code >> 23u8) & 0x7) as _))],
            Opcode::PsDiv => vec![Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::PsMadd => vec![Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::PsMadds0 => vec![Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::PsMadds1 => vec![Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::PsMerge00 => vec![Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::PsMerge01 => vec![Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::PsMerge10 => vec![Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::PsMerge11 => vec![Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::PsMr => vec![Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::PsMsub => vec![Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::PsMul => vec![Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::PsMuls0 => vec![Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::PsMuls1 => vec![Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::PsNabs => vec![Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::PsNeg => vec![Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::PsNmadd => vec![Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::PsNmsub => vec![Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::PsRes => vec![Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::PsRsqrte => vec![Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::PsSel => vec![Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::PsSub => vec![Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::PsSum0 => vec![Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::PsSum1 => vec![Field::frD(FPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Rfi => vec![],
            Opcode::Rlwimi => vec![Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _))],
            Opcode::Rlwinm => vec![Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _))],
            Opcode::Rlwnm => vec![Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _))],
            Opcode::Sc => vec![],
            Opcode::Slw => vec![Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _))],
            Opcode::Sraw => vec![Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _))],
            Opcode::Srawi => vec![Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _))],
            Opcode::Srw => vec![Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _))],
            Opcode::Stb => vec![],
            Opcode::Stbu => vec![Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _))],
            Opcode::Stbux => vec![Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _))],
            Opcode::Stbx => vec![],
            Opcode::Stfd => vec![],
            Opcode::Stfdu => vec![Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _))],
            Opcode::Stfdux => vec![Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _))],
            Opcode::Stfdx => vec![],
            Opcode::Stfiwx => vec![],
            Opcode::Stfs => vec![],
            Opcode::Stfsu => vec![Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _))],
            Opcode::Stfsux => vec![Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _))],
            Opcode::Stfsx => vec![],
            Opcode::Sth => vec![],
            Opcode::Sthbrx => vec![],
            Opcode::Sthu => vec![Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _))],
            Opcode::Sthux => vec![Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _))],
            Opcode::Sthx => vec![],
            Opcode::Stmw => vec![],
            Opcode::Stswi => vec![],
            Opcode::Stswx => vec![],
            Opcode::Stw => vec![],
            Opcode::Stwbrx => vec![],
            Opcode::Stwcx_ => vec![],
            Opcode::Stwu => vec![Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _))],
            Opcode::Stwux => vec![Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _))],
            Opcode::Stwx => vec![],
            Opcode::Subf => vec![Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Subfc => vec![Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Subfe => vec![Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Subfic => vec![Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Subfme => vec![Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Subfze => vec![Field::rD(GPR(((self.code >> 21u8) & 0x1f) as _))],
            Opcode::Sync => vec![],
            Opcode::Tlbie => vec![],
            Opcode::Tlbsync => vec![],
            Opcode::Tw => vec![],
            Opcode::Twi => vec![],
            Opcode::Xor => vec![Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _))],
            Opcode::Xori => vec![Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _))],
            Opcode::Xoris => vec![Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _))],
        }
    }
    pub(crate) fn _uses(&self) -> Vec<Field> {
        match self.op {
            Opcode::Illegal => vec![],
            Opcode::Add => {
                let mut uses = vec![
                    Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                    Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::Addc => {
                let mut uses = vec![
                    Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                    Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::Adde => {
                let mut uses = vec![
                    Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                    Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::Addi => {
                let mut uses = vec![];
                if ((self.code >> 16u8) & 0x1f) != 0 {
                    uses.push(Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)));
                }
                uses
            }
            Opcode::Addic => {
                let mut uses = vec![Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _))];
                uses
            }
            Opcode::Addic_ => {
                let mut uses = vec![Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _))];
                uses
            }
            Opcode::Addis => {
                let mut uses = vec![];
                if ((self.code >> 16u8) & 0x1f) != 0 {
                    uses.push(Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)));
                }
                uses
            }
            Opcode::Addme => {
                let mut uses = vec![Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _))];
                uses
            }
            Opcode::Addze => {
                let mut uses = vec![Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _))];
                uses
            }
            Opcode::And => {
                let mut uses = vec![
                    Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _)),
                    Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::Andc => {
                let mut uses = vec![
                    Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _)),
                    Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::Andi_ => {
                let mut uses = vec![Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _))];
                uses
            }
            Opcode::Andis_ => {
                let mut uses = vec![Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _))];
                uses
            }
            Opcode::B => {
                let mut uses = vec![];
                uses
            }
            Opcode::Bc => {
                let mut uses = vec![];
                uses
            }
            Opcode::Bcctr => {
                let mut uses = vec![Field::ctr];
                uses
            }
            Opcode::Bclr => {
                let mut uses = vec![Field::lr];
                uses
            }
            Opcode::Cmp => {
                let mut uses = vec![
                    Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                    Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::Cmpi => {
                let mut uses = vec![Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _))];
                uses
            }
            Opcode::Cmpl => {
                let mut uses = vec![
                    Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                    Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::Cmpli => {
                let mut uses = vec![Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _))];
                uses
            }
            Opcode::Cntlzw => {
                let mut uses = vec![Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _))];
                uses
            }
            Opcode::Crand => {
                let mut uses = vec![
                    Field::crbA(CRBit(((self.code >> 16u8) & 0x1f) as _)),
                    Field::crbB(CRBit(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::Crandc => {
                let mut uses = vec![
                    Field::crbA(CRBit(((self.code >> 16u8) & 0x1f) as _)),
                    Field::crbB(CRBit(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::Creqv => {
                let mut uses = vec![
                    Field::crbA(CRBit(((self.code >> 16u8) & 0x1f) as _)),
                    Field::crbB(CRBit(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::Crnand => {
                let mut uses = vec![
                    Field::crbA(CRBit(((self.code >> 16u8) & 0x1f) as _)),
                    Field::crbB(CRBit(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::Crnor => {
                let mut uses = vec![
                    Field::crbA(CRBit(((self.code >> 16u8) & 0x1f) as _)),
                    Field::crbB(CRBit(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::Cror => {
                let mut uses = vec![
                    Field::crbA(CRBit(((self.code >> 16u8) & 0x1f) as _)),
                    Field::crbB(CRBit(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::Crorc => {
                let mut uses = vec![
                    Field::crbA(CRBit(((self.code >> 16u8) & 0x1f) as _)),
                    Field::crbB(CRBit(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::Crxor => {
                let mut uses = vec![
                    Field::crbA(CRBit(((self.code >> 16u8) & 0x1f) as _)),
                    Field::crbB(CRBit(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::Dcbf => {
                let mut uses = vec![Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _))];
                if ((self.code >> 16u8) & 0x1f) != 0 {
                    uses.push(Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)));
                }
                uses
            }
            Opcode::Dcbi => {
                let mut uses = vec![Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _))];
                if ((self.code >> 16u8) & 0x1f) != 0 {
                    uses.push(Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)));
                }
                uses
            }
            Opcode::Dcbst => {
                let mut uses = vec![Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _))];
                if ((self.code >> 16u8) & 0x1f) != 0 {
                    uses.push(Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)));
                }
                uses
            }
            Opcode::Dcbt => {
                let mut uses = vec![Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _))];
                if ((self.code >> 16u8) & 0x1f) != 0 {
                    uses.push(Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)));
                }
                uses
            }
            Opcode::Dcbtst => {
                let mut uses = vec![Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _))];
                if ((self.code >> 16u8) & 0x1f) != 0 {
                    uses.push(Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)));
                }
                uses
            }
            Opcode::Dcbz => {
                let mut uses = vec![Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _))];
                if ((self.code >> 16u8) & 0x1f) != 0 {
                    uses.push(Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)));
                }
                uses
            }
            Opcode::DcbzL => {
                let mut uses = vec![Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _))];
                if ((self.code >> 16u8) & 0x1f) != 0 {
                    uses.push(Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)));
                }
                uses
            }
            Opcode::Divw => {
                let mut uses = vec![
                    Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                    Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::Divwu => {
                let mut uses = vec![
                    Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                    Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::Eciwx => {
                let mut uses = vec![Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _))];
                if ((self.code >> 16u8) & 0x1f) != 0 {
                    uses.push(Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)));
                }
                uses
            }
            Opcode::Ecowx => {
                let mut uses = vec![
                    Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _)),
                    Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                if ((self.code >> 16u8) & 0x1f) != 0 {
                    uses.push(Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)));
                }
                uses
            }
            Opcode::Eieio => {
                let mut uses = vec![];
                uses
            }
            Opcode::Eqv => {
                let mut uses = vec![
                    Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _)),
                    Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::Extsb => {
                let mut uses = vec![Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _))];
                uses
            }
            Opcode::Extsh => {
                let mut uses = vec![Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _))];
                uses
            }
            Opcode::Fabs => {
                let mut uses = vec![Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _))];
                uses
            }
            Opcode::Fadd => {
                let mut uses = vec![
                    Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                    Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::Fadds => {
                let mut uses = vec![
                    Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                    Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::Fcmpo => {
                let mut uses = vec![
                    Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                    Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::Fcmpu => {
                let mut uses = vec![
                    Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                    Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::Fctiw => {
                let mut uses = vec![Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _))];
                uses
            }
            Opcode::Fctiwz => {
                let mut uses = vec![Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _))];
                uses
            }
            Opcode::Fdiv => {
                let mut uses = vec![
                    Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                    Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::Fdivs => {
                let mut uses = vec![
                    Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                    Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::Fmadd => {
                let mut uses = vec![
                    Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                    Field::frC(FPR(((self.code >> 6u8) & 0x1f) as _)),
                    Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::Fmadds => {
                let mut uses = vec![
                    Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                    Field::frC(FPR(((self.code >> 6u8) & 0x1f) as _)),
                    Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::Fmr => {
                let mut uses = vec![Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _))];
                uses
            }
            Opcode::Fmsub => {
                let mut uses = vec![
                    Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                    Field::frC(FPR(((self.code >> 6u8) & 0x1f) as _)),
                    Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::Fmsubs => {
                let mut uses = vec![
                    Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                    Field::frC(FPR(((self.code >> 6u8) & 0x1f) as _)),
                    Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::Fmul => {
                let mut uses = vec![
                    Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                    Field::frC(FPR(((self.code >> 6u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::Fmuls => {
                let mut uses = vec![
                    Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                    Field::frC(FPR(((self.code >> 6u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::Fnabs => {
                let mut uses = vec![Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _))];
                uses
            }
            Opcode::Fneg => {
                let mut uses = vec![Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _))];
                uses
            }
            Opcode::Fnmadd => {
                let mut uses = vec![
                    Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                    Field::frC(FPR(((self.code >> 6u8) & 0x1f) as _)),
                    Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::Fnmadds => {
                let mut uses = vec![
                    Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                    Field::frC(FPR(((self.code >> 6u8) & 0x1f) as _)),
                    Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::Fnmsub => {
                let mut uses = vec![
                    Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                    Field::frC(FPR(((self.code >> 6u8) & 0x1f) as _)),
                    Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::Fnmsubs => {
                let mut uses = vec![
                    Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                    Field::frC(FPR(((self.code >> 6u8) & 0x1f) as _)),
                    Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::Fres => {
                let mut uses = vec![Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _))];
                uses
            }
            Opcode::Frsp => {
                let mut uses = vec![Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _))];
                uses
            }
            Opcode::Frsqrte => {
                let mut uses = vec![Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _))];
                uses
            }
            Opcode::Fsel => {
                let mut uses = vec![
                    Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                    Field::frC(FPR(((self.code >> 6u8) & 0x1f) as _)),
                    Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::Fsub => {
                let mut uses = vec![
                    Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                    Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::Fsubs => {
                let mut uses = vec![
                    Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                    Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::Icbi => {
                let mut uses = vec![Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _))];
                if ((self.code >> 16u8) & 0x1f) != 0 {
                    uses.push(Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)));
                }
                uses
            }
            Opcode::Isync => {
                let mut uses = vec![];
                uses
            }
            Opcode::Lbz => {
                let mut uses = vec![Field::offset(Offset(
                    ((((self.code & 0xffff) ^ 0x8000).wrapping_sub(0x8000)) as i32) as _,
                ))];
                if ((self.code >> 16u8) & 0x1f) != 0 {
                    uses.push(Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)));
                }
                uses
            }
            Opcode::Lbzu => {
                let mut uses = vec![
                    Field::offset(Offset(
                        ((((self.code & 0xffff) ^ 0x8000).wrapping_sub(0x8000)) as i32) as _,
                    )),
                    Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::Lbzux => {
                let mut uses = vec![
                    Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                    Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::Lbzx => {
                let mut uses = vec![Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _))];
                if ((self.code >> 16u8) & 0x1f) != 0 {
                    uses.push(Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)));
                }
                uses
            }
            Opcode::Lfd => {
                let mut uses = vec![Field::offset(Offset(
                    ((((self.code & 0xffff) ^ 0x8000).wrapping_sub(0x8000)) as i32) as _,
                ))];
                if ((self.code >> 16u8) & 0x1f) != 0 {
                    uses.push(Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)));
                }
                uses
            }
            Opcode::Lfdu => {
                let mut uses = vec![
                    Field::offset(Offset(
                        ((((self.code & 0xffff) ^ 0x8000).wrapping_sub(0x8000)) as i32) as _,
                    )),
                    Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::Lfdux => {
                let mut uses = vec![
                    Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                    Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::Lfdx => {
                let mut uses = vec![Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _))];
                if ((self.code >> 16u8) & 0x1f) != 0 {
                    uses.push(Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)));
                }
                uses
            }
            Opcode::Lfs => {
                let mut uses = vec![Field::offset(Offset(
                    ((((self.code & 0xffff) ^ 0x8000).wrapping_sub(0x8000)) as i32) as _,
                ))];
                if ((self.code >> 16u8) & 0x1f) != 0 {
                    uses.push(Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)));
                }
                uses
            }
            Opcode::Lfsu => {
                let mut uses = vec![
                    Field::offset(Offset(
                        ((((self.code & 0xffff) ^ 0x8000).wrapping_sub(0x8000)) as i32) as _,
                    )),
                    Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::Lfsux => {
                let mut uses = vec![
                    Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                    Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::Lfsx => {
                let mut uses = vec![Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _))];
                if ((self.code >> 16u8) & 0x1f) != 0 {
                    uses.push(Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)));
                }
                uses
            }
            Opcode::Lha => {
                let mut uses = vec![Field::offset(Offset(
                    ((((self.code & 0xffff) ^ 0x8000).wrapping_sub(0x8000)) as i32) as _,
                ))];
                if ((self.code >> 16u8) & 0x1f) != 0 {
                    uses.push(Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)));
                }
                uses
            }
            Opcode::Lhau => {
                let mut uses = vec![
                    Field::offset(Offset(
                        ((((self.code & 0xffff) ^ 0x8000).wrapping_sub(0x8000)) as i32) as _,
                    )),
                    Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::Lhaux => {
                let mut uses = vec![
                    Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                    Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::Lhax => {
                let mut uses = vec![Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _))];
                if ((self.code >> 16u8) & 0x1f) != 0 {
                    uses.push(Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)));
                }
                uses
            }
            Opcode::Lhbrx => {
                let mut uses = vec![Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _))];
                if ((self.code >> 16u8) & 0x1f) != 0 {
                    uses.push(Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)));
                }
                uses
            }
            Opcode::Lhz => {
                let mut uses = vec![Field::offset(Offset(
                    ((((self.code & 0xffff) ^ 0x8000).wrapping_sub(0x8000)) as i32) as _,
                ))];
                if ((self.code >> 16u8) & 0x1f) != 0 {
                    uses.push(Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)));
                }
                uses
            }
            Opcode::Lhzu => {
                let mut uses = vec![
                    Field::offset(Offset(
                        ((((self.code & 0xffff) ^ 0x8000).wrapping_sub(0x8000)) as i32) as _,
                    )),
                    Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::Lhzux => {
                let mut uses = vec![
                    Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                    Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::Lhzx => {
                let mut uses = vec![Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _))];
                if ((self.code >> 16u8) & 0x1f) != 0 {
                    uses.push(Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)));
                }
                uses
            }
            Opcode::Lmw => {
                let mut uses = vec![Field::offset(Offset(
                    ((((self.code & 0xffff) ^ 0x8000).wrapping_sub(0x8000)) as i32) as _,
                ))];
                if ((self.code >> 16u8) & 0x1f) != 0 {
                    uses.push(Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)));
                }
                uses
            }
            Opcode::Lswi => {
                let mut uses = vec![];
                if ((self.code >> 16u8) & 0x1f) != 0 {
                    uses.push(Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)));
                }
                uses
            }
            Opcode::Lswx => {
                let mut uses = vec![Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _))];
                if ((self.code >> 16u8) & 0x1f) != 0 {
                    uses.push(Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)));
                }
                uses
            }
            Opcode::Lwarx => {
                let mut uses = vec![Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _))];
                if ((self.code >> 16u8) & 0x1f) != 0 {
                    uses.push(Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)));
                }
                uses
            }
            Opcode::Lwbrx => {
                let mut uses = vec![Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _))];
                if ((self.code >> 16u8) & 0x1f) != 0 {
                    uses.push(Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)));
                }
                uses
            }
            Opcode::Lwz => {
                let mut uses = vec![Field::offset(Offset(
                    ((((self.code & 0xffff) ^ 0x8000).wrapping_sub(0x8000)) as i32) as _,
                ))];
                if ((self.code >> 16u8) & 0x1f) != 0 {
                    uses.push(Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)));
                }
                uses
            }
            Opcode::Lwzu => {
                let mut uses = vec![
                    Field::offset(Offset(
                        ((((self.code & 0xffff) ^ 0x8000).wrapping_sub(0x8000)) as i32) as _,
                    )),
                    Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::Lwzux => {
                let mut uses = vec![
                    Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                    Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::Lwzx => {
                let mut uses = vec![Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _))];
                if ((self.code >> 16u8) & 0x1f) != 0 {
                    uses.push(Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)));
                }
                uses
            }
            Opcode::Mcrf => {
                let mut uses = vec![Field::crfS(CRField(((self.code >> 18u8) & 0x7) as _))];
                uses
            }
            Opcode::Mcrfs => {
                let mut uses = vec![Field::crfS(CRField(((self.code >> 18u8) & 0x7) as _))];
                uses
            }
            Opcode::Mcrxr => {
                let mut uses = vec![];
                uses
            }
            Opcode::Mfcr => {
                let mut uses = vec![];
                uses
            }
            Opcode::Mffs => {
                let mut uses = vec![];
                uses
            }
            Opcode::Mfmsr => {
                let mut uses = vec![];
                uses
            }
            Opcode::Mfspr => {
                let mut uses = vec![];
                uses
            }
            Opcode::Mfsr => {
                let mut uses = vec![];
                uses
            }
            Opcode::Mfsrin => {
                let mut uses = vec![Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _))];
                uses
            }
            Opcode::Mftb => {
                let mut uses = vec![];
                uses
            }
            Opcode::Mtcrf => {
                let mut uses = vec![Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _))];
                uses
            }
            Opcode::Mtfsb0 => {
                let mut uses = vec![];
                uses
            }
            Opcode::Mtfsb1 => {
                let mut uses = vec![];
                uses
            }
            Opcode::Mtfsf => {
                let mut uses = vec![Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _))];
                uses
            }
            Opcode::Mtfsfi => {
                let mut uses = vec![];
                uses
            }
            Opcode::Mtmsr => {
                let mut uses = vec![Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _))];
                uses
            }
            Opcode::Mtspr => {
                let mut uses = vec![Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _))];
                uses
            }
            Opcode::Mtsr => {
                let mut uses = vec![Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _))];
                uses
            }
            Opcode::Mtsrin => {
                let mut uses = vec![
                    Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _)),
                    Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::Mulhw => {
                let mut uses = vec![
                    Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                    Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::Mulhwu => {
                let mut uses = vec![
                    Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                    Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::Mulli => {
                let mut uses = vec![Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _))];
                uses
            }
            Opcode::Mullw => {
                let mut uses = vec![
                    Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                    Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::Nand => {
                let mut uses = vec![
                    Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _)),
                    Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::Neg => {
                let mut uses = vec![Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _))];
                uses
            }
            Opcode::Nor => {
                let mut uses = vec![
                    Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _)),
                    Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::Or => {
                let mut uses = vec![
                    Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _)),
                    Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::Orc => {
                let mut uses = vec![
                    Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _)),
                    Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::Ori => {
                let mut uses = vec![Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _))];
                uses
            }
            Opcode::Oris => {
                let mut uses = vec![Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _))];
                uses
            }
            Opcode::PsqL => {
                let mut uses = vec![];
                if ((self.code >> 16u8) & 0x1f) != 0 {
                    uses.push(Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)));
                }
                uses
            }
            Opcode::PsqLu => {
                let mut uses = vec![Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _))];
                uses
            }
            Opcode::PsqLux => {
                let mut uses = vec![
                    Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                    Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::PsqLx => {
                let mut uses = vec![Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _))];
                if ((self.code >> 16u8) & 0x1f) != 0 {
                    uses.push(Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)));
                }
                uses
            }
            Opcode::PsqSt => {
                let mut uses = vec![Field::frS(FPR(((self.code >> 21u8) & 0x1f) as _))];
                if ((self.code >> 16u8) & 0x1f) != 0 {
                    uses.push(Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)));
                }
                uses
            }
            Opcode::PsqStu => {
                let mut uses = vec![
                    Field::frS(FPR(((self.code >> 21u8) & 0x1f) as _)),
                    Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::PsqStux => {
                let mut uses = vec![
                    Field::frS(FPR(((self.code >> 21u8) & 0x1f) as _)),
                    Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                    Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::PsqStx => {
                let mut uses = vec![
                    Field::frS(FPR(((self.code >> 21u8) & 0x1f) as _)),
                    Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                if ((self.code >> 16u8) & 0x1f) != 0 {
                    uses.push(Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)));
                }
                uses
            }
            Opcode::PsAbs => {
                let mut uses = vec![Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _))];
                uses
            }
            Opcode::PsAdd => {
                let mut uses = vec![
                    Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                    Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::PsCmpo0 => {
                let mut uses = vec![Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _))];
                if ((self.code >> 16u8) & 0x1f) != 0 {
                    uses.push(Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)));
                }
                uses
            }
            Opcode::PsCmpo1 => {
                let mut uses = vec![Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _))];
                if ((self.code >> 16u8) & 0x1f) != 0 {
                    uses.push(Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)));
                }
                uses
            }
            Opcode::PsCmpu0 => {
                let mut uses = vec![Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _))];
                if ((self.code >> 16u8) & 0x1f) != 0 {
                    uses.push(Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)));
                }
                uses
            }
            Opcode::PsCmpu1 => {
                let mut uses = vec![Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _))];
                if ((self.code >> 16u8) & 0x1f) != 0 {
                    uses.push(Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)));
                }
                uses
            }
            Opcode::PsDiv => {
                let mut uses = vec![
                    Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                    Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::PsMadd => {
                let mut uses = vec![
                    Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                    Field::frC(FPR(((self.code >> 6u8) & 0x1f) as _)),
                    Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::PsMadds0 => {
                let mut uses = vec![
                    Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                    Field::frC(FPR(((self.code >> 6u8) & 0x1f) as _)),
                    Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::PsMadds1 => {
                let mut uses = vec![
                    Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                    Field::frC(FPR(((self.code >> 6u8) & 0x1f) as _)),
                    Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::PsMerge00 => {
                let mut uses = vec![
                    Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                    Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::PsMerge01 => {
                let mut uses = vec![
                    Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                    Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::PsMerge10 => {
                let mut uses = vec![
                    Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                    Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::PsMerge11 => {
                let mut uses = vec![
                    Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                    Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::PsMr => {
                let mut uses = vec![Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _))];
                uses
            }
            Opcode::PsMsub => {
                let mut uses = vec![
                    Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                    Field::frC(FPR(((self.code >> 6u8) & 0x1f) as _)),
                    Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::PsMul => {
                let mut uses = vec![
                    Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                    Field::frC(FPR(((self.code >> 6u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::PsMuls0 => {
                let mut uses = vec![
                    Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                    Field::frC(FPR(((self.code >> 6u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::PsMuls1 => {
                let mut uses = vec![
                    Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                    Field::frC(FPR(((self.code >> 6u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::PsNabs => {
                let mut uses = vec![Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _))];
                uses
            }
            Opcode::PsNeg => {
                let mut uses = vec![Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _))];
                uses
            }
            Opcode::PsNmadd => {
                let mut uses = vec![
                    Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                    Field::frC(FPR(((self.code >> 6u8) & 0x1f) as _)),
                    Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::PsNmsub => {
                let mut uses = vec![
                    Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                    Field::frC(FPR(((self.code >> 6u8) & 0x1f) as _)),
                    Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::PsRes => {
                let mut uses = vec![Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _))];
                uses
            }
            Opcode::PsRsqrte => {
                let mut uses = vec![Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _))];
                uses
            }
            Opcode::PsSel => {
                let mut uses = vec![
                    Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                    Field::frC(FPR(((self.code >> 6u8) & 0x1f) as _)),
                    Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::PsSub => {
                let mut uses = vec![
                    Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                    Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::PsSum0 => {
                let mut uses = vec![
                    Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                    Field::frC(FPR(((self.code >> 6u8) & 0x1f) as _)),
                    Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::PsSum1 => {
                let mut uses = vec![
                    Field::frA(FPR(((self.code >> 16u8) & 0x1f) as _)),
                    Field::frC(FPR(((self.code >> 6u8) & 0x1f) as _)),
                    Field::frB(FPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::Rfi => {
                let mut uses = vec![];
                uses
            }
            Opcode::Rlwimi => {
                let mut uses = vec![
                    Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                    Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _)),
                    Field::SH(OpaqueU(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::Rlwinm => {
                let mut uses = vec![
                    Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _)),
                    Field::SH(OpaqueU(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::Rlwnm => {
                let mut uses = vec![
                    Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _)),
                    Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::Sc => {
                let mut uses = vec![];
                uses
            }
            Opcode::Slw => {
                let mut uses = vec![
                    Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _)),
                    Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::Sraw => {
                let mut uses = vec![
                    Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _)),
                    Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::Srawi => {
                let mut uses = vec![Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _))];
                uses
            }
            Opcode::Srw => {
                let mut uses = vec![
                    Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                    Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::Stb => {
                let mut uses = vec![Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _))];
                if ((self.code >> 16u8) & 0x1f) != 0 {
                    uses.push(Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)));
                }
                uses
            }
            Opcode::Stbu => {
                let mut uses = vec![
                    Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _)),
                    Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::Stbux => {
                let mut uses = vec![
                    Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _)),
                    Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                    Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::Stbx => {
                let mut uses = vec![
                    Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _)),
                    Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                if ((self.code >> 16u8) & 0x1f) != 0 {
                    uses.push(Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)));
                }
                uses
            }
            Opcode::Stfd => {
                let mut uses = vec![Field::frS(FPR(((self.code >> 21u8) & 0x1f) as _))];
                if ((self.code >> 16u8) & 0x1f) != 0 {
                    uses.push(Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)));
                }
                uses
            }
            Opcode::Stfdu => {
                let mut uses = vec![
                    Field::frS(FPR(((self.code >> 21u8) & 0x1f) as _)),
                    Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::Stfdux => {
                let mut uses = vec![
                    Field::frS(FPR(((self.code >> 21u8) & 0x1f) as _)),
                    Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                    Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::Stfdx => {
                let mut uses = vec![
                    Field::frS(FPR(((self.code >> 21u8) & 0x1f) as _)),
                    Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                if ((self.code >> 16u8) & 0x1f) != 0 {
                    uses.push(Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)));
                }
                uses
            }
            Opcode::Stfiwx => {
                let mut uses = vec![
                    Field::frS(FPR(((self.code >> 21u8) & 0x1f) as _)),
                    Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                if ((self.code >> 16u8) & 0x1f) != 0 {
                    uses.push(Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)));
                }
                uses
            }
            Opcode::Stfs => {
                let mut uses = vec![Field::frS(FPR(((self.code >> 21u8) & 0x1f) as _))];
                if ((self.code >> 16u8) & 0x1f) != 0 {
                    uses.push(Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)));
                }
                uses
            }
            Opcode::Stfsu => {
                let mut uses = vec![
                    Field::frS(FPR(((self.code >> 21u8) & 0x1f) as _)),
                    Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::Stfsux => {
                let mut uses = vec![
                    Field::frS(FPR(((self.code >> 21u8) & 0x1f) as _)),
                    Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                    Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::Stfsx => {
                let mut uses = vec![
                    Field::frS(FPR(((self.code >> 21u8) & 0x1f) as _)),
                    Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                if ((self.code >> 16u8) & 0x1f) != 0 {
                    uses.push(Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)));
                }
                uses
            }
            Opcode::Sth => {
                let mut uses = vec![Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _))];
                if ((self.code >> 16u8) & 0x1f) != 0 {
                    uses.push(Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)));
                }
                uses
            }
            Opcode::Sthbrx => {
                let mut uses = vec![
                    Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _)),
                    Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                if ((self.code >> 16u8) & 0x1f) != 0 {
                    uses.push(Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)));
                }
                uses
            }
            Opcode::Sthu => {
                let mut uses = vec![
                    Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _)),
                    Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::Sthux => {
                let mut uses = vec![
                    Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _)),
                    Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                    Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::Sthx => {
                let mut uses = vec![
                    Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _)),
                    Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                if ((self.code >> 16u8) & 0x1f) != 0 {
                    uses.push(Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)));
                }
                uses
            }
            Opcode::Stmw => {
                let mut uses = vec![Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _))];
                if ((self.code >> 16u8) & 0x1f) != 0 {
                    uses.push(Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)));
                }
                uses
            }
            Opcode::Stswi => {
                let mut uses = vec![Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _))];
                if ((self.code >> 16u8) & 0x1f) != 0 {
                    uses.push(Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)));
                }
                uses
            }
            Opcode::Stswx => {
                let mut uses = vec![
                    Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _)),
                    Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                if ((self.code >> 16u8) & 0x1f) != 0 {
                    uses.push(Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)));
                }
                uses
            }
            Opcode::Stw => {
                let mut uses = vec![Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _))];
                if ((self.code >> 16u8) & 0x1f) != 0 {
                    uses.push(Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)));
                }
                uses
            }
            Opcode::Stwbrx => {
                let mut uses = vec![
                    Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _)),
                    Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                if ((self.code >> 16u8) & 0x1f) != 0 {
                    uses.push(Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)));
                }
                uses
            }
            Opcode::Stwcx_ => {
                let mut uses = vec![
                    Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _)),
                    Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                if ((self.code >> 16u8) & 0x1f) != 0 {
                    uses.push(Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)));
                }
                uses
            }
            Opcode::Stwu => {
                let mut uses = vec![
                    Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _)),
                    Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::Stwux => {
                let mut uses = vec![
                    Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _)),
                    Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                    Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::Stwx => {
                let mut uses = vec![
                    Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _)),
                    Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                if ((self.code >> 16u8) & 0x1f) != 0 {
                    uses.push(Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)));
                }
                uses
            }
            Opcode::Subf => {
                let mut uses = vec![
                    Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                    Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::Subfc => {
                let mut uses = vec![
                    Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                    Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::Subfe => {
                let mut uses = vec![
                    Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                    Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::Subfic => {
                let mut uses = vec![Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _))];
                uses
            }
            Opcode::Subfme => {
                let mut uses = vec![Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _))];
                uses
            }
            Opcode::Subfze => {
                let mut uses = vec![Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _))];
                uses
            }
            Opcode::Sync => {
                let mut uses = vec![];
                uses
            }
            Opcode::Tlbie => {
                let mut uses = vec![Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _))];
                uses
            }
            Opcode::Tlbsync => {
                let mut uses = vec![];
                uses
            }
            Opcode::Tw => {
                let mut uses = vec![
                    Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _)),
                    Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::Twi => {
                let mut uses = vec![Field::rA(GPR(((self.code >> 16u8) & 0x1f) as _))];
                uses
            }
            Opcode::Xor => {
                let mut uses = vec![
                    Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _)),
                    Field::rB(GPR(((self.code >> 11u8) & 0x1f) as _)),
                ];
                uses
            }
            Opcode::Xori => {
                let mut uses = vec![Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _))];
                uses
            }
            Opcode::Xoris => {
                let mut uses = vec![Field::rS(GPR(((self.code >> 21u8) & 0x1f) as _))];
                uses
            }
        }
    }
    pub(crate) fn _suffix(&self) -> String {
        match self.op {
            Opcode::Illegal => String::new(),
            Opcode::Add => {
                let mut s = String::with_capacity(4);
                if self.bit(21usize) {
                    s.push('o');
                }
                if self.bit(31usize) {
                    s.push('.');
                }
                s
            }
            Opcode::Addc => {
                let mut s = String::with_capacity(4);
                if self.bit(21usize) {
                    s.push('o');
                }
                if self.bit(31usize) {
                    s.push('.');
                }
                s
            }
            Opcode::Adde => {
                let mut s = String::with_capacity(4);
                if self.bit(21usize) {
                    s.push('o');
                }
                if self.bit(31usize) {
                    s.push('.');
                }
                s
            }
            Opcode::Addi => String::new(),
            Opcode::Addic => String::new(),
            Opcode::Addic_ => String::new(),
            Opcode::Addis => String::new(),
            Opcode::Addme => {
                let mut s = String::with_capacity(4);
                if self.bit(21usize) {
                    s.push('o');
                }
                if self.bit(31usize) {
                    s.push('.');
                }
                s
            }
            Opcode::Addze => {
                let mut s = String::with_capacity(4);
                if self.bit(21usize) {
                    s.push('o');
                }
                if self.bit(31usize) {
                    s.push('.');
                }
                s
            }
            Opcode::And => {
                let mut s = String::with_capacity(4);
                if self.bit(31usize) {
                    s.push('.');
                }
                s
            }
            Opcode::Andc => {
                let mut s = String::with_capacity(4);
                if self.bit(31usize) {
                    s.push('.');
                }
                s
            }
            Opcode::Andi_ => String::new(),
            Opcode::Andis_ => String::new(),
            Opcode::B => {
                let mut s = String::with_capacity(4);
                if self.bit(31usize) {
                    s.push('l');
                }
                if self.bit(30usize) {
                    s.push('a');
                }
                s
            }
            Opcode::Bc => {
                let mut s = String::with_capacity(4);
                if self.bit(31usize) {
                    s.push('l');
                }
                if self.bit(30usize) {
                    s.push('a');
                }
                if ((self.code >> 21u8) & 0x1f) & 1 == 1
                    && ((((((self.code >> 2u8) & 0x3fff) ^ 0x2000).wrapping_sub(0x2000)) as i32)
                        << 2u8)
                        >= 0
                {
                    s.push('+');
                }
                if ((self.code >> 21u8) & 0x1f) & 1 == 1
                    && ((((((self.code >> 2u8) & 0x3fff) ^ 0x2000).wrapping_sub(0x2000)) as i32)
                        << 2u8)
                        < 0
                {
                    s.push('-');
                }
                s
            }
            Opcode::Bcctr => {
                let mut s = String::with_capacity(4);
                if self.bit(31usize) {
                    s.push('l');
                }
                if ((self.code >> 21u8) & 0x1f) & 1 == 1 {
                    s.push('+');
                }
                s
            }
            Opcode::Bclr => {
                let mut s = String::with_capacity(4);
                if self.bit(31usize) {
                    s.push('l');
                }
                if ((self.code >> 21u8) & 0x1f) & 1 == 1 {
                    s.push('+');
                }
                s
            }
            Opcode::Cmp => String::new(),
            Opcode::Cmpi => String::new(),
            Opcode::Cmpl => String::new(),
            Opcode::Cmpli => String::new(),
            Opcode::Cntlzw => {
                let mut s = String::with_capacity(4);
                if self.bit(31usize) {
                    s.push('.');
                }
                s
            }
            Opcode::Crand => String::new(),
            Opcode::Crandc => String::new(),
            Opcode::Creqv => String::new(),
            Opcode::Crnand => String::new(),
            Opcode::Crnor => String::new(),
            Opcode::Cror => String::new(),
            Opcode::Crorc => String::new(),
            Opcode::Crxor => String::new(),
            Opcode::Dcbf => String::new(),
            Opcode::Dcbi => String::new(),
            Opcode::Dcbst => String::new(),
            Opcode::Dcbt => String::new(),
            Opcode::Dcbtst => String::new(),
            Opcode::Dcbz => String::new(),
            Opcode::DcbzL => String::new(),
            Opcode::Divw => {
                let mut s = String::with_capacity(4);
                if self.bit(21usize) {
                    s.push('o');
                }
                if self.bit(31usize) {
                    s.push('.');
                }
                s
            }
            Opcode::Divwu => {
                let mut s = String::with_capacity(4);
                if self.bit(21usize) {
                    s.push('o');
                }
                if self.bit(31usize) {
                    s.push('.');
                }
                s
            }
            Opcode::Eciwx => String::new(),
            Opcode::Ecowx => String::new(),
            Opcode::Eieio => String::new(),
            Opcode::Eqv => {
                let mut s = String::with_capacity(4);
                if self.bit(31usize) {
                    s.push('.');
                }
                s
            }
            Opcode::Extsb => {
                let mut s = String::with_capacity(4);
                if self.bit(31usize) {
                    s.push('.');
                }
                s
            }
            Opcode::Extsh => {
                let mut s = String::with_capacity(4);
                if self.bit(31usize) {
                    s.push('.');
                }
                s
            }
            Opcode::Fabs => {
                let mut s = String::with_capacity(4);
                if self.bit(31usize) {
                    s.push('.');
                }
                s
            }
            Opcode::Fadd => {
                let mut s = String::with_capacity(4);
                if self.bit(31usize) {
                    s.push('.');
                }
                s
            }
            Opcode::Fadds => {
                let mut s = String::with_capacity(4);
                if self.bit(31usize) {
                    s.push('.');
                }
                s
            }
            Opcode::Fcmpo => String::new(),
            Opcode::Fcmpu => String::new(),
            Opcode::Fctiw => {
                let mut s = String::with_capacity(4);
                if self.bit(31usize) {
                    s.push('.');
                }
                s
            }
            Opcode::Fctiwz => {
                let mut s = String::with_capacity(4);
                if self.bit(31usize) {
                    s.push('.');
                }
                s
            }
            Opcode::Fdiv => {
                let mut s = String::with_capacity(4);
                if self.bit(31usize) {
                    s.push('.');
                }
                s
            }
            Opcode::Fdivs => {
                let mut s = String::with_capacity(4);
                if self.bit(31usize) {
                    s.push('.');
                }
                s
            }
            Opcode::Fmadd => {
                let mut s = String::with_capacity(4);
                if self.bit(31usize) {
                    s.push('.');
                }
                s
            }
            Opcode::Fmadds => {
                let mut s = String::with_capacity(4);
                if self.bit(31usize) {
                    s.push('.');
                }
                s
            }
            Opcode::Fmr => {
                let mut s = String::with_capacity(4);
                if self.bit(31usize) {
                    s.push('.');
                }
                s
            }
            Opcode::Fmsub => {
                let mut s = String::with_capacity(4);
                if self.bit(31usize) {
                    s.push('.');
                }
                s
            }
            Opcode::Fmsubs => {
                let mut s = String::with_capacity(4);
                if self.bit(31usize) {
                    s.push('.');
                }
                s
            }
            Opcode::Fmul => {
                let mut s = String::with_capacity(4);
                if self.bit(31usize) {
                    s.push('.');
                }
                s
            }
            Opcode::Fmuls => {
                let mut s = String::with_capacity(4);
                if self.bit(31usize) {
                    s.push('.');
                }
                s
            }
            Opcode::Fnabs => {
                let mut s = String::with_capacity(4);
                if self.bit(31usize) {
                    s.push('.');
                }
                s
            }
            Opcode::Fneg => {
                let mut s = String::with_capacity(4);
                if self.bit(31usize) {
                    s.push('.');
                }
                s
            }
            Opcode::Fnmadd => {
                let mut s = String::with_capacity(4);
                if self.bit(31usize) {
                    s.push('.');
                }
                s
            }
            Opcode::Fnmadds => {
                let mut s = String::with_capacity(4);
                if self.bit(31usize) {
                    s.push('.');
                }
                s
            }
            Opcode::Fnmsub => {
                let mut s = String::with_capacity(4);
                if self.bit(31usize) {
                    s.push('.');
                }
                s
            }
            Opcode::Fnmsubs => {
                let mut s = String::with_capacity(4);
                if self.bit(31usize) {
                    s.push('.');
                }
                s
            }
            Opcode::Fres => {
                let mut s = String::with_capacity(4);
                if self.bit(31usize) {
                    s.push('.');
                }
                s
            }
            Opcode::Frsp => {
                let mut s = String::with_capacity(4);
                if self.bit(31usize) {
                    s.push('.');
                }
                s
            }
            Opcode::Frsqrte => {
                let mut s = String::with_capacity(4);
                if self.bit(31usize) {
                    s.push('.');
                }
                s
            }
            Opcode::Fsel => {
                let mut s = String::with_capacity(4);
                if self.bit(31usize) {
                    s.push('.');
                }
                s
            }
            Opcode::Fsub => {
                let mut s = String::with_capacity(4);
                if self.bit(31usize) {
                    s.push('.');
                }
                s
            }
            Opcode::Fsubs => {
                let mut s = String::with_capacity(4);
                if self.bit(31usize) {
                    s.push('.');
                }
                s
            }
            Opcode::Icbi => {
                let mut s = String::with_capacity(4);
                if self.bit(31usize) {
                    s.push('.');
                }
                s
            }
            Opcode::Isync => String::new(),
            Opcode::Lbz => String::new(),
            Opcode::Lbzu => String::new(),
            Opcode::Lbzux => String::new(),
            Opcode::Lbzx => String::new(),
            Opcode::Lfd => String::new(),
            Opcode::Lfdu => String::new(),
            Opcode::Lfdux => String::new(),
            Opcode::Lfdx => String::new(),
            Opcode::Lfs => String::new(),
            Opcode::Lfsu => String::new(),
            Opcode::Lfsux => String::new(),
            Opcode::Lfsx => String::new(),
            Opcode::Lha => String::new(),
            Opcode::Lhau => String::new(),
            Opcode::Lhaux => String::new(),
            Opcode::Lhax => String::new(),
            Opcode::Lhbrx => String::new(),
            Opcode::Lhz => String::new(),
            Opcode::Lhzu => String::new(),
            Opcode::Lhzux => String::new(),
            Opcode::Lhzx => String::new(),
            Opcode::Lmw => String::new(),
            Opcode::Lswi => String::new(),
            Opcode::Lswx => String::new(),
            Opcode::Lwarx => String::new(),
            Opcode::Lwbrx => String::new(),
            Opcode::Lwz => String::new(),
            Opcode::Lwzu => String::new(),
            Opcode::Lwzux => String::new(),
            Opcode::Lwzx => String::new(),
            Opcode::Mcrf => String::new(),
            Opcode::Mcrfs => String::new(),
            Opcode::Mcrxr => String::new(),
            Opcode::Mfcr => String::new(),
            Opcode::Mffs => String::new(),
            Opcode::Mfmsr => String::new(),
            Opcode::Mfspr => String::new(),
            Opcode::Mfsr => String::new(),
            Opcode::Mfsrin => String::new(),
            Opcode::Mftb => String::new(),
            Opcode::Mtcrf => String::new(),
            Opcode::Mtfsb0 => {
                let mut s = String::with_capacity(4);
                if self.bit(31usize) {
                    s.push('.');
                }
                s
            }
            Opcode::Mtfsb1 => {
                let mut s = String::with_capacity(4);
                if self.bit(31usize) {
                    s.push('.');
                }
                s
            }
            Opcode::Mtfsf => {
                let mut s = String::with_capacity(4);
                if self.bit(31usize) {
                    s.push('.');
                }
                s
            }
            Opcode::Mtfsfi => {
                let mut s = String::with_capacity(4);
                if self.bit(31usize) {
                    s.push('.');
                }
                s
            }
            Opcode::Mtmsr => String::new(),
            Opcode::Mtspr => String::new(),
            Opcode::Mtsr => String::new(),
            Opcode::Mtsrin => String::new(),
            Opcode::Mulhw => {
                let mut s = String::with_capacity(4);
                if self.bit(31usize) {
                    s.push('.');
                }
                s
            }
            Opcode::Mulhwu => {
                let mut s = String::with_capacity(4);
                if self.bit(31usize) {
                    s.push('.');
                }
                s
            }
            Opcode::Mulli => String::new(),
            Opcode::Mullw => {
                let mut s = String::with_capacity(4);
                if self.bit(21usize) {
                    s.push('o');
                }
                if self.bit(31usize) {
                    s.push('.');
                }
                s
            }
            Opcode::Nand => {
                let mut s = String::with_capacity(4);
                if self.bit(31usize) {
                    s.push('.');
                }
                s
            }
            Opcode::Neg => {
                let mut s = String::with_capacity(4);
                if self.bit(21usize) {
                    s.push('o');
                }
                if self.bit(31usize) {
                    s.push('.');
                }
                s
            }
            Opcode::Nor => {
                let mut s = String::with_capacity(4);
                if self.bit(31usize) {
                    s.push('.');
                }
                s
            }
            Opcode::Or => {
                let mut s = String::with_capacity(4);
                if self.bit(31usize) {
                    s.push('.');
                }
                s
            }
            Opcode::Orc => {
                let mut s = String::with_capacity(4);
                if self.bit(31usize) {
                    s.push('.');
                }
                s
            }
            Opcode::Ori => String::new(),
            Opcode::Oris => String::new(),
            Opcode::PsqL => String::new(),
            Opcode::PsqLu => String::new(),
            Opcode::PsqLux => String::new(),
            Opcode::PsqLx => String::new(),
            Opcode::PsqSt => String::new(),
            Opcode::PsqStu => String::new(),
            Opcode::PsqStux => String::new(),
            Opcode::PsqStx => String::new(),
            Opcode::PsAbs => String::new(),
            Opcode::PsAdd => String::new(),
            Opcode::PsCmpo0 => String::new(),
            Opcode::PsCmpo1 => String::new(),
            Opcode::PsCmpu0 => String::new(),
            Opcode::PsCmpu1 => String::new(),
            Opcode::PsDiv => String::new(),
            Opcode::PsMadd => String::new(),
            Opcode::PsMadds0 => String::new(),
            Opcode::PsMadds1 => String::new(),
            Opcode::PsMerge00 => String::new(),
            Opcode::PsMerge01 => String::new(),
            Opcode::PsMerge10 => String::new(),
            Opcode::PsMerge11 => String::new(),
            Opcode::PsMr => String::new(),
            Opcode::PsMsub => String::new(),
            Opcode::PsMul => String::new(),
            Opcode::PsMuls0 => String::new(),
            Opcode::PsMuls1 => String::new(),
            Opcode::PsNabs => String::new(),
            Opcode::PsNeg => String::new(),
            Opcode::PsNmadd => String::new(),
            Opcode::PsNmsub => String::new(),
            Opcode::PsRes => String::new(),
            Opcode::PsRsqrte => String::new(),
            Opcode::PsSel => String::new(),
            Opcode::PsSub => String::new(),
            Opcode::PsSum0 => String::new(),
            Opcode::PsSum1 => String::new(),
            Opcode::Rfi => String::new(),
            Opcode::Rlwimi => {
                let mut s = String::with_capacity(4);
                if self.bit(31usize) {
                    s.push('.');
                }
                s
            }
            Opcode::Rlwinm => {
                let mut s = String::with_capacity(4);
                if self.bit(31usize) {
                    s.push('.');
                }
                s
            }
            Opcode::Rlwnm => {
                let mut s = String::with_capacity(4);
                if self.bit(31usize) {
                    s.push('.');
                }
                s
            }
            Opcode::Sc => String::new(),
            Opcode::Slw => {
                let mut s = String::with_capacity(4);
                if self.bit(31usize) {
                    s.push('.');
                }
                s
            }
            Opcode::Sraw => {
                let mut s = String::with_capacity(4);
                if self.bit(31usize) {
                    s.push('.');
                }
                s
            }
            Opcode::Srawi => {
                let mut s = String::with_capacity(4);
                if self.bit(31usize) {
                    s.push('.');
                }
                s
            }
            Opcode::Srw => {
                let mut s = String::with_capacity(4);
                if self.bit(31usize) {
                    s.push('.');
                }
                s
            }
            Opcode::Stb => String::new(),
            Opcode::Stbu => String::new(),
            Opcode::Stbux => String::new(),
            Opcode::Stbx => String::new(),
            Opcode::Stfd => String::new(),
            Opcode::Stfdu => String::new(),
            Opcode::Stfdux => String::new(),
            Opcode::Stfdx => String::new(),
            Opcode::Stfiwx => String::new(),
            Opcode::Stfs => String::new(),
            Opcode::Stfsu => String::new(),
            Opcode::Stfsux => String::new(),
            Opcode::Stfsx => String::new(),
            Opcode::Sth => String::new(),
            Opcode::Sthbrx => String::new(),
            Opcode::Sthu => String::new(),
            Opcode::Sthux => String::new(),
            Opcode::Sthx => String::new(),
            Opcode::Stmw => String::new(),
            Opcode::Stswi => String::new(),
            Opcode::Stswx => String::new(),
            Opcode::Stw => String::new(),
            Opcode::Stwbrx => String::new(),
            Opcode::Stwcx_ => String::new(),
            Opcode::Stwu => String::new(),
            Opcode::Stwux => String::new(),
            Opcode::Stwx => String::new(),
            Opcode::Subf => {
                let mut s = String::with_capacity(4);
                if self.bit(21usize) {
                    s.push('o');
                }
                if self.bit(31usize) {
                    s.push('.');
                }
                s
            }
            Opcode::Subfc => {
                let mut s = String::with_capacity(4);
                if self.bit(21usize) {
                    s.push('o');
                }
                if self.bit(31usize) {
                    s.push('.');
                }
                s
            }
            Opcode::Subfe => {
                let mut s = String::with_capacity(4);
                if self.bit(21usize) {
                    s.push('o');
                }
                if self.bit(31usize) {
                    s.push('.');
                }
                s
            }
            Opcode::Subfic => String::new(),
            Opcode::Subfme => {
                let mut s = String::with_capacity(4);
                if self.bit(21usize) {
                    s.push('o');
                }
                if self.bit(31usize) {
                    s.push('.');
                }
                s
            }
            Opcode::Subfze => {
                let mut s = String::with_capacity(4);
                if self.bit(21usize) {
                    s.push('o');
                }
                if self.bit(31usize) {
                    s.push('.');
                }
                s
            }
            Opcode::Sync => String::new(),
            Opcode::Tlbie => String::new(),
            Opcode::Tlbsync => String::new(),
            Opcode::Tw => String::new(),
            Opcode::Twi => String::new(),
            Opcode::Xor => {
                let mut s = String::with_capacity(4);
                if self.bit(31usize) {
                    s.push('.');
                }
                s
            }
            Opcode::Xori => String::new(),
            Opcode::Xoris => String::new(),
        }
    }
    pub(crate) fn _simplified(self) -> SimplifiedIns {
        match self.op {
            Opcode::Addi => {
                if ((self.code >> 16u8) & 0x1f) == 0 {
                    return SimplifiedIns {
                        mnemonic: "li",
                        suffix: String::new(),
                        args: vec![
                            Argument::GPR(GPR(((self.code >> 21u8) & 0x1f) as _)),
                            Argument::Simm(Simm(
                                ((((self.code & 0xffff) ^ 0x8000).wrapping_sub(0x8000)) as i32)
                                    as _,
                            )),
                        ],
                        ins: self,
                    };
                }
            }
            Opcode::Addis => {
                if ((self.code >> 16u8) & 0x1f) == 0 {
                    return SimplifiedIns {
                        mnemonic: "lis",
                        suffix: String::new(),
                        args: vec![
                            Argument::GPR(GPR(((self.code >> 21u8) & 0x1f) as _)),
                            Argument::Uimm(Uimm((self.code & 0xffff) as _)),
                        ],
                        ins: self,
                    };
                }
            }
            Opcode::Bc => {
                if ((self.code >> 21u8) & 0x1f) & 0b11110 == 12 && ((self.code >> 16u8) & 0x1f) == 0
                {
                    return SimplifiedIns {
                        mnemonic: "blt",
                        suffix: {
                            {
                                let mut s = String::with_capacity(4);
                                if self.bit(31usize) {
                                    s.push('l');
                                }
                                if self.bit(30usize) {
                                    s.push('a');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1
                                    && ((((((self.code >> 2u8) & 0x3fff) ^ 0x2000)
                                        .wrapping_sub(0x2000))
                                        as i32)
                                        << 2u8)
                                        >= 0
                                {
                                    s.push('+');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1
                                    && ((((((self.code >> 2u8) & 0x3fff) ^ 0x2000)
                                        .wrapping_sub(0x2000))
                                        as i32)
                                        << 2u8)
                                        < 0
                                {
                                    s.push('-');
                                }
                                s
                            }
                        },
                        args: vec![Argument::BranchDest(BranchDest(
                            ((((((self.code >> 2u8) & 0x3fff) ^ 0x2000).wrapping_sub(0x2000))
                                as i32)
                                << 2u8) as _,
                        ))],
                        ins: self,
                    };
                }
                if ((self.code >> 21u8) & 0x1f) & 0b11110 == 12
                    && ((self.code >> 16u8) & 0x1f) & 0b11 == 0
                {
                    return SimplifiedIns {
                        mnemonic: "blt",
                        suffix: {
                            {
                                let mut s = String::with_capacity(4);
                                if self.bit(31usize) {
                                    s.push('l');
                                }
                                if self.bit(30usize) {
                                    s.push('a');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1
                                    && ((((((self.code >> 2u8) & 0x3fff) ^ 0x2000)
                                        .wrapping_sub(0x2000))
                                        as i32)
                                        << 2u8)
                                        >= 0
                                {
                                    s.push('+');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1
                                    && ((((((self.code >> 2u8) & 0x3fff) ^ 0x2000)
                                        .wrapping_sub(0x2000))
                                        as i32)
                                        << 2u8)
                                        < 0
                                {
                                    s.push('-');
                                }
                                s
                            }
                        },
                        args: vec![
                            Argument::CRField(CRField(((self.code >> 18u8) & 0x7) as _)),
                            Argument::BranchDest(BranchDest(
                                ((((((self.code >> 2u8) & 0x3fff) ^ 0x2000).wrapping_sub(0x2000))
                                    as i32)
                                    << 2u8) as _,
                            )),
                        ],
                        ins: self,
                    };
                }
                if ((self.code >> 21u8) & 0x1f) & 0b11110 == 4 && ((self.code >> 16u8) & 0x1f) == 1
                {
                    return SimplifiedIns {
                        mnemonic: "ble",
                        suffix: {
                            {
                                let mut s = String::with_capacity(4);
                                if self.bit(31usize) {
                                    s.push('l');
                                }
                                if self.bit(30usize) {
                                    s.push('a');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1
                                    && ((((((self.code >> 2u8) & 0x3fff) ^ 0x2000)
                                        .wrapping_sub(0x2000))
                                        as i32)
                                        << 2u8)
                                        >= 0
                                {
                                    s.push('+');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1
                                    && ((((((self.code >> 2u8) & 0x3fff) ^ 0x2000)
                                        .wrapping_sub(0x2000))
                                        as i32)
                                        << 2u8)
                                        < 0
                                {
                                    s.push('-');
                                }
                                s
                            }
                        },
                        args: vec![Argument::BranchDest(BranchDest(
                            ((((((self.code >> 2u8) & 0x3fff) ^ 0x2000).wrapping_sub(0x2000))
                                as i32)
                                << 2u8) as _,
                        ))],
                        ins: self,
                    };
                }
                if ((self.code >> 21u8) & 0x1f) & 0b11110 == 4
                    && ((self.code >> 16u8) & 0x1f) & 0b11 == 1
                {
                    return SimplifiedIns {
                        mnemonic: "ble",
                        suffix: {
                            {
                                let mut s = String::with_capacity(4);
                                if self.bit(31usize) {
                                    s.push('l');
                                }
                                if self.bit(30usize) {
                                    s.push('a');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1
                                    && ((((((self.code >> 2u8) & 0x3fff) ^ 0x2000)
                                        .wrapping_sub(0x2000))
                                        as i32)
                                        << 2u8)
                                        >= 0
                                {
                                    s.push('+');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1
                                    && ((((((self.code >> 2u8) & 0x3fff) ^ 0x2000)
                                        .wrapping_sub(0x2000))
                                        as i32)
                                        << 2u8)
                                        < 0
                                {
                                    s.push('-');
                                }
                                s
                            }
                        },
                        args: vec![
                            Argument::CRField(CRField(((self.code >> 18u8) & 0x7) as _)),
                            Argument::BranchDest(BranchDest(
                                ((((((self.code >> 2u8) & 0x3fff) ^ 0x2000).wrapping_sub(0x2000))
                                    as i32)
                                    << 2u8) as _,
                            )),
                        ],
                        ins: self,
                    };
                }
                if ((self.code >> 21u8) & 0x1f) & 0b11110 == 12 && ((self.code >> 16u8) & 0x1f) == 2
                {
                    return SimplifiedIns {
                        mnemonic: "beq",
                        suffix: {
                            {
                                let mut s = String::with_capacity(4);
                                if self.bit(31usize) {
                                    s.push('l');
                                }
                                if self.bit(30usize) {
                                    s.push('a');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1
                                    && ((((((self.code >> 2u8) & 0x3fff) ^ 0x2000)
                                        .wrapping_sub(0x2000))
                                        as i32)
                                        << 2u8)
                                        >= 0
                                {
                                    s.push('+');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1
                                    && ((((((self.code >> 2u8) & 0x3fff) ^ 0x2000)
                                        .wrapping_sub(0x2000))
                                        as i32)
                                        << 2u8)
                                        < 0
                                {
                                    s.push('-');
                                }
                                s
                            }
                        },
                        args: vec![Argument::BranchDest(BranchDest(
                            ((((((self.code >> 2u8) & 0x3fff) ^ 0x2000).wrapping_sub(0x2000))
                                as i32)
                                << 2u8) as _,
                        ))],
                        ins: self,
                    };
                }
                if ((self.code >> 21u8) & 0x1f) & 0b11110 == 12
                    && ((self.code >> 16u8) & 0x1f) & 0b11 == 2
                {
                    return SimplifiedIns {
                        mnemonic: "beq",
                        suffix: {
                            {
                                let mut s = String::with_capacity(4);
                                if self.bit(31usize) {
                                    s.push('l');
                                }
                                if self.bit(30usize) {
                                    s.push('a');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1
                                    && ((((((self.code >> 2u8) & 0x3fff) ^ 0x2000)
                                        .wrapping_sub(0x2000))
                                        as i32)
                                        << 2u8)
                                        >= 0
                                {
                                    s.push('+');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1
                                    && ((((((self.code >> 2u8) & 0x3fff) ^ 0x2000)
                                        .wrapping_sub(0x2000))
                                        as i32)
                                        << 2u8)
                                        < 0
                                {
                                    s.push('-');
                                }
                                s
                            }
                        },
                        args: vec![
                            Argument::CRField(CRField(((self.code >> 18u8) & 0x7) as _)),
                            Argument::BranchDest(BranchDest(
                                ((((((self.code >> 2u8) & 0x3fff) ^ 0x2000).wrapping_sub(0x2000))
                                    as i32)
                                    << 2u8) as _,
                            )),
                        ],
                        ins: self,
                    };
                }
                if ((self.code >> 21u8) & 0x1f) & 0b11110 == 4 && ((self.code >> 16u8) & 0x1f) == 0
                {
                    return SimplifiedIns {
                        mnemonic: "bge",
                        suffix: {
                            {
                                let mut s = String::with_capacity(4);
                                if self.bit(31usize) {
                                    s.push('l');
                                }
                                if self.bit(30usize) {
                                    s.push('a');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1
                                    && ((((((self.code >> 2u8) & 0x3fff) ^ 0x2000)
                                        .wrapping_sub(0x2000))
                                        as i32)
                                        << 2u8)
                                        >= 0
                                {
                                    s.push('+');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1
                                    && ((((((self.code >> 2u8) & 0x3fff) ^ 0x2000)
                                        .wrapping_sub(0x2000))
                                        as i32)
                                        << 2u8)
                                        < 0
                                {
                                    s.push('-');
                                }
                                s
                            }
                        },
                        args: vec![Argument::BranchDest(BranchDest(
                            ((((((self.code >> 2u8) & 0x3fff) ^ 0x2000).wrapping_sub(0x2000))
                                as i32)
                                << 2u8) as _,
                        ))],
                        ins: self,
                    };
                }
                if ((self.code >> 21u8) & 0x1f) & 0b11110 == 4
                    && ((self.code >> 16u8) & 0x1f) & 0b11 == 0
                {
                    return SimplifiedIns {
                        mnemonic: "bge",
                        suffix: {
                            {
                                let mut s = String::with_capacity(4);
                                if self.bit(31usize) {
                                    s.push('l');
                                }
                                if self.bit(30usize) {
                                    s.push('a');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1
                                    && ((((((self.code >> 2u8) & 0x3fff) ^ 0x2000)
                                        .wrapping_sub(0x2000))
                                        as i32)
                                        << 2u8)
                                        >= 0
                                {
                                    s.push('+');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1
                                    && ((((((self.code >> 2u8) & 0x3fff) ^ 0x2000)
                                        .wrapping_sub(0x2000))
                                        as i32)
                                        << 2u8)
                                        < 0
                                {
                                    s.push('-');
                                }
                                s
                            }
                        },
                        args: vec![
                            Argument::CRField(CRField(((self.code >> 18u8) & 0x7) as _)),
                            Argument::BranchDest(BranchDest(
                                ((((((self.code >> 2u8) & 0x3fff) ^ 0x2000).wrapping_sub(0x2000))
                                    as i32)
                                    << 2u8) as _,
                            )),
                        ],
                        ins: self,
                    };
                }
                if ((self.code >> 21u8) & 0x1f) & 0b11110 == 12 && ((self.code >> 16u8) & 0x1f) == 1
                {
                    return SimplifiedIns {
                        mnemonic: "bgt",
                        suffix: {
                            {
                                let mut s = String::with_capacity(4);
                                if self.bit(31usize) {
                                    s.push('l');
                                }
                                if self.bit(30usize) {
                                    s.push('a');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1
                                    && ((((((self.code >> 2u8) & 0x3fff) ^ 0x2000)
                                        .wrapping_sub(0x2000))
                                        as i32)
                                        << 2u8)
                                        >= 0
                                {
                                    s.push('+');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1
                                    && ((((((self.code >> 2u8) & 0x3fff) ^ 0x2000)
                                        .wrapping_sub(0x2000))
                                        as i32)
                                        << 2u8)
                                        < 0
                                {
                                    s.push('-');
                                }
                                s
                            }
                        },
                        args: vec![Argument::BranchDest(BranchDest(
                            ((((((self.code >> 2u8) & 0x3fff) ^ 0x2000).wrapping_sub(0x2000))
                                as i32)
                                << 2u8) as _,
                        ))],
                        ins: self,
                    };
                }
                if ((self.code >> 21u8) & 0x1f) & 0b11110 == 12
                    && ((self.code >> 16u8) & 0x1f) & 0b11 == 1
                {
                    return SimplifiedIns {
                        mnemonic: "bgt",
                        suffix: {
                            {
                                let mut s = String::with_capacity(4);
                                if self.bit(31usize) {
                                    s.push('l');
                                }
                                if self.bit(30usize) {
                                    s.push('a');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1
                                    && ((((((self.code >> 2u8) & 0x3fff) ^ 0x2000)
                                        .wrapping_sub(0x2000))
                                        as i32)
                                        << 2u8)
                                        >= 0
                                {
                                    s.push('+');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1
                                    && ((((((self.code >> 2u8) & 0x3fff) ^ 0x2000)
                                        .wrapping_sub(0x2000))
                                        as i32)
                                        << 2u8)
                                        < 0
                                {
                                    s.push('-');
                                }
                                s
                            }
                        },
                        args: vec![
                            Argument::CRField(CRField(((self.code >> 18u8) & 0x7) as _)),
                            Argument::BranchDest(BranchDest(
                                ((((((self.code >> 2u8) & 0x3fff) ^ 0x2000).wrapping_sub(0x2000))
                                    as i32)
                                    << 2u8) as _,
                            )),
                        ],
                        ins: self,
                    };
                }
                if ((self.code >> 21u8) & 0x1f) & 0b11110 == 4 && ((self.code >> 16u8) & 0x1f) == 2
                {
                    return SimplifiedIns {
                        mnemonic: "bne",
                        suffix: {
                            {
                                let mut s = String::with_capacity(4);
                                if self.bit(31usize) {
                                    s.push('l');
                                }
                                if self.bit(30usize) {
                                    s.push('a');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1
                                    && ((((((self.code >> 2u8) & 0x3fff) ^ 0x2000)
                                        .wrapping_sub(0x2000))
                                        as i32)
                                        << 2u8)
                                        >= 0
                                {
                                    s.push('+');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1
                                    && ((((((self.code >> 2u8) & 0x3fff) ^ 0x2000)
                                        .wrapping_sub(0x2000))
                                        as i32)
                                        << 2u8)
                                        < 0
                                {
                                    s.push('-');
                                }
                                s
                            }
                        },
                        args: vec![Argument::BranchDest(BranchDest(
                            ((((((self.code >> 2u8) & 0x3fff) ^ 0x2000).wrapping_sub(0x2000))
                                as i32)
                                << 2u8) as _,
                        ))],
                        ins: self,
                    };
                }
                if ((self.code >> 21u8) & 0x1f) & 0b11110 == 4
                    && ((self.code >> 16u8) & 0x1f) & 0b11 == 2
                {
                    return SimplifiedIns {
                        mnemonic: "bne",
                        suffix: {
                            {
                                let mut s = String::with_capacity(4);
                                if self.bit(31usize) {
                                    s.push('l');
                                }
                                if self.bit(30usize) {
                                    s.push('a');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1
                                    && ((((((self.code >> 2u8) & 0x3fff) ^ 0x2000)
                                        .wrapping_sub(0x2000))
                                        as i32)
                                        << 2u8)
                                        >= 0
                                {
                                    s.push('+');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1
                                    && ((((((self.code >> 2u8) & 0x3fff) ^ 0x2000)
                                        .wrapping_sub(0x2000))
                                        as i32)
                                        << 2u8)
                                        < 0
                                {
                                    s.push('-');
                                }
                                s
                            }
                        },
                        args: vec![
                            Argument::CRField(CRField(((self.code >> 18u8) & 0x7) as _)),
                            Argument::BranchDest(BranchDest(
                                ((((((self.code >> 2u8) & 0x3fff) ^ 0x2000).wrapping_sub(0x2000))
                                    as i32)
                                    << 2u8) as _,
                            )),
                        ],
                        ins: self,
                    };
                }
                if ((self.code >> 21u8) & 0x1f) & 0b11110 == 12 && ((self.code >> 16u8) & 0x1f) == 3
                {
                    return SimplifiedIns {
                        mnemonic: "bso",
                        suffix: {
                            {
                                let mut s = String::with_capacity(4);
                                if self.bit(31usize) {
                                    s.push('l');
                                }
                                if self.bit(30usize) {
                                    s.push('a');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1
                                    && ((((((self.code >> 2u8) & 0x3fff) ^ 0x2000)
                                        .wrapping_sub(0x2000))
                                        as i32)
                                        << 2u8)
                                        >= 0
                                {
                                    s.push('+');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1
                                    && ((((((self.code >> 2u8) & 0x3fff) ^ 0x2000)
                                        .wrapping_sub(0x2000))
                                        as i32)
                                        << 2u8)
                                        < 0
                                {
                                    s.push('-');
                                }
                                s
                            }
                        },
                        args: vec![Argument::BranchDest(BranchDest(
                            ((((((self.code >> 2u8) & 0x3fff) ^ 0x2000).wrapping_sub(0x2000))
                                as i32)
                                << 2u8) as _,
                        ))],
                        ins: self,
                    };
                }
                if ((self.code >> 21u8) & 0x1f) & 0b11110 == 12
                    && ((self.code >> 16u8) & 0x1f) & 0b11 == 3
                {
                    return SimplifiedIns {
                        mnemonic: "bso",
                        suffix: {
                            {
                                let mut s = String::with_capacity(4);
                                if self.bit(31usize) {
                                    s.push('l');
                                }
                                if self.bit(30usize) {
                                    s.push('a');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1
                                    && ((((((self.code >> 2u8) & 0x3fff) ^ 0x2000)
                                        .wrapping_sub(0x2000))
                                        as i32)
                                        << 2u8)
                                        >= 0
                                {
                                    s.push('+');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1
                                    && ((((((self.code >> 2u8) & 0x3fff) ^ 0x2000)
                                        .wrapping_sub(0x2000))
                                        as i32)
                                        << 2u8)
                                        < 0
                                {
                                    s.push('-');
                                }
                                s
                            }
                        },
                        args: vec![
                            Argument::CRField(CRField(((self.code >> 18u8) & 0x7) as _)),
                            Argument::BranchDest(BranchDest(
                                ((((((self.code >> 2u8) & 0x3fff) ^ 0x2000).wrapping_sub(0x2000))
                                    as i32)
                                    << 2u8) as _,
                            )),
                        ],
                        ins: self,
                    };
                }
                if ((self.code >> 21u8) & 0x1f) & 0b11110 == 4 && ((self.code >> 16u8) & 0x1f) == 3
                {
                    return SimplifiedIns {
                        mnemonic: "bns",
                        suffix: {
                            {
                                let mut s = String::with_capacity(4);
                                if self.bit(31usize) {
                                    s.push('l');
                                }
                                if self.bit(30usize) {
                                    s.push('a');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1
                                    && ((((((self.code >> 2u8) & 0x3fff) ^ 0x2000)
                                        .wrapping_sub(0x2000))
                                        as i32)
                                        << 2u8)
                                        >= 0
                                {
                                    s.push('+');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1
                                    && ((((((self.code >> 2u8) & 0x3fff) ^ 0x2000)
                                        .wrapping_sub(0x2000))
                                        as i32)
                                        << 2u8)
                                        < 0
                                {
                                    s.push('-');
                                }
                                s
                            }
                        },
                        args: vec![Argument::BranchDest(BranchDest(
                            ((((((self.code >> 2u8) & 0x3fff) ^ 0x2000).wrapping_sub(0x2000))
                                as i32)
                                << 2u8) as _,
                        ))],
                        ins: self,
                    };
                }
                if ((self.code >> 21u8) & 0x1f) & 0b11110 == 4
                    && ((self.code >> 16u8) & 0x1f) & 0b11 == 3
                {
                    return SimplifiedIns {
                        mnemonic: "bns",
                        suffix: {
                            {
                                let mut s = String::with_capacity(4);
                                if self.bit(31usize) {
                                    s.push('l');
                                }
                                if self.bit(30usize) {
                                    s.push('a');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1
                                    && ((((((self.code >> 2u8) & 0x3fff) ^ 0x2000)
                                        .wrapping_sub(0x2000))
                                        as i32)
                                        << 2u8)
                                        >= 0
                                {
                                    s.push('+');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1
                                    && ((((((self.code >> 2u8) & 0x3fff) ^ 0x2000)
                                        .wrapping_sub(0x2000))
                                        as i32)
                                        << 2u8)
                                        < 0
                                {
                                    s.push('-');
                                }
                                s
                            }
                        },
                        args: vec![
                            Argument::CRField(CRField(((self.code >> 18u8) & 0x7) as _)),
                            Argument::BranchDest(BranchDest(
                                ((((((self.code >> 2u8) & 0x3fff) ^ 0x2000).wrapping_sub(0x2000))
                                    as i32)
                                    << 2u8) as _,
                            )),
                        ],
                        ins: self,
                    };
                }
                if ((self.code >> 21u8) & 0x1f) & 0b11110 == 16 && ((self.code >> 16u8) & 0x1f) == 0
                {
                    return SimplifiedIns {
                        mnemonic: "bdnz",
                        suffix: {
                            {
                                let mut s = String::with_capacity(4);
                                if self.bit(31usize) {
                                    s.push('l');
                                }
                                if self.bit(30usize) {
                                    s.push('a');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1
                                    && ((((((self.code >> 2u8) & 0x3fff) ^ 0x2000)
                                        .wrapping_sub(0x2000))
                                        as i32)
                                        << 2u8)
                                        >= 0
                                {
                                    s.push('+');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1
                                    && ((((((self.code >> 2u8) & 0x3fff) ^ 0x2000)
                                        .wrapping_sub(0x2000))
                                        as i32)
                                        << 2u8)
                                        < 0
                                {
                                    s.push('-');
                                }
                                s
                            }
                        },
                        args: vec![Argument::BranchDest(BranchDest(
                            ((((((self.code >> 2u8) & 0x3fff) ^ 0x2000).wrapping_sub(0x2000))
                                as i32)
                                << 2u8) as _,
                        ))],
                        ins: self,
                    };
                }
                if ((self.code >> 21u8) & 0x1f) & 0b11110 == 8 {
                    return SimplifiedIns {
                        mnemonic: "bdnzt",
                        suffix: {
                            {
                                let mut s = String::with_capacity(4);
                                if self.bit(31usize) {
                                    s.push('l');
                                }
                                if self.bit(30usize) {
                                    s.push('a');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1
                                    && ((((((self.code >> 2u8) & 0x3fff) ^ 0x2000)
                                        .wrapping_sub(0x2000))
                                        as i32)
                                        << 2u8)
                                        >= 0
                                {
                                    s.push('+');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1
                                    && ((((((self.code >> 2u8) & 0x3fff) ^ 0x2000)
                                        .wrapping_sub(0x2000))
                                        as i32)
                                        << 2u8)
                                        < 0
                                {
                                    s.push('-');
                                }
                                s
                            }
                        },
                        args: vec![
                            Argument::CRBit(CRBit(((self.code >> 16u8) & 0x1f) as _)),
                            Argument::BranchDest(BranchDest(
                                ((((((self.code >> 2u8) & 0x3fff) ^ 0x2000).wrapping_sub(0x2000))
                                    as i32)
                                    << 2u8) as _,
                            )),
                        ],
                        ins: self,
                    };
                }
                if ((self.code >> 21u8) & 0x1f) & 0b11110 == 0 {
                    return SimplifiedIns {
                        mnemonic: "bdnzf",
                        suffix: {
                            {
                                let mut s = String::with_capacity(4);
                                if self.bit(31usize) {
                                    s.push('l');
                                }
                                if self.bit(30usize) {
                                    s.push('a');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1
                                    && ((((((self.code >> 2u8) & 0x3fff) ^ 0x2000)
                                        .wrapping_sub(0x2000))
                                        as i32)
                                        << 2u8)
                                        >= 0
                                {
                                    s.push('+');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1
                                    && ((((((self.code >> 2u8) & 0x3fff) ^ 0x2000)
                                        .wrapping_sub(0x2000))
                                        as i32)
                                        << 2u8)
                                        < 0
                                {
                                    s.push('-');
                                }
                                s
                            }
                        },
                        args: vec![
                            Argument::CRBit(CRBit(((self.code >> 16u8) & 0x1f) as _)),
                            Argument::BranchDest(BranchDest(
                                ((((((self.code >> 2u8) & 0x3fff) ^ 0x2000).wrapping_sub(0x2000))
                                    as i32)
                                    << 2u8) as _,
                            )),
                        ],
                        ins: self,
                    };
                }
                if ((self.code >> 21u8) & 0x1f) & 0b11110 == 18 && ((self.code >> 16u8) & 0x1f) == 0
                {
                    return SimplifiedIns {
                        mnemonic: "bdz",
                        suffix: {
                            {
                                let mut s = String::with_capacity(4);
                                if self.bit(31usize) {
                                    s.push('l');
                                }
                                if self.bit(30usize) {
                                    s.push('a');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1
                                    && ((((((self.code >> 2u8) & 0x3fff) ^ 0x2000)
                                        .wrapping_sub(0x2000))
                                        as i32)
                                        << 2u8)
                                        >= 0
                                {
                                    s.push('+');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1
                                    && ((((((self.code >> 2u8) & 0x3fff) ^ 0x2000)
                                        .wrapping_sub(0x2000))
                                        as i32)
                                        << 2u8)
                                        < 0
                                {
                                    s.push('-');
                                }
                                s
                            }
                        },
                        args: vec![Argument::BranchDest(BranchDest(
                            ((((((self.code >> 2u8) & 0x3fff) ^ 0x2000).wrapping_sub(0x2000))
                                as i32)
                                << 2u8) as _,
                        ))],
                        ins: self,
                    };
                }
                if ((self.code >> 21u8) & 0x1f) & 0b11110 == 10 {
                    return SimplifiedIns {
                        mnemonic: "bdzt",
                        suffix: {
                            {
                                let mut s = String::with_capacity(4);
                                if self.bit(31usize) {
                                    s.push('l');
                                }
                                if self.bit(30usize) {
                                    s.push('a');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1
                                    && ((((((self.code >> 2u8) & 0x3fff) ^ 0x2000)
                                        .wrapping_sub(0x2000))
                                        as i32)
                                        << 2u8)
                                        >= 0
                                {
                                    s.push('+');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1
                                    && ((((((self.code >> 2u8) & 0x3fff) ^ 0x2000)
                                        .wrapping_sub(0x2000))
                                        as i32)
                                        << 2u8)
                                        < 0
                                {
                                    s.push('-');
                                }
                                s
                            }
                        },
                        args: vec![
                            Argument::CRBit(CRBit(((self.code >> 16u8) & 0x1f) as _)),
                            Argument::BranchDest(BranchDest(
                                ((((((self.code >> 2u8) & 0x3fff) ^ 0x2000).wrapping_sub(0x2000))
                                    as i32)
                                    << 2u8) as _,
                            )),
                        ],
                        ins: self,
                    };
                }
                if ((self.code >> 21u8) & 0x1f) & 0b11110 == 2 {
                    return SimplifiedIns {
                        mnemonic: "bdzf",
                        suffix: {
                            {
                                let mut s = String::with_capacity(4);
                                if self.bit(31usize) {
                                    s.push('l');
                                }
                                if self.bit(30usize) {
                                    s.push('a');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1
                                    && ((((((self.code >> 2u8) & 0x3fff) ^ 0x2000)
                                        .wrapping_sub(0x2000))
                                        as i32)
                                        << 2u8)
                                        >= 0
                                {
                                    s.push('+');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1
                                    && ((((((self.code >> 2u8) & 0x3fff) ^ 0x2000)
                                        .wrapping_sub(0x2000))
                                        as i32)
                                        << 2u8)
                                        < 0
                                {
                                    s.push('-');
                                }
                                s
                            }
                        },
                        args: vec![
                            Argument::CRBit(CRBit(((self.code >> 16u8) & 0x1f) as _)),
                            Argument::BranchDest(BranchDest(
                                ((((((self.code >> 2u8) & 0x3fff) ^ 0x2000).wrapping_sub(0x2000))
                                    as i32)
                                    << 2u8) as _,
                            )),
                        ],
                        ins: self,
                    };
                }
            }
            Opcode::Bcctr => {
                if ((self.code >> 21u8) & 0x1f) == 20 && ((self.code >> 16u8) & 0x1f) == 0 {
                    return SimplifiedIns {
                        mnemonic: "bctr",
                        suffix: {
                            {
                                let mut s = String::with_capacity(4);
                                if self.bit(31usize) {
                                    s.push('l');
                                }
                                s
                            }
                        },
                        args: vec![],
                        ins: self,
                    };
                }
                if ((self.code >> 21u8) & 0x1f) & 0b11110 == 12 && ((self.code >> 16u8) & 0x1f) == 0
                {
                    return SimplifiedIns {
                        mnemonic: "bltctr",
                        suffix: {
                            {
                                let mut s = String::with_capacity(4);
                                if self.bit(31usize) {
                                    s.push('l');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1 {
                                    s.push('+');
                                }
                                s
                            }
                        },
                        args: vec![],
                        ins: self,
                    };
                }
                if ((self.code >> 21u8) & 0x1f) & 0b11110 == 12
                    && ((self.code >> 16u8) & 0x1f) & 0b11 == 0
                {
                    return SimplifiedIns {
                        mnemonic: "bltctr",
                        suffix: {
                            {
                                let mut s = String::with_capacity(4);
                                if self.bit(31usize) {
                                    s.push('l');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1 {
                                    s.push('+');
                                }
                                s
                            }
                        },
                        args: vec![Argument::CRField(CRField(((self.code >> 18u8) & 0x7) as _))],
                        ins: self,
                    };
                }
                if ((self.code >> 21u8) & 0x1f) & 0b11110 == 4 && ((self.code >> 16u8) & 0x1f) == 1
                {
                    return SimplifiedIns {
                        mnemonic: "blectr",
                        suffix: {
                            {
                                let mut s = String::with_capacity(4);
                                if self.bit(31usize) {
                                    s.push('l');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1 {
                                    s.push('+');
                                }
                                s
                            }
                        },
                        args: vec![],
                        ins: self,
                    };
                }
                if ((self.code >> 21u8) & 0x1f) & 0b11110 == 4
                    && ((self.code >> 16u8) & 0x1f) & 0b11 == 1
                {
                    return SimplifiedIns {
                        mnemonic: "blectr",
                        suffix: {
                            {
                                let mut s = String::with_capacity(4);
                                if self.bit(31usize) {
                                    s.push('l');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1 {
                                    s.push('+');
                                }
                                s
                            }
                        },
                        args: vec![Argument::CRField(CRField(((self.code >> 18u8) & 0x7) as _))],
                        ins: self,
                    };
                }
                if ((self.code >> 21u8) & 0x1f) & 0b11110 == 12 && ((self.code >> 16u8) & 0x1f) == 2
                {
                    return SimplifiedIns {
                        mnemonic: "beqctr",
                        suffix: {
                            {
                                let mut s = String::with_capacity(4);
                                if self.bit(31usize) {
                                    s.push('l');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1 {
                                    s.push('+');
                                }
                                s
                            }
                        },
                        args: vec![],
                        ins: self,
                    };
                }
                if ((self.code >> 21u8) & 0x1f) & 0b11110 == 12
                    && ((self.code >> 16u8) & 0x1f) & 0b11 == 2
                {
                    return SimplifiedIns {
                        mnemonic: "beqctr",
                        suffix: {
                            {
                                let mut s = String::with_capacity(4);
                                if self.bit(31usize) {
                                    s.push('l');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1 {
                                    s.push('+');
                                }
                                s
                            }
                        },
                        args: vec![Argument::CRField(CRField(((self.code >> 18u8) & 0x7) as _))],
                        ins: self,
                    };
                }
                if ((self.code >> 21u8) & 0x1f) & 0b11110 == 4 && ((self.code >> 16u8) & 0x1f) == 0
                {
                    return SimplifiedIns {
                        mnemonic: "bgectr",
                        suffix: {
                            {
                                let mut s = String::with_capacity(4);
                                if self.bit(31usize) {
                                    s.push('l');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1 {
                                    s.push('+');
                                }
                                s
                            }
                        },
                        args: vec![],
                        ins: self,
                    };
                }
                if ((self.code >> 21u8) & 0x1f) & 0b11110 == 4
                    && ((self.code >> 16u8) & 0x1f) & 0b11 == 0
                {
                    return SimplifiedIns {
                        mnemonic: "bgectr",
                        suffix: {
                            {
                                let mut s = String::with_capacity(4);
                                if self.bit(31usize) {
                                    s.push('l');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1 {
                                    s.push('+');
                                }
                                s
                            }
                        },
                        args: vec![Argument::CRField(CRField(((self.code >> 18u8) & 0x7) as _))],
                        ins: self,
                    };
                }
                if ((self.code >> 21u8) & 0x1f) & 0b11110 == 12 && ((self.code >> 16u8) & 0x1f) == 1
                {
                    return SimplifiedIns {
                        mnemonic: "bgtctr",
                        suffix: {
                            {
                                let mut s = String::with_capacity(4);
                                if self.bit(31usize) {
                                    s.push('l');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1 {
                                    s.push('+');
                                }
                                s
                            }
                        },
                        args: vec![],
                        ins: self,
                    };
                }
                if ((self.code >> 21u8) & 0x1f) & 0b11110 == 12
                    && ((self.code >> 16u8) & 0x1f) & 0b11 == 1
                {
                    return SimplifiedIns {
                        mnemonic: "bgtctr",
                        suffix: {
                            {
                                let mut s = String::with_capacity(4);
                                if self.bit(31usize) {
                                    s.push('l');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1 {
                                    s.push('+');
                                }
                                s
                            }
                        },
                        args: vec![Argument::CRField(CRField(((self.code >> 18u8) & 0x7) as _))],
                        ins: self,
                    };
                }
                if ((self.code >> 21u8) & 0x1f) & 0b11110 == 4 && ((self.code >> 16u8) & 0x1f) == 2
                {
                    return SimplifiedIns {
                        mnemonic: "bnectr",
                        suffix: {
                            {
                                let mut s = String::with_capacity(4);
                                if self.bit(31usize) {
                                    s.push('l');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1 {
                                    s.push('+');
                                }
                                s
                            }
                        },
                        args: vec![],
                        ins: self,
                    };
                }
                if ((self.code >> 21u8) & 0x1f) & 0b11110 == 4
                    && ((self.code >> 16u8) & 0x1f) & 0b11 == 2
                {
                    return SimplifiedIns {
                        mnemonic: "bnectr",
                        suffix: {
                            {
                                let mut s = String::with_capacity(4);
                                if self.bit(31usize) {
                                    s.push('l');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1 {
                                    s.push('+');
                                }
                                s
                            }
                        },
                        args: vec![Argument::CRField(CRField(((self.code >> 18u8) & 0x7) as _))],
                        ins: self,
                    };
                }
                if ((self.code >> 21u8) & 0x1f) & 0b11110 == 12 && ((self.code >> 16u8) & 0x1f) == 3
                {
                    return SimplifiedIns {
                        mnemonic: "bsoctr",
                        suffix: {
                            {
                                let mut s = String::with_capacity(4);
                                if self.bit(31usize) {
                                    s.push('l');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1 {
                                    s.push('+');
                                }
                                s
                            }
                        },
                        args: vec![],
                        ins: self,
                    };
                }
                if ((self.code >> 21u8) & 0x1f) & 0b11110 == 12
                    && ((self.code >> 16u8) & 0x1f) & 0b11 == 3
                {
                    return SimplifiedIns {
                        mnemonic: "bsoctr",
                        suffix: {
                            {
                                let mut s = String::with_capacity(4);
                                if self.bit(31usize) {
                                    s.push('l');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1 {
                                    s.push('+');
                                }
                                s
                            }
                        },
                        args: vec![Argument::CRField(CRField(((self.code >> 18u8) & 0x7) as _))],
                        ins: self,
                    };
                }
                if ((self.code >> 21u8) & 0x1f) & 0b11110 == 4 && ((self.code >> 16u8) & 0x1f) == 3
                {
                    return SimplifiedIns {
                        mnemonic: "bnsctr",
                        suffix: {
                            {
                                let mut s = String::with_capacity(4);
                                if self.bit(31usize) {
                                    s.push('l');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1 {
                                    s.push('+');
                                }
                                s
                            }
                        },
                        args: vec![],
                        ins: self,
                    };
                }
                if ((self.code >> 21u8) & 0x1f) & 0b11110 == 4
                    && ((self.code >> 16u8) & 0x1f) & 0b11 == 3
                {
                    return SimplifiedIns {
                        mnemonic: "bnsctr",
                        suffix: {
                            {
                                let mut s = String::with_capacity(4);
                                if self.bit(31usize) {
                                    s.push('l');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1 {
                                    s.push('+');
                                }
                                s
                            }
                        },
                        args: vec![Argument::CRField(CRField(((self.code >> 18u8) & 0x7) as _))],
                        ins: self,
                    };
                }
            }
            Opcode::Bclr => {
                if ((self.code >> 21u8) & 0x1f) == 20 && ((self.code >> 16u8) & 0x1f) == 0 {
                    return SimplifiedIns {
                        mnemonic: "blr",
                        suffix: {
                            {
                                let mut s = String::with_capacity(4);
                                if self.bit(31usize) {
                                    s.push('l');
                                }
                                s
                            }
                        },
                        args: vec![],
                        ins: self,
                    };
                }
                if ((self.code >> 21u8) & 0x1f) & 0b11110 == 12 && ((self.code >> 16u8) & 0x1f) == 0
                {
                    return SimplifiedIns {
                        mnemonic: "bltlr",
                        suffix: {
                            {
                                let mut s = String::with_capacity(4);
                                if self.bit(31usize) {
                                    s.push('l');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1 {
                                    s.push('+');
                                }
                                s
                            }
                        },
                        args: vec![],
                        ins: self,
                    };
                }
                if ((self.code >> 21u8) & 0x1f) & 0b11110 == 12
                    && ((self.code >> 16u8) & 0x1f) & 0b11 == 0
                {
                    return SimplifiedIns {
                        mnemonic: "bltlr",
                        suffix: {
                            {
                                let mut s = String::with_capacity(4);
                                if self.bit(31usize) {
                                    s.push('l');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1 {
                                    s.push('+');
                                }
                                s
                            }
                        },
                        args: vec![Argument::CRField(CRField(((self.code >> 18u8) & 0x7) as _))],
                        ins: self,
                    };
                }
                if ((self.code >> 21u8) & 0x1f) & 0b11110 == 4 && ((self.code >> 16u8) & 0x1f) == 1
                {
                    return SimplifiedIns {
                        mnemonic: "blelr",
                        suffix: {
                            {
                                let mut s = String::with_capacity(4);
                                if self.bit(31usize) {
                                    s.push('l');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1 {
                                    s.push('+');
                                }
                                s
                            }
                        },
                        args: vec![],
                        ins: self,
                    };
                }
                if ((self.code >> 21u8) & 0x1f) & 0b11110 == 4
                    && ((self.code >> 16u8) & 0x1f) & 0b11 == 1
                {
                    return SimplifiedIns {
                        mnemonic: "blelr",
                        suffix: {
                            {
                                let mut s = String::with_capacity(4);
                                if self.bit(31usize) {
                                    s.push('l');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1 {
                                    s.push('+');
                                }
                                s
                            }
                        },
                        args: vec![Argument::CRField(CRField(((self.code >> 18u8) & 0x7) as _))],
                        ins: self,
                    };
                }
                if ((self.code >> 21u8) & 0x1f) & 0b11110 == 12 && ((self.code >> 16u8) & 0x1f) == 2
                {
                    return SimplifiedIns {
                        mnemonic: "beqlr",
                        suffix: {
                            {
                                let mut s = String::with_capacity(4);
                                if self.bit(31usize) {
                                    s.push('l');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1 {
                                    s.push('+');
                                }
                                s
                            }
                        },
                        args: vec![],
                        ins: self,
                    };
                }
                if ((self.code >> 21u8) & 0x1f) & 0b11110 == 12
                    && ((self.code >> 16u8) & 0x1f) & 0b11 == 2
                {
                    return SimplifiedIns {
                        mnemonic: "beqlr",
                        suffix: {
                            {
                                let mut s = String::with_capacity(4);
                                if self.bit(31usize) {
                                    s.push('l');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1 {
                                    s.push('+');
                                }
                                s
                            }
                        },
                        args: vec![Argument::CRField(CRField(((self.code >> 18u8) & 0x7) as _))],
                        ins: self,
                    };
                }
                if ((self.code >> 21u8) & 0x1f) & 0b11110 == 4 && ((self.code >> 16u8) & 0x1f) == 0
                {
                    return SimplifiedIns {
                        mnemonic: "bgelr",
                        suffix: {
                            {
                                let mut s = String::with_capacity(4);
                                if self.bit(31usize) {
                                    s.push('l');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1 {
                                    s.push('+');
                                }
                                s
                            }
                        },
                        args: vec![],
                        ins: self,
                    };
                }
                if ((self.code >> 21u8) & 0x1f) & 0b11110 == 4
                    && ((self.code >> 16u8) & 0x1f) & 0b11 == 0
                {
                    return SimplifiedIns {
                        mnemonic: "bgelr",
                        suffix: {
                            {
                                let mut s = String::with_capacity(4);
                                if self.bit(31usize) {
                                    s.push('l');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1 {
                                    s.push('+');
                                }
                                s
                            }
                        },
                        args: vec![Argument::CRField(CRField(((self.code >> 18u8) & 0x7) as _))],
                        ins: self,
                    };
                }
                if ((self.code >> 21u8) & 0x1f) & 0b11110 == 12 && ((self.code >> 16u8) & 0x1f) == 1
                {
                    return SimplifiedIns {
                        mnemonic: "bgtlr",
                        suffix: {
                            {
                                let mut s = String::with_capacity(4);
                                if self.bit(31usize) {
                                    s.push('l');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1 {
                                    s.push('+');
                                }
                                s
                            }
                        },
                        args: vec![],
                        ins: self,
                    };
                }
                if ((self.code >> 21u8) & 0x1f) & 0b11110 == 12
                    && ((self.code >> 16u8) & 0x1f) & 0b11 == 1
                {
                    return SimplifiedIns {
                        mnemonic: "bgtlr",
                        suffix: {
                            {
                                let mut s = String::with_capacity(4);
                                if self.bit(31usize) {
                                    s.push('l');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1 {
                                    s.push('+');
                                }
                                s
                            }
                        },
                        args: vec![Argument::CRField(CRField(((self.code >> 18u8) & 0x7) as _))],
                        ins: self,
                    };
                }
                if ((self.code >> 21u8) & 0x1f) & 0b11110 == 4 && ((self.code >> 16u8) & 0x1f) == 2
                {
                    return SimplifiedIns {
                        mnemonic: "bnelr",
                        suffix: {
                            {
                                let mut s = String::with_capacity(4);
                                if self.bit(31usize) {
                                    s.push('l');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1 {
                                    s.push('+');
                                }
                                s
                            }
                        },
                        args: vec![],
                        ins: self,
                    };
                }
                if ((self.code >> 21u8) & 0x1f) & 0b11110 == 4
                    && ((self.code >> 16u8) & 0x1f) & 0b11 == 2
                {
                    return SimplifiedIns {
                        mnemonic: "bnelr",
                        suffix: {
                            {
                                let mut s = String::with_capacity(4);
                                if self.bit(31usize) {
                                    s.push('l');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1 {
                                    s.push('+');
                                }
                                s
                            }
                        },
                        args: vec![Argument::CRField(CRField(((self.code >> 18u8) & 0x7) as _))],
                        ins: self,
                    };
                }
                if ((self.code >> 21u8) & 0x1f) & 0b11110 == 12 && ((self.code >> 16u8) & 0x1f) == 3
                {
                    return SimplifiedIns {
                        mnemonic: "bsolr",
                        suffix: {
                            {
                                let mut s = String::with_capacity(4);
                                if self.bit(31usize) {
                                    s.push('l');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1 {
                                    s.push('+');
                                }
                                s
                            }
                        },
                        args: vec![],
                        ins: self,
                    };
                }
                if ((self.code >> 21u8) & 0x1f) & 0b11110 == 12
                    && ((self.code >> 16u8) & 0x1f) & 0b11 == 3
                {
                    return SimplifiedIns {
                        mnemonic: "bsolr",
                        suffix: {
                            {
                                let mut s = String::with_capacity(4);
                                if self.bit(31usize) {
                                    s.push('l');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1 {
                                    s.push('+');
                                }
                                s
                            }
                        },
                        args: vec![Argument::CRField(CRField(((self.code >> 18u8) & 0x7) as _))],
                        ins: self,
                    };
                }
                if ((self.code >> 21u8) & 0x1f) & 0b11110 == 4 && ((self.code >> 16u8) & 0x1f) == 3
                {
                    return SimplifiedIns {
                        mnemonic: "bnslr",
                        suffix: {
                            {
                                let mut s = String::with_capacity(4);
                                if self.bit(31usize) {
                                    s.push('l');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1 {
                                    s.push('+');
                                }
                                s
                            }
                        },
                        args: vec![],
                        ins: self,
                    };
                }
                if ((self.code >> 21u8) & 0x1f) & 0b11110 == 4
                    && ((self.code >> 16u8) & 0x1f) & 0b11 == 3
                {
                    return SimplifiedIns {
                        mnemonic: "bnslr",
                        suffix: {
                            {
                                let mut s = String::with_capacity(4);
                                if self.bit(31usize) {
                                    s.push('l');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1 {
                                    s.push('+');
                                }
                                s
                            }
                        },
                        args: vec![Argument::CRField(CRField(((self.code >> 18u8) & 0x7) as _))],
                        ins: self,
                    };
                }
                if ((self.code >> 21u8) & 0x1f) & 0b11110 == 16 && ((self.code >> 16u8) & 0x1f) == 0
                {
                    return SimplifiedIns {
                        mnemonic: "bdnzlr",
                        suffix: {
                            {
                                let mut s = String::with_capacity(4);
                                if self.bit(31usize) {
                                    s.push('l');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1 {
                                    s.push('+');
                                }
                                s
                            }
                        },
                        args: vec![],
                        ins: self,
                    };
                }
                if ((self.code >> 21u8) & 0x1f) & 0b11110 == 8 {
                    return SimplifiedIns {
                        mnemonic: "bdnztlr",
                        suffix: {
                            {
                                let mut s = String::with_capacity(4);
                                if self.bit(31usize) {
                                    s.push('l');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1 {
                                    s.push('+');
                                }
                                s
                            }
                        },
                        args: vec![Argument::CRBit(CRBit(((self.code >> 16u8) & 0x1f) as _))],
                        ins: self,
                    };
                }
                if ((self.code >> 21u8) & 0x1f) & 0b11110 == 0 {
                    return SimplifiedIns {
                        mnemonic: "bdnzflr",
                        suffix: {
                            {
                                let mut s = String::with_capacity(4);
                                if self.bit(31usize) {
                                    s.push('l');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1 {
                                    s.push('+');
                                }
                                s
                            }
                        },
                        args: vec![Argument::CRBit(CRBit(((self.code >> 16u8) & 0x1f) as _))],
                        ins: self,
                    };
                }
                if ((self.code >> 21u8) & 0x1f) & 0b11110 == 18 && ((self.code >> 16u8) & 0x1f) == 0
                {
                    return SimplifiedIns {
                        mnemonic: "bdzlr",
                        suffix: {
                            {
                                let mut s = String::with_capacity(4);
                                if self.bit(31usize) {
                                    s.push('l');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1 {
                                    s.push('+');
                                }
                                s
                            }
                        },
                        args: vec![],
                        ins: self,
                    };
                }
                if ((self.code >> 21u8) & 0x1f) & 0b11110 == 10 {
                    return SimplifiedIns {
                        mnemonic: "bdztlr",
                        suffix: {
                            {
                                let mut s = String::with_capacity(4);
                                if self.bit(31usize) {
                                    s.push('l');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1 {
                                    s.push('+');
                                }
                                s
                            }
                        },
                        args: vec![Argument::CRBit(CRBit(((self.code >> 16u8) & 0x1f) as _))],
                        ins: self,
                    };
                }
                if ((self.code >> 21u8) & 0x1f) & 0b11110 == 0 {
                    return SimplifiedIns {
                        mnemonic: "bdzflr",
                        suffix: {
                            {
                                let mut s = String::with_capacity(4);
                                if self.bit(31usize) {
                                    s.push('l');
                                }
                                if ((self.code >> 21u8) & 0x1f) & 1 == 1 {
                                    s.push('+');
                                }
                                s
                            }
                        },
                        args: vec![Argument::CRBit(CRBit(((self.code >> 16u8) & 0x1f) as _))],
                        ins: self,
                    };
                }
            }
            Opcode::Cmp => {
                if ((self.code >> 23u8) & 0x7) == 0 && ((self.code >> 21u8) & 0x1) == 0 {
                    return SimplifiedIns {
                        mnemonic: "cmpw",
                        suffix: String::new(),
                        args: vec![
                            Argument::GPR(GPR(((self.code >> 16u8) & 0x1f) as _)),
                            Argument::GPR(GPR(((self.code >> 11u8) & 0x1f) as _)),
                        ],
                        ins: self,
                    };
                }
                if ((self.code >> 21u8) & 0x1) == 0 {
                    return SimplifiedIns {
                        mnemonic: "cmpw",
                        suffix: String::new(),
                        args: vec![
                            Argument::CRField(CRField(((self.code >> 23u8) & 0x7) as _)),
                            Argument::GPR(GPR(((self.code >> 16u8) & 0x1f) as _)),
                            Argument::GPR(GPR(((self.code >> 11u8) & 0x1f) as _)),
                        ],
                        ins: self,
                    };
                }
                if ((self.code >> 23u8) & 0x7) == 0 && ((self.code >> 21u8) & 0x1) == 1 {
                    return SimplifiedIns {
                        mnemonic: "cmpd",
                        suffix: String::new(),
                        args: vec![
                            Argument::GPR(GPR(((self.code >> 16u8) & 0x1f) as _)),
                            Argument::GPR(GPR(((self.code >> 11u8) & 0x1f) as _)),
                        ],
                        ins: self,
                    };
                }
                if ((self.code >> 21u8) & 0x1) == 1 {
                    return SimplifiedIns {
                        mnemonic: "cmpd",
                        suffix: String::new(),
                        args: vec![
                            Argument::CRField(CRField(((self.code >> 23u8) & 0x7) as _)),
                            Argument::GPR(GPR(((self.code >> 16u8) & 0x1f) as _)),
                            Argument::GPR(GPR(((self.code >> 11u8) & 0x1f) as _)),
                        ],
                        ins: self,
                    };
                }
            }
            Opcode::Cmpi => {
                if ((self.code >> 23u8) & 0x7) == 0 && ((self.code >> 21u8) & 0x1) == 0 {
                    return SimplifiedIns {
                        mnemonic: "cmpwi",
                        suffix: String::new(),
                        args: vec![
                            Argument::GPR(GPR(((self.code >> 16u8) & 0x1f) as _)),
                            Argument::Simm(Simm(
                                ((((self.code & 0xffff) ^ 0x8000).wrapping_sub(0x8000)) as i32)
                                    as _,
                            )),
                        ],
                        ins: self,
                    };
                }
                if ((self.code >> 21u8) & 0x1) == 0 {
                    return SimplifiedIns {
                        mnemonic: "cmpwi",
                        suffix: String::new(),
                        args: vec![
                            Argument::CRField(CRField(((self.code >> 23u8) & 0x7) as _)),
                            Argument::GPR(GPR(((self.code >> 16u8) & 0x1f) as _)),
                            Argument::Simm(Simm(
                                ((((self.code & 0xffff) ^ 0x8000).wrapping_sub(0x8000)) as i32)
                                    as _,
                            )),
                        ],
                        ins: self,
                    };
                }
                if ((self.code >> 23u8) & 0x7) == 0 && ((self.code >> 21u8) & 0x1) == 1 {
                    return SimplifiedIns {
                        mnemonic: "cmpdi",
                        suffix: String::new(),
                        args: vec![
                            Argument::GPR(GPR(((self.code >> 16u8) & 0x1f) as _)),
                            Argument::Simm(Simm(
                                ((((self.code & 0xffff) ^ 0x8000).wrapping_sub(0x8000)) as i32)
                                    as _,
                            )),
                        ],
                        ins: self,
                    };
                }
                if ((self.code >> 21u8) & 0x1) == 1 {
                    return SimplifiedIns {
                        mnemonic: "cmpdi",
                        suffix: String::new(),
                        args: vec![
                            Argument::CRField(CRField(((self.code >> 23u8) & 0x7) as _)),
                            Argument::GPR(GPR(((self.code >> 16u8) & 0x1f) as _)),
                            Argument::Simm(Simm(
                                ((((self.code & 0xffff) ^ 0x8000).wrapping_sub(0x8000)) as i32)
                                    as _,
                            )),
                        ],
                        ins: self,
                    };
                }
            }
            Opcode::Cmpl => {
                if ((self.code >> 23u8) & 0x7) == 0 && ((self.code >> 21u8) & 0x1) == 0 {
                    return SimplifiedIns {
                        mnemonic: "cmplw",
                        suffix: String::new(),
                        args: vec![
                            Argument::GPR(GPR(((self.code >> 16u8) & 0x1f) as _)),
                            Argument::GPR(GPR(((self.code >> 11u8) & 0x1f) as _)),
                        ],
                        ins: self,
                    };
                }
                if ((self.code >> 21u8) & 0x1) == 0 {
                    return SimplifiedIns {
                        mnemonic: "cmplw",
                        suffix: String::new(),
                        args: vec![
                            Argument::CRField(CRField(((self.code >> 23u8) & 0x7) as _)),
                            Argument::GPR(GPR(((self.code >> 16u8) & 0x1f) as _)),
                            Argument::GPR(GPR(((self.code >> 11u8) & 0x1f) as _)),
                        ],
                        ins: self,
                    };
                }
                if ((self.code >> 23u8) & 0x7) == 0 && ((self.code >> 21u8) & 0x1) == 1 {
                    return SimplifiedIns {
                        mnemonic: "cmpld",
                        suffix: String::new(),
                        args: vec![
                            Argument::GPR(GPR(((self.code >> 16u8) & 0x1f) as _)),
                            Argument::GPR(GPR(((self.code >> 11u8) & 0x1f) as _)),
                        ],
                        ins: self,
                    };
                }
                if ((self.code >> 21u8) & 0x1) == 1 {
                    return SimplifiedIns {
                        mnemonic: "cmpld",
                        suffix: String::new(),
                        args: vec![
                            Argument::CRField(CRField(((self.code >> 23u8) & 0x7) as _)),
                            Argument::GPR(GPR(((self.code >> 16u8) & 0x1f) as _)),
                            Argument::GPR(GPR(((self.code >> 11u8) & 0x1f) as _)),
                        ],
                        ins: self,
                    };
                }
            }
            Opcode::Cmpli => {
                if ((self.code >> 23u8) & 0x7) == 0 && ((self.code >> 21u8) & 0x1) == 0 {
                    return SimplifiedIns {
                        mnemonic: "cmplwi",
                        suffix: String::new(),
                        args: vec![
                            Argument::GPR(GPR(((self.code >> 16u8) & 0x1f) as _)),
                            Argument::Uimm(Uimm((self.code & 0xffff) as _)),
                        ],
                        ins: self,
                    };
                }
                if ((self.code >> 21u8) & 0x1) == 0 {
                    return SimplifiedIns {
                        mnemonic: "cmplwi",
                        suffix: String::new(),
                        args: vec![
                            Argument::CRField(CRField(((self.code >> 23u8) & 0x7) as _)),
                            Argument::GPR(GPR(((self.code >> 16u8) & 0x1f) as _)),
                            Argument::Uimm(Uimm((self.code & 0xffff) as _)),
                        ],
                        ins: self,
                    };
                }
                if ((self.code >> 23u8) & 0x7) == 0 && ((self.code >> 21u8) & 0x1) == 1 {
                    return SimplifiedIns {
                        mnemonic: "cmpldi",
                        suffix: String::new(),
                        args: vec![
                            Argument::GPR(GPR(((self.code >> 16u8) & 0x1f) as _)),
                            Argument::Uimm(Uimm((self.code & 0xffff) as _)),
                        ],
                        ins: self,
                    };
                }
                if ((self.code >> 21u8) & 0x1) == 1 {
                    return SimplifiedIns {
                        mnemonic: "cmpldi",
                        suffix: String::new(),
                        args: vec![
                            Argument::CRField(CRField(((self.code >> 23u8) & 0x7) as _)),
                            Argument::GPR(GPR(((self.code >> 16u8) & 0x1f) as _)),
                            Argument::Uimm(Uimm((self.code & 0xffff) as _)),
                        ],
                        ins: self,
                    };
                }
            }
            Opcode::Creqv => {
                if ((self.code >> 21u8) & 0x1f) == ((self.code >> 16u8) & 0x1f)
                    && ((self.code >> 21u8) & 0x1f) == ((self.code >> 11u8) & 0x1f)
                {
                    return SimplifiedIns {
                        mnemonic: "crset",
                        suffix: String::new(),
                        args: vec![Argument::CRBit(CRBit(((self.code >> 21u8) & 0x1f) as _))],
                        ins: self,
                    };
                }
            }
            Opcode::Crnor => {
                if ((self.code >> 16u8) & 0x1f) == ((self.code >> 11u8) & 0x1f) {
                    return SimplifiedIns {
                        mnemonic: "crnot",
                        suffix: String::new(),
                        args: vec![
                            Argument::CRBit(CRBit(((self.code >> 21u8) & 0x1f) as _)),
                            Argument::CRBit(CRBit(((self.code >> 16u8) & 0x1f) as _)),
                        ],
                        ins: self,
                    };
                }
            }
            Opcode::Cror => {
                if ((self.code >> 16u8) & 0x1f) == ((self.code >> 11u8) & 0x1f) {
                    return SimplifiedIns {
                        mnemonic: "crmove",
                        suffix: String::new(),
                        args: vec![
                            Argument::CRBit(CRBit(((self.code >> 21u8) & 0x1f) as _)),
                            Argument::CRBit(CRBit(((self.code >> 16u8) & 0x1f) as _)),
                        ],
                        ins: self,
                    };
                }
            }
            Opcode::Crxor => {
                if ((self.code >> 21u8) & 0x1f) == ((self.code >> 16u8) & 0x1f)
                    && ((self.code >> 21u8) & 0x1f) == ((self.code >> 11u8) & 0x1f)
                {
                    return SimplifiedIns {
                        mnemonic: "crclr",
                        suffix: String::new(),
                        args: vec![Argument::CRBit(CRBit(((self.code >> 21u8) & 0x1f) as _))],
                        ins: self,
                    };
                }
            }
            Opcode::Mfspr => {
                if (((((self.code >> 11u8) & 0x3ff) & 0b11111_00000u32) >> 5u32)
                    | ((((self.code >> 11u8) & 0x3ff) & 0b00000_11111u32) << 5u32))
                    as u32
                    == 1
                {
                    return SimplifiedIns {
                        mnemonic: "mfxer",
                        suffix: String::new(),
                        args: vec![Argument::GPR(GPR(((self.code >> 21u8) & 0x1f) as _))],
                        ins: self,
                    };
                }
                if (((((self.code >> 11u8) & 0x3ff) & 0b11111_00000u32) >> 5u32)
                    | ((((self.code >> 11u8) & 0x3ff) & 0b00000_11111u32) << 5u32))
                    as u32
                    == 8
                {
                    return SimplifiedIns {
                        mnemonic: "mflr",
                        suffix: String::new(),
                        args: vec![Argument::GPR(GPR(((self.code >> 21u8) & 0x1f) as _))],
                        ins: self,
                    };
                }
                if (((((self.code >> 11u8) & 0x3ff) & 0b11111_00000u32) >> 5u32)
                    | ((((self.code >> 11u8) & 0x3ff) & 0b00000_11111u32) << 5u32))
                    as u32
                    == 9
                {
                    return SimplifiedIns {
                        mnemonic: "mfctr",
                        suffix: String::new(),
                        args: vec![Argument::GPR(GPR(((self.code >> 21u8) & 0x1f) as _))],
                        ins: self,
                    };
                }
                if (((((self.code >> 11u8) & 0x3ff) & 0b11111_00000u32) >> 5u32)
                    | ((((self.code >> 11u8) & 0x3ff) & 0b00000_11111u32) << 5u32))
                    as u32
                    == 18
                {
                    return SimplifiedIns {
                        mnemonic: "mfdsisr",
                        suffix: String::new(),
                        args: vec![Argument::GPR(GPR(((self.code >> 21u8) & 0x1f) as _))],
                        ins: self,
                    };
                }
                if (((((self.code >> 11u8) & 0x3ff) & 0b11111_00000u32) >> 5u32)
                    | ((((self.code >> 11u8) & 0x3ff) & 0b00000_11111u32) << 5u32))
                    as u32
                    == 19
                {
                    return SimplifiedIns {
                        mnemonic: "mfdar",
                        suffix: String::new(),
                        args: vec![Argument::GPR(GPR(((self.code >> 21u8) & 0x1f) as _))],
                        ins: self,
                    };
                }
                if (((((self.code >> 11u8) & 0x3ff) & 0b11111_00000u32) >> 5u32)
                    | ((((self.code >> 11u8) & 0x3ff) & 0b00000_11111u32) << 5u32))
                    as u32
                    == 22
                {
                    return SimplifiedIns {
                        mnemonic: "mfdec",
                        suffix: String::new(),
                        args: vec![Argument::GPR(GPR(((self.code >> 21u8) & 0x1f) as _))],
                        ins: self,
                    };
                }
                if (((((self.code >> 11u8) & 0x3ff) & 0b11111_00000u32) >> 5u32)
                    | ((((self.code >> 11u8) & 0x3ff) & 0b00000_11111u32) << 5u32))
                    as u32
                    == 25
                {
                    return SimplifiedIns {
                        mnemonic: "mfsdr1",
                        suffix: String::new(),
                        args: vec![Argument::GPR(GPR(((self.code >> 21u8) & 0x1f) as _))],
                        ins: self,
                    };
                }
                if (((((self.code >> 11u8) & 0x3ff) & 0b11111_00000u32) >> 5u32)
                    | ((((self.code >> 11u8) & 0x3ff) & 0b00000_11111u32) << 5u32))
                    as u32
                    == 26
                {
                    return SimplifiedIns {
                        mnemonic: "mfsrr0",
                        suffix: String::new(),
                        args: vec![Argument::GPR(GPR(((self.code >> 21u8) & 0x1f) as _))],
                        ins: self,
                    };
                }
                if (((((self.code >> 11u8) & 0x3ff) & 0b11111_00000u32) >> 5u32)
                    | ((((self.code >> 11u8) & 0x3ff) & 0b00000_11111u32) << 5u32))
                    as u32
                    == 27
                {
                    return SimplifiedIns {
                        mnemonic: "mfsrr1",
                        suffix: String::new(),
                        args: vec![Argument::GPR(GPR(((self.code >> 21u8) & 0x1f) as _))],
                        ins: self,
                    };
                }
                if (((((self.code >> 11u8) & 0x3ff) & 0b11111_00000u32) >> 5u32)
                    | ((((self.code >> 11u8) & 0x3ff) & 0b00000_11111u32) << 5u32))
                    as u32
                    & 0b1111111100
                    == 272
                {
                    return SimplifiedIns {
                        mnemonic: "mfsprg",
                        suffix: String::new(),
                        args: vec![
                            Argument::GPR(GPR(((self.code >> 21u8) & 0x1f) as _)),
                            Argument::OpaqueU(OpaqueU(((self.code >> 16u8) & 0x3) as _)),
                        ],
                        ins: self,
                    };
                }
                if (((((self.code >> 11u8) & 0x3ff) & 0b11111_00000u32) >> 5u32)
                    | ((((self.code >> 11u8) & 0x3ff) & 0b00000_11111u32) << 5u32))
                    as u32
                    == 282
                {
                    return SimplifiedIns {
                        mnemonic: "mfear",
                        suffix: String::new(),
                        args: vec![Argument::GPR(GPR(((self.code >> 21u8) & 0x1f) as _))],
                        ins: self,
                    };
                }
                if (((((self.code >> 11u8) & 0x3ff) & 0b11111_00000u32) >> 5u32)
                    | ((((self.code >> 11u8) & 0x3ff) & 0b00000_11111u32) << 5u32))
                    as u32
                    & 0b1111111001
                    == 528
                {
                    return SimplifiedIns {
                        mnemonic: "mfibatu",
                        suffix: String::new(),
                        args: vec![
                            Argument::GPR(GPR(((self.code >> 21u8) & 0x1f) as _)),
                            Argument::OpaqueU(OpaqueU(((self.code >> 17u8) & 0x3) as _)),
                        ],
                        ins: self,
                    };
                }
                if (((((self.code >> 11u8) & 0x3ff) & 0b11111_00000u32) >> 5u32)
                    | ((((self.code >> 11u8) & 0x3ff) & 0b00000_11111u32) << 5u32))
                    as u32
                    & 0b1111111001
                    == 529
                {
                    return SimplifiedIns {
                        mnemonic: "mfibatl",
                        suffix: String::new(),
                        args: vec![
                            Argument::GPR(GPR(((self.code >> 21u8) & 0x1f) as _)),
                            Argument::OpaqueU(OpaqueU(((self.code >> 17u8) & 0x3) as _)),
                        ],
                        ins: self,
                    };
                }
                if (((((self.code >> 11u8) & 0x3ff) & 0b11111_00000u32) >> 5u32)
                    | ((((self.code >> 11u8) & 0x3ff) & 0b00000_11111u32) << 5u32))
                    as u32
                    & 0b1111111001
                    == 536
                {
                    return SimplifiedIns {
                        mnemonic: "mfdbatu",
                        suffix: String::new(),
                        args: vec![
                            Argument::GPR(GPR(((self.code >> 21u8) & 0x1f) as _)),
                            Argument::OpaqueU(OpaqueU(((self.code >> 17u8) & 0x3) as _)),
                        ],
                        ins: self,
                    };
                }
                if (((((self.code >> 11u8) & 0x3ff) & 0b11111_00000u32) >> 5u32)
                    | ((((self.code >> 11u8) & 0x3ff) & 0b00000_11111u32) << 5u32))
                    as u32
                    & 0b1111111001
                    == 537
                {
                    return SimplifiedIns {
                        mnemonic: "mfdbatl",
                        suffix: String::new(),
                        args: vec![
                            Argument::GPR(GPR(((self.code >> 21u8) & 0x1f) as _)),
                            Argument::OpaqueU(OpaqueU(((self.code >> 17u8) & 0x3) as _)),
                        ],
                        ins: self,
                    };
                }
            }
            Opcode::Mtspr => {
                if (((((self.code >> 11u8) & 0x3ff) & 0b11111_00000u32) >> 5u32)
                    | ((((self.code >> 11u8) & 0x3ff) & 0b00000_11111u32) << 5u32))
                    as u32
                    == 1
                {
                    return SimplifiedIns {
                        mnemonic: "mtxer",
                        suffix: String::new(),
                        args: vec![Argument::GPR(GPR(((self.code >> 21u8) & 0x1f) as _))],
                        ins: self,
                    };
                }
                if (((((self.code >> 11u8) & 0x3ff) & 0b11111_00000u32) >> 5u32)
                    | ((((self.code >> 11u8) & 0x3ff) & 0b00000_11111u32) << 5u32))
                    as u32
                    == 8
                {
                    return SimplifiedIns {
                        mnemonic: "mtlr",
                        suffix: String::new(),
                        args: vec![Argument::GPR(GPR(((self.code >> 21u8) & 0x1f) as _))],
                        ins: self,
                    };
                }
                if (((((self.code >> 11u8) & 0x3ff) & 0b11111_00000u32) >> 5u32)
                    | ((((self.code >> 11u8) & 0x3ff) & 0b00000_11111u32) << 5u32))
                    as u32
                    == 9
                {
                    return SimplifiedIns {
                        mnemonic: "mtctr",
                        suffix: String::new(),
                        args: vec![Argument::GPR(GPR(((self.code >> 21u8) & 0x1f) as _))],
                        ins: self,
                    };
                }
                if (((((self.code >> 11u8) & 0x3ff) & 0b11111_00000u32) >> 5u32)
                    | ((((self.code >> 11u8) & 0x3ff) & 0b00000_11111u32) << 5u32))
                    as u32
                    == 18
                {
                    return SimplifiedIns {
                        mnemonic: "mtdsisr",
                        suffix: String::new(),
                        args: vec![Argument::GPR(GPR(((self.code >> 21u8) & 0x1f) as _))],
                        ins: self,
                    };
                }
                if (((((self.code >> 11u8) & 0x3ff) & 0b11111_00000u32) >> 5u32)
                    | ((((self.code >> 11u8) & 0x3ff) & 0b00000_11111u32) << 5u32))
                    as u32
                    == 19
                {
                    return SimplifiedIns {
                        mnemonic: "mtdar",
                        suffix: String::new(),
                        args: vec![Argument::GPR(GPR(((self.code >> 21u8) & 0x1f) as _))],
                        ins: self,
                    };
                }
                if (((((self.code >> 11u8) & 0x3ff) & 0b11111_00000u32) >> 5u32)
                    | ((((self.code >> 11u8) & 0x3ff) & 0b00000_11111u32) << 5u32))
                    as u32
                    == 22
                {
                    return SimplifiedIns {
                        mnemonic: "mtdec",
                        suffix: String::new(),
                        args: vec![Argument::GPR(GPR(((self.code >> 21u8) & 0x1f) as _))],
                        ins: self,
                    };
                }
                if (((((self.code >> 11u8) & 0x3ff) & 0b11111_00000u32) >> 5u32)
                    | ((((self.code >> 11u8) & 0x3ff) & 0b00000_11111u32) << 5u32))
                    as u32
                    == 25
                {
                    return SimplifiedIns {
                        mnemonic: "mtsdr1",
                        suffix: String::new(),
                        args: vec![Argument::GPR(GPR(((self.code >> 21u8) & 0x1f) as _))],
                        ins: self,
                    };
                }
                if (((((self.code >> 11u8) & 0x3ff) & 0b11111_00000u32) >> 5u32)
                    | ((((self.code >> 11u8) & 0x3ff) & 0b00000_11111u32) << 5u32))
                    as u32
                    == 26
                {
                    return SimplifiedIns {
                        mnemonic: "mtsrr0",
                        suffix: String::new(),
                        args: vec![Argument::GPR(GPR(((self.code >> 21u8) & 0x1f) as _))],
                        ins: self,
                    };
                }
                if (((((self.code >> 11u8) & 0x3ff) & 0b11111_00000u32) >> 5u32)
                    | ((((self.code >> 11u8) & 0x3ff) & 0b00000_11111u32) << 5u32))
                    as u32
                    == 27
                {
                    return SimplifiedIns {
                        mnemonic: "mtsrr1",
                        suffix: String::new(),
                        args: vec![Argument::GPR(GPR(((self.code >> 21u8) & 0x1f) as _))],
                        ins: self,
                    };
                }
                if (((((self.code >> 11u8) & 0x3ff) & 0b11111_00000u32) >> 5u32)
                    | ((((self.code >> 11u8) & 0x3ff) & 0b00000_11111u32) << 5u32))
                    as u32
                    & 0b1111111100
                    == 272
                {
                    return SimplifiedIns {
                        mnemonic: "mtsprg",
                        suffix: String::new(),
                        args: vec![
                            Argument::OpaqueU(OpaqueU(((self.code >> 16u8) & 0x3) as _)),
                            Argument::GPR(GPR(((self.code >> 21u8) & 0x1f) as _)),
                        ],
                        ins: self,
                    };
                }
                if (((((self.code >> 11u8) & 0x3ff) & 0b11111_00000u32) >> 5u32)
                    | ((((self.code >> 11u8) & 0x3ff) & 0b00000_11111u32) << 5u32))
                    as u32
                    == 282
                {
                    return SimplifiedIns {
                        mnemonic: "mtear",
                        suffix: String::new(),
                        args: vec![Argument::GPR(GPR(((self.code >> 21u8) & 0x1f) as _))],
                        ins: self,
                    };
                }
                if (((((self.code >> 11u8) & 0x3ff) & 0b11111_00000u32) >> 5u32)
                    | ((((self.code >> 11u8) & 0x3ff) & 0b00000_11111u32) << 5u32))
                    as u32
                    == 284
                {
                    return SimplifiedIns {
                        mnemonic: "mttbl",
                        suffix: String::new(),
                        args: vec![Argument::GPR(GPR(((self.code >> 21u8) & 0x1f) as _))],
                        ins: self,
                    };
                }
                if (((((self.code >> 11u8) & 0x3ff) & 0b11111_00000u32) >> 5u32)
                    | ((((self.code >> 11u8) & 0x3ff) & 0b00000_11111u32) << 5u32))
                    as u32
                    == 285
                {
                    return SimplifiedIns {
                        mnemonic: "mttbu",
                        suffix: String::new(),
                        args: vec![Argument::GPR(GPR(((self.code >> 21u8) & 0x1f) as _))],
                        ins: self,
                    };
                }
                if (((((self.code >> 11u8) & 0x3ff) & 0b11111_00000u32) >> 5u32)
                    | ((((self.code >> 11u8) & 0x3ff) & 0b00000_11111u32) << 5u32))
                    as u32
                    & 0b1111111001
                    == 528
                {
                    return SimplifiedIns {
                        mnemonic: "mtibatu",
                        suffix: String::new(),
                        args: vec![
                            Argument::OpaqueU(OpaqueU(((self.code >> 17u8) & 0x3) as _)),
                            Argument::GPR(GPR(((self.code >> 21u8) & 0x1f) as _)),
                        ],
                        ins: self,
                    };
                }
                if (((((self.code >> 11u8) & 0x3ff) & 0b11111_00000u32) >> 5u32)
                    | ((((self.code >> 11u8) & 0x3ff) & 0b00000_11111u32) << 5u32))
                    as u32
                    & 0b1111111001
                    == 529
                {
                    return SimplifiedIns {
                        mnemonic: "mtibatl",
                        suffix: String::new(),
                        args: vec![
                            Argument::OpaqueU(OpaqueU(((self.code >> 17u8) & 0x3) as _)),
                            Argument::GPR(GPR(((self.code >> 21u8) & 0x1f) as _)),
                        ],
                        ins: self,
                    };
                }
                if (((((self.code >> 11u8) & 0x3ff) & 0b11111_00000u32) >> 5u32)
                    | ((((self.code >> 11u8) & 0x3ff) & 0b00000_11111u32) << 5u32))
                    as u32
                    & 0b1111111001
                    == 536
                {
                    return SimplifiedIns {
                        mnemonic: "mtdbatu",
                        suffix: String::new(),
                        args: vec![
                            Argument::OpaqueU(OpaqueU(((self.code >> 17u8) & 0x3) as _)),
                            Argument::GPR(GPR(((self.code >> 21u8) & 0x1f) as _)),
                        ],
                        ins: self,
                    };
                }
                if (((((self.code >> 11u8) & 0x3ff) & 0b11111_00000u32) >> 5u32)
                    | ((((self.code >> 11u8) & 0x3ff) & 0b00000_11111u32) << 5u32))
                    as u32
                    & 0b1111111001
                    == 537
                {
                    return SimplifiedIns {
                        mnemonic: "mtdbatl",
                        suffix: String::new(),
                        args: vec![
                            Argument::OpaqueU(OpaqueU(((self.code >> 17u8) & 0x3) as _)),
                            Argument::GPR(GPR(((self.code >> 21u8) & 0x1f) as _)),
                        ],
                        ins: self,
                    };
                }
            }
            Opcode::Or => {
                if ((self.code >> 21u8) & 0x1f) == ((self.code >> 11u8) & 0x1f) {
                    return SimplifiedIns {
                        mnemonic: "mr",
                        suffix: {
                            {
                                let mut s = String::with_capacity(4);
                                if self.bit(31usize) {
                                    s.push('.');
                                }
                                s
                            }
                        },
                        args: vec![
                            Argument::GPR(GPR(((self.code >> 16u8) & 0x1f) as _)),
                            Argument::GPR(GPR(((self.code >> 21u8) & 0x1f) as _)),
                        ],
                        ins: self,
                    };
                }
            }
            Opcode::Ori => {
                if ((self.code >> 16u8) & 0x1f) == 0
                    && ((self.code >> 21u8) & 0x1f) == 0
                    && (self.code & 0xffff) == 0
                {
                    return SimplifiedIns {
                        mnemonic: "nop",
                        suffix: String::new(),
                        args: vec![],
                        ins: self,
                    };
                }
            }
            Opcode::Rlwinm => {
                if ((self.code >> 11u8) & 0x1f) == 0
                    && ((self.code >> 6u8) & 0x1f) == 0
                    && ((self.code >> 1u8) & 0x1f) < 32
                {
                    return SimplifiedIns {
                        mnemonic: "clrrwi",
                        suffix: {
                            {
                                let mut s = String::with_capacity(4);
                                if self.bit(31usize) {
                                    s.push('.');
                                }
                                s
                            }
                        },
                        args: vec![
                            Argument::GPR(GPR(((self.code >> 16u8) & 0x1f) as _)),
                            Argument::GPR(GPR(((self.code >> 21u8) & 0x1f) as _)),
                            Argument::OpaqueU(OpaqueU((31 - ((self.code >> 1u8) & 0x1f)) as _)),
                        ],
                        ins: self,
                    };
                }
                if ((self.code >> 11u8) & 0x1f) == 0 && ((self.code >> 1u8) & 0x1f) == 31 {
                    return SimplifiedIns {
                        mnemonic: "clrlwi",
                        suffix: {
                            {
                                let mut s = String::with_capacity(4);
                                if self.bit(31usize) {
                                    s.push('.');
                                }
                                s
                            }
                        },
                        args: vec![
                            Argument::GPR(GPR(((self.code >> 16u8) & 0x1f) as _)),
                            Argument::GPR(GPR(((self.code >> 21u8) & 0x1f) as _)),
                            Argument::OpaqueU(OpaqueU(((self.code >> 6u8) & 0x1f) as _)),
                        ],
                        ins: self,
                    };
                }
                if ((self.code >> 6u8) & 0x1f) == 0
                    && ((self.code >> 1u8) & 0x1f) == 31
                    && ((self.code >> 11u8) & 0x1f) <= 16
                {
                    return SimplifiedIns {
                        mnemonic: "rotlwi",
                        suffix: {
                            {
                                let mut s = String::with_capacity(4);
                                if self.bit(31usize) {
                                    s.push('.');
                                }
                                s
                            }
                        },
                        args: vec![
                            Argument::GPR(GPR(((self.code >> 16u8) & 0x1f) as _)),
                            Argument::GPR(GPR(((self.code >> 21u8) & 0x1f) as _)),
                            Argument::OpaqueU(OpaqueU(((self.code >> 11u8) & 0x1f) as _)),
                        ],
                        ins: self,
                    };
                }
                if ((self.code >> 6u8) & 0x1f) == 0
                    && ((self.code >> 1u8) & 0x1f) == 31
                    && ((self.code >> 11u8) & 0x1f) > 16
                {
                    return SimplifiedIns {
                        mnemonic: "rotrwi",
                        suffix: {
                            {
                                let mut s = String::with_capacity(4);
                                if self.bit(31usize) {
                                    s.push('.');
                                }
                                s
                            }
                        },
                        args: vec![
                            Argument::GPR(GPR(((self.code >> 16u8) & 0x1f) as _)),
                            Argument::GPR(GPR(((self.code >> 21u8) & 0x1f) as _)),
                            Argument::OpaqueU(OpaqueU((32 - ((self.code >> 11u8) & 0x1f)) as _)),
                        ],
                        ins: self,
                    };
                }
                if ((self.code >> 6u8) & 0x1f) == 0
                    && 31 - ((self.code >> 11u8) & 0x1f) == ((self.code >> 1u8) & 0x1f)
                {
                    return SimplifiedIns {
                        mnemonic: "slwi",
                        suffix: {
                            {
                                let mut s = String::with_capacity(4);
                                if self.bit(31usize) {
                                    s.push('.');
                                }
                                s
                            }
                        },
                        args: vec![
                            Argument::GPR(GPR(((self.code >> 16u8) & 0x1f) as _)),
                            Argument::GPR(GPR(((self.code >> 21u8) & 0x1f) as _)),
                            Argument::OpaqueU(OpaqueU(((self.code >> 11u8) & 0x1f) as _)),
                        ],
                        ins: self,
                    };
                }
                if ((self.code >> 1u8) & 0x1f) == 31
                    && 32 - ((self.code >> 6u8) & 0x1f) == ((self.code >> 11u8) & 0x1f)
                {
                    return SimplifiedIns {
                        mnemonic: "srwi",
                        suffix: {
                            {
                                let mut s = String::with_capacity(4);
                                if self.bit(31usize) {
                                    s.push('.');
                                }
                                s
                            }
                        },
                        args: vec![
                            Argument::GPR(GPR(((self.code >> 16u8) & 0x1f) as _)),
                            Argument::GPR(GPR(((self.code >> 21u8) & 0x1f) as _)),
                            Argument::OpaqueU(OpaqueU(((self.code >> 6u8) & 0x1f) as _)),
                        ],
                        ins: self,
                    };
                }
                if ((self.code >> 11u8) & 0x1f) < 32
                    && ((self.code >> 1u8) & 0x1f) == 31 - ((self.code >> 11u8) & 0x1f)
                {
                    return SimplifiedIns {
                        mnemonic: "clrlslwi",
                        suffix: {
                            {
                                let mut s = String::with_capacity(4);
                                if self.bit(31usize) {
                                    s.push('.');
                                }
                                s
                            }
                        },
                        args: vec![
                            Argument::GPR(GPR(((self.code >> 16u8) & 0x1f) as _)),
                            Argument::GPR(GPR(((self.code >> 21u8) & 0x1f) as _)),
                            Argument::OpaqueU(OpaqueU(
                                (((self.code >> 6u8) & 0x1f) + ((self.code >> 11u8) & 0x1f)) as _,
                            )),
                            Argument::OpaqueU(OpaqueU(((self.code >> 11u8) & 0x1f) as _)),
                        ],
                        ins: self,
                    };
                }
                if ((self.code >> 6u8) & 0x1f) == 0 {
                    return SimplifiedIns {
                        mnemonic: "extlwi",
                        suffix: {
                            {
                                let mut s = String::with_capacity(4);
                                if self.bit(31usize) {
                                    s.push('.');
                                }
                                s
                            }
                        },
                        args: vec![
                            Argument::GPR(GPR(((self.code >> 16u8) & 0x1f) as _)),
                            Argument::GPR(GPR(((self.code >> 21u8) & 0x1f) as _)),
                            Argument::OpaqueU(OpaqueU((((self.code >> 1u8) & 0x1f) + 1) as _)),
                            Argument::OpaqueU(OpaqueU(((self.code >> 11u8) & 0x1f) as _)),
                        ],
                        ins: self,
                    };
                }
                if ((self.code >> 1u8) & 0x1f) == 31
                    && ((self.code >> 11u8) & 0x1f) >= 32 - ((self.code >> 6u8) & 0x1f)
                {
                    return SimplifiedIns {
                        mnemonic: "extrwi",
                        suffix: {
                            {
                                let mut s = String::with_capacity(4);
                                if self.bit(31usize) {
                                    s.push('.');
                                }
                                s
                            }
                        },
                        args: vec![
                            Argument::GPR(GPR(((self.code >> 16u8) & 0x1f) as _)),
                            Argument::GPR(GPR(((self.code >> 21u8) & 0x1f) as _)),
                            Argument::OpaqueU(OpaqueU((32 - ((self.code >> 6u8) & 0x1f)) as _)),
                            Argument::OpaqueU(OpaqueU(
                                (((self.code >> 11u8) & 0x1f) - (32 - ((self.code >> 6u8) & 0x1f)))
                                    as _,
                            )),
                        ],
                        ins: self,
                    };
                }
            }
            Opcode::Rlwnm => {
                if ((self.code >> 6u8) & 0x1f) == 0 && ((self.code >> 1u8) & 0x1f) == 31 {
                    return SimplifiedIns {
                        mnemonic: "rotlw",
                        suffix: {
                            {
                                let mut s = String::with_capacity(4);
                                if self.bit(31usize) {
                                    s.push('.');
                                }
                                s
                            }
                        },
                        args: vec![
                            Argument::GPR(GPR(((self.code >> 16u8) & 0x1f) as _)),
                            Argument::GPR(GPR(((self.code >> 21u8) & 0x1f) as _)),
                            Argument::GPR(GPR(((self.code >> 11u8) & 0x1f) as _)),
                        ],
                        ins: self,
                    };
                }
            }
            Opcode::Tw => {
                if ((self.code >> 21u8) & 0x1f) == 4 {
                    return SimplifiedIns {
                        mnemonic: "tweq",
                        suffix: String::new(),
                        args: vec![
                            Argument::GPR(GPR(((self.code >> 16u8) & 0x1f) as _)),
                            Argument::GPR(GPR(((self.code >> 11u8) & 0x1f) as _)),
                        ],
                        ins: self,
                    };
                }
                if ((self.code >> 21u8) & 0x1f) == 5 {
                    return SimplifiedIns {
                        mnemonic: "twlge",
                        suffix: String::new(),
                        args: vec![
                            Argument::GPR(GPR(((self.code >> 16u8) & 0x1f) as _)),
                            Argument::GPR(GPR(((self.code >> 11u8) & 0x1f) as _)),
                        ],
                        ins: self,
                    };
                }
                if ((self.code >> 21u8) & 0x1f) == 31
                    && ((self.code >> 16u8) & 0x1f) == 0
                    && ((self.code >> 11u8) & 0x1f) == 0
                {
                    return SimplifiedIns {
                        mnemonic: "trap",
                        suffix: String::new(),
                        args: vec![],
                        ins: self,
                    };
                }
            }
            Opcode::Twi => {
                if ((self.code >> 21u8) & 0x1f) == 8 {
                    return SimplifiedIns {
                        mnemonic: "twgti",
                        suffix: String::new(),
                        args: vec![
                            Argument::GPR(GPR(((self.code >> 16u8) & 0x1f) as _)),
                            Argument::Simm(Simm(
                                ((((self.code & 0xffff) ^ 0x8000).wrapping_sub(0x8000)) as i32)
                                    as _,
                            )),
                        ],
                        ins: self,
                    };
                }
                if ((self.code >> 21u8) & 0x1f) == 6 {
                    return SimplifiedIns {
                        mnemonic: "twllei",
                        suffix: String::new(),
                        args: vec![
                            Argument::GPR(GPR(((self.code >> 16u8) & 0x1f) as _)),
                            Argument::Simm(Simm(
                                ((((self.code & 0xffff) ^ 0x8000).wrapping_sub(0x8000)) as i32)
                                    as _,
                            )),
                        ],
                        ins: self,
                    };
                }
                if ((self.code >> 21u8) & 0x1f) == 31 {
                    return SimplifiedIns {
                        mnemonic: "twui",
                        suffix: String::new(),
                        args: vec![
                            Argument::GPR(GPR(((self.code >> 16u8) & 0x1f) as _)),
                            Argument::Simm(Simm(
                                ((((self.code & 0xffff) ^ 0x8000).wrapping_sub(0x8000)) as i32)
                                    as _,
                            )),
                        ],
                        ins: self,
                    };
                }
            }
            _ => {}
        }
        SimplifiedIns::basic_form(self)
    }
}
#[allow(clippy::all, non_snake_case)]
impl Ins {
    #[inline(always)]
    pub fn field_simm(&self) -> isize {
        ((((self.code & 0xffff) ^ 0x8000).wrapping_sub(0x8000)) as i32) as _
    }
    #[inline(always)]
    pub fn field_uimm(&self) -> usize {
        (self.code & 0xffff) as _
    }
    #[inline(always)]
    pub fn field_offset(&self) -> isize {
        ((((self.code & 0xffff) ^ 0x8000).wrapping_sub(0x8000)) as i32) as _
    }
    #[inline(always)]
    pub fn field_ps_offset(&self) -> isize {
        ((((self.code & 0xfff) ^ 0x800).wrapping_sub(0x800)) as i32) as _
    }
    #[inline(always)]
    pub fn field_BO(&self) -> usize {
        ((self.code >> 21u8) & 0x1f) as _
    }
    #[inline(always)]
    pub fn field_BI(&self) -> usize {
        ((self.code >> 16u8) & 0x1f) as _
    }
    #[inline(always)]
    pub fn field_BH(&self) -> usize {
        ((self.code >> 11u8) & 0x3) as _
    }
    #[inline(always)]
    pub fn field_BD(&self) -> isize {
        ((((((self.code >> 2u8) & 0x3fff) ^ 0x2000).wrapping_sub(0x2000)) as i32) << 2u8) as _
    }
    #[inline(always)]
    pub fn field_LI(&self) -> isize {
        ((((((self.code >> 2u8) & 0xffffff) ^ 0x800000).wrapping_sub(0x800000)) as i32) << 2u8) as _
    }
    #[inline(always)]
    pub fn field_SH(&self) -> usize {
        ((self.code >> 11u8) & 0x1f) as _
    }
    #[inline(always)]
    pub fn field_MB(&self) -> usize {
        ((self.code >> 6u8) & 0x1f) as _
    }
    #[inline(always)]
    pub fn field_ME(&self) -> usize {
        ((self.code >> 1u8) & 0x1f) as _
    }
    #[inline(always)]
    pub fn field_rS(&self) -> usize {
        ((self.code >> 21u8) & 0x1f) as _
    }
    #[inline(always)]
    pub fn field_rD(&self) -> usize {
        ((self.code >> 21u8) & 0x1f) as _
    }
    #[inline(always)]
    pub fn field_rA(&self) -> usize {
        ((self.code >> 16u8) & 0x1f) as _
    }
    #[inline(always)]
    pub fn field_rB(&self) -> usize {
        ((self.code >> 11u8) & 0x1f) as _
    }
    #[inline(always)]
    pub fn field_rC(&self) -> usize {
        ((self.code >> 6u8) & 0x1f) as _
    }
    #[inline(always)]
    pub fn field_sr(&self) -> usize {
        ((self.code >> 16u8) & 0xf) as _
    }
    #[inline(always)]
    pub fn field_spr(&self) -> usize {
        (((((self.code >> 11u8) & 0x3ff) & 0b11111_00000u32) >> 5u32)
            | ((((self.code >> 11u8) & 0x3ff) & 0b00000_11111u32) << 5u32)) as u32 as _
    }
    #[inline(always)]
    pub fn field_frS(&self) -> usize {
        ((self.code >> 21u8) & 0x1f) as _
    }
    #[inline(always)]
    pub fn field_frD(&self) -> usize {
        ((self.code >> 21u8) & 0x1f) as _
    }
    #[inline(always)]
    pub fn field_frA(&self) -> usize {
        ((self.code >> 16u8) & 0x1f) as _
    }
    #[inline(always)]
    pub fn field_frB(&self) -> usize {
        ((self.code >> 11u8) & 0x1f) as _
    }
    #[inline(always)]
    pub fn field_frC(&self) -> usize {
        ((self.code >> 6u8) & 0x1f) as _
    }
    #[inline(always)]
    pub fn field_crbD(&self) -> usize {
        ((self.code >> 21u8) & 0x1f) as _
    }
    #[inline(always)]
    pub fn field_crbA(&self) -> usize {
        ((self.code >> 16u8) & 0x1f) as _
    }
    #[inline(always)]
    pub fn field_crbB(&self) -> usize {
        ((self.code >> 11u8) & 0x1f) as _
    }
    #[inline(always)]
    pub fn field_crfD(&self) -> usize {
        ((self.code >> 23u8) & 0x7) as _
    }
    #[inline(always)]
    pub fn field_crfS(&self) -> usize {
        ((self.code >> 18u8) & 0x7) as _
    }
    #[inline(always)]
    pub fn field_crm(&self) -> usize {
        ((self.code >> 12u8) & 0xff) as _
    }
    #[inline(always)]
    pub fn field_ps_I(&self) -> usize {
        ((self.code >> 12u8) & 0x7) as _
    }
    #[inline(always)]
    pub fn field_ps_IX(&self) -> usize {
        ((self.code >> 7u8) & 0x7) as _
    }
    #[inline(always)]
    pub fn field_ps_W(&self) -> usize {
        ((self.code >> 15u8) & 0x1) as _
    }
    #[inline(always)]
    pub fn field_ps_WX(&self) -> usize {
        ((self.code >> 10u8) & 0x1) as _
    }
    #[inline(always)]
    pub fn field_NB(&self) -> usize {
        ((self.code >> 11u8) & 0x1f) as _
    }
    #[inline(always)]
    pub fn field_tbr(&self) -> usize {
        (((((self.code >> 11u8) & 0x3ff) & 0b11111_00000u32) >> 5u32)
            | ((((self.code >> 11u8) & 0x3ff) & 0b00000_11111u32) << 5u32)) as u32 as _
    }
    #[inline(always)]
    pub fn field_mtfsf_FM(&self) -> usize {
        ((self.code >> 17u8) & 0xff) as _
    }
    #[inline(always)]
    pub fn field_mtfsf_IMM(&self) -> usize {
        ((self.code >> 12u8) & 0xf) as _
    }
    #[inline(always)]
    pub fn field_spr_SPRG(&self) -> usize {
        ((self.code >> 16u8) & 0x3) as _
    }
    #[inline(always)]
    pub fn field_spr_BAT(&self) -> usize {
        ((self.code >> 17u8) & 0x3) as _
    }
    #[inline(always)]
    pub fn field_TO(&self) -> usize {
        ((self.code >> 21u8) & 0x1f) as _
    }
    #[inline(always)]
    pub fn field_L(&self) -> usize {
        ((self.code >> 21u8) & 0x1) as _
    }
    #[inline(always)]
    pub fn field_OE(&self) -> bool {
        self.bit(21usize)
    }
    #[inline(always)]
    pub fn field_Rc(&self) -> bool {
        self.bit(31usize)
    }
    #[inline(always)]
    pub fn field_LK(&self) -> bool {
        self.bit(31usize)
    }
    #[inline(always)]
    pub fn field_AA(&self) -> bool {
        self.bit(30usize)
    }
    #[inline(always)]
    pub fn field_BP(&self) -> bool {
        ((self.code >> 21u8) & 0x1f) & 1 == 1
            && ((((((self.code >> 2u8) & 0x3fff) ^ 0x2000).wrapping_sub(0x2000)) as i32) << 2u8)
                >= 0
    }
    #[inline(always)]
    pub fn field_BNP(&self) -> bool {
        ((self.code >> 21u8) & 0x1f) & 1 == 1
            && ((((((self.code >> 2u8) & 0x3fff) ^ 0x2000).wrapping_sub(0x2000)) as i32) << 2u8) < 0
    }
    #[inline(always)]
    pub fn field_BP_ND(&self) -> bool {
        ((self.code >> 21u8) & 0x1f) & 1 == 1
    }
}
