module
public import Init.Data.Int.DivMod.Basic
public import OmegaInit.Data.Int.Basic

public section
namespace Omega.Int
export _root_.Int (ediv emod instDiv instMod natCast_ediv ofNat_ediv_ofNat ofNat_ediv_negSucc
  negSucc_ediv_ofNat_succ negSucc_ediv_negSucc negSucc_emod_ofNat negSucc_emod_negSucc
  tdiv tmod ofNat_tdiv fdiv fmod ofNat_fdiv bmod bdiv divExact divExact_eq_ediv
  ediv.match_1 emod.match_1 tdiv.match_1 fdiv.match_1 fmod.match_1
  fdiv.eq_1 fdiv.eq_2 fdiv.eq_3 fdiv.eq_4 fdiv.eq_5 fdiv.eq_6)
end Omega.Int
