module
public import Init.Data.Int.DivMod.Bootstrap
public import OmegaInit.Data.Int.DivMod.Basic
public import OmegaInit.Data.Nat.Div.Basic

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega
export _root_ (Int.ediv.eq_1 Int.ediv.eq_2 Int.ediv.eq_3 Int.ediv.eq_4 Int.ediv.eq_5)
end Omega
namespace Omega.Int
export _root_.Int (add_ediv_of_dvd_left add_ediv_of_dvd_right add_emod add_emod_emod add_emod_eq_add_emod_right add_mul_ediv_left add_mul_ediv_right add_mul_emod_self_left add_mul_emod_self_right bmod_def bmod_emod div_def dvd_def dvd_iff_emod_eq_zero dvd_mul_left dvd_mul_right dvd_neg dvd_of_emod_eq_zero dvd_refl dvd_trans dvd_zero ediv_mul_add_emod ediv_mul_cancel ediv_mul_cancel_of_emod_eq_zero ediv_mul_self ediv_neg ediv_nonneg_iff_of_pos ediv_zero emod_add_cancel_right emod_add_ediv_mul emod_add_emod emod_add_mul_ediv emod_def emod_emod emod_emod_of_dvd emod_eq_zero_of_dvd emod_lt_of_pos emod_nonneg emod_pos_of_not_dvd emod_self emod_zero lt_mul_ediv_self_add mul_add_emod_self_left mul_add_emod_self_right mul_ediv_add_emod mul_ediv_assoc mul_ediv_assoc' mul_ediv_cancel mul_ediv_cancel' mul_ediv_cancel_left mul_ediv_cancel_of_emod_eq_zero mul_ediv_self mul_ediv_self_le mul_emod mul_emod_left mul_emod_right natAbs_dvd_natAbs natCast_emod neg_dvd neg_ediv_of_dvd ofNat_dvd ofNat_dvd_left one_dvd sub_ediv_of_dvd sub_emod zero_dvd zero_ediv zero_emod)
end Omega.Int
