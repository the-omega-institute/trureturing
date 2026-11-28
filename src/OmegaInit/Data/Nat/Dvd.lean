module
public import Init.Data.Nat.Dvd
public import OmegaInit.Data.Nat.Div.Basic
public import OmegaInit.SimpLemmas

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega.Nat
export _root_.Nat (decidable_dvd div_mul_cancel dvd_add dvd_add_iff_left dvd_add_iff_right dvd_antisymm dvd_iff_mod_eq_zero dvd_mod_iff dvd_mul_left dvd_mul_left_of_dvd dvd_mul_right dvd_mul_right_of_dvd dvd_of_mod_eq_zero dvd_of_mul_dvd_mul_left dvd_of_mul_dvd_mul_right dvd_one dvd_refl dvd_sub dvd_sub_iff_left dvd_sub_iff_right dvd_trans dvd_zero emod_pos_of_not_dvd eq_one_of_dvd_one eq_zero_of_zero_dvd le_of_dvd mod_eq_zero_of_dvd mod_mod_of_dvd mul_div_assoc mul_div_cancel' mul_dvd_mul mul_dvd_mul_left mul_dvd_mul_right one_dvd pos_of_dvd_of_pos zero_dvd)
end Omega.Nat
