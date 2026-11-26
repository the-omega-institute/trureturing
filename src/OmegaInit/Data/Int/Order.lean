module
public import Init.Data.Int.Order
public import OmegaInit.Data.Int.Basic

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega
export _root_ (Int.le.dest Int.le.dest_sub Int.le.intro Int.le.intro_sub Int.natAbs.eq_1 Int.natAbs.eq_2 Int.toNat.eq_1)
end Omega
namespace Omega.Int
export _root_.Int (add_le_add add_le_add_left add_le_add_right eq_ofNat_of_zero_le ge_of_eq le_antisymm le_antisymm_iff le_def le_of_add_le_add_left le_of_eq le_of_lt le_refl le_rfl le_total le_trans lt_iff_add_one_le lt_irrefl lt_of_le_of_lt lt_of_lt_of_le lt_succ lt_trans natAbs_eq natAbs_eq_zero natAbs_mul natAbs_mul_self natAbs_natCast natAbs_neg natAbs_negOfNat natAbs_negSucc natAbs_ofNat' natAbs_one natAbs_zero natCast_nonneg ne_of_gt ne_of_lt nonneg_def nonneg_or_nonneg_neg ofNat_succ_pos sign_natCast_add_one sign_neg sign_negSucc sign_neg_one sign_one sign_sign sign_zero toNat_add_toNat_neg_eq_natAbs toNat_natCast toNat_negSucc toNat_neg_natCast toNat_one toNat_sub_toNat_neg toNat_zero)
end Omega.Int
