module
public import Init.Data.Nat.Lemmas
public import OmegaInit.Data.Nat.Basic
public import OmegaInit.Data.Nat.Div.Basic
public import OmegaInit.Data.Nat.Log2

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega.Nat
export _root_.Nat (add_add_add_comm add_eq_left add_eq_right add_eq_zero_iff add_left_cancel_iff add_left_inj add_right_cancel_iff add_right_inj add_sub_cancel_right add_succ_sub_one eq_zero_of_add_eq_zero_right le_log2 left_eq_add log2_eq_iff log2_lt lt_iff_add_one_le lt_one_add_iff mul_eq_zero mul_right_comm one_add one_add_le_iff one_add_sub_one one_le_of_lt one_lt_succ_succ one_pow pow_add pow_add' pow_add_one' pow_mul pow_mul' pow_right_comm pow_succ' pow_two pred_eq_of_eq_succ pred_one_add pred_sub right_eq_add sub_one sub_right_comm sub_succ' succ_add_eq_add_succ succ_add_sub_one succ_eq_one_add succ_le succ_ne_succ succ_sub_one two_pow_succ)
end Omega.Nat
