module
public import Init.Data.Nat.Basic
public import OmegaInit.Core

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega.Nat
export _root_.Nat (add_assoc add_comm add_le_add_left add_left_cancel add_mul add_one add_right_cancel add_right_comm add_succ eq_zero_of_add_eq_zero le_total mul_add mul_assoc mul_comm mul_one mul_succ mul_zero one_mul pred_succ pred_zero sub_le_of_le_add sub_succ sub_zero succ_add succ_mul succ_ne_zero zero_add zero_mul)
end Omega.Nat
