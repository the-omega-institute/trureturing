module
public import Init.Data.Int.Bitwise.Lemmas
public import OmegaInit.Data.Int.Bitwise.Basic
public import OmegaInit.Data.Int.DivMod.Basic

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega
export _root_ (Int.shiftLeft.eq_1 Int.shiftLeft.eq_2 Int.shiftRight.eq_1 Int.shiftRight.eq_2)
end Omega
namespace Omega.Int
export _root_.Int (add_shiftLeft instNeZeroHShiftLeftNat le_shiftRight_of_nonneg le_shiftRight_of_nonpos mul_shiftLeft natCast_shiftLeft natCast_shiftRight negSucc_shiftRight neg_shiftLeft shiftLeft_add shiftLeft_eq shiftLeft_eq' shiftLeft_eq_zero_iff shiftLeft_mul shiftLeft_mul_shiftLeft shiftLeft_shiftRight_cancel shiftLeft_shiftRight_eq shiftLeft_shiftRight_eq_shiftLeft_of_le shiftLeft_shiftRight_eq_shiftRight_of_le shiftLeft_succ shiftLeft_succ' shiftLeft_zero shiftRight_add shiftRight_eq shiftRight_eq_div_pow shiftRight_le_of_nonneg shiftRight_le_of_nonpos shiftRight_shiftLeft_cancel shiftRight_zero zero_shiftLeft zero_shiftRight)
end Omega.Int
