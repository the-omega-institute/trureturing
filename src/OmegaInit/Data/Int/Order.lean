module
public import Init.Data.Int.Order
public import OmegaInit.Data.Int.Basic

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega.Int
export _root_.Int (natAbs_eq_zero natAbs_mul natAbs_mul_self natAbs_neg natAbs_negOfNat ofNat_succ_pos)
end Omega.Int
