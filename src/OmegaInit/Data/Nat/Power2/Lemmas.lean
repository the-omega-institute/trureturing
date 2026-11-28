module
public import Init.Data.Nat.Power2.Lemmas
public import OmegaInit.Data.Nat.Power2.Basic

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega.Nat
export _root_.Nat (isPowerOfTwo_nextPowerOfTwo le_nextPowerOfTwo nextPowerOfTwo_eq_iff nextPowerOfTwo_eq_self nextPowerOfTwo_le not_isPowerOfTwo_zero)
end Omega.Nat
