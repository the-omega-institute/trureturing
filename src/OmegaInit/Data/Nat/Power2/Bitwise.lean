module
public import Init.Data.Nat.Power2.Bitwise
public import OmegaInit.Data.Nat.Log2
public import OmegaInit.Data.Nat.Power2.Basic
public import OmegaInit.PropLemmas

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega.Nat
export _root_.Nat (and_sub_one_eq_zero_iff_isPowerOfTwo and_sub_one_testBit_log2 instDecidableIsPowerOfTwo ne_zero_and_sub_one_eq_zero_iff_isPowerOfTwo)
end Omega.Nat
