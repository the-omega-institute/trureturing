module
public import Init.Data.Nat.Bitwise.Lemmas
public import OmegaInit.Core
public import OmegaInit.Data.Nat.Bitwise.Basic

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega.Nat
export _root_.Nat (and_lt_two_pow bitwise_lt_two_pow exists_ge_and_testBit_of_ge_two_pow exists_testBit_of_ne_zero lt_pow_two_of_testBit or_lt_two_pow testBit_add_one testBit_div_two testBit_succ)
end Omega.Nat
