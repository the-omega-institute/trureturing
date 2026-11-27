module
public import Init.Data.Nat.Bitwise.Lemmas
public import OmegaInit.Core
public import OmegaInit.Data.Nat.Bitwise.Basic

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega.Nat
export _root_.Nat (and_lt_two_pow bitwise_lt_two_pow exists_ge_and_testBit_of_ge_two_pow exists_testBit_of_ne_zero ge_two_pow_of_testBit lt_pow_two_of_testBit one_and_eq_mod_two or_lt_two_pow testBit_add_one testBit_and testBit_bitwise testBit_div_two testBit_lt_two_pow testBit_of_two_pow_le_and_two_pow_add_one_gt testBit_or testBit_succ zero_testBit)
end Omega.Nat
