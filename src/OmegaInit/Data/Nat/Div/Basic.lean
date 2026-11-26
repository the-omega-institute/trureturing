module
public import Init.Data.Nat.Div.Basic
public import OmegaInit.Core

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega
export _root_ (Nat.mod.eq_2)
end Omega
namespace Omega.Nat
export _root_.Nat (div_add_mod div_eq_ite div_eq_of_lt div_eq_sub_div div_le_self div_lt_iff_lt_mul div_lt_self div_mul_le_self div_one div_zero le_div_iff_mul_le modCore_eq modCore_eq_mod mod_add_div mod_def mod_eq_ite mod_eq_of_lt mod_eq_sub_div_mul mod_eq_sub_mul_div mod_one mod_zero mul_div_le zero_div)
end Omega.Nat
