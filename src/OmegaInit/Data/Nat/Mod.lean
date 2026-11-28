module
public import Init.Data.Nat.Mod
public import OmegaInit.Core
import OmegaInit.Data.Nat.Dvd
import OmegaInit.Data.Nat.Div.Lemmas

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega.Nat
export _root_.Nat (mul_lt_mul_left mul_lt_mul_right lt_of_mul_lt_mul_left
  lt_of_mul_lt_mul_right div_lt_of_lt_mul mod_mul_right_div_self
  mod_mul_left_div_self mod_mul_right_mod mod_mul_left_mod
  mod_mul mod_pow_succ two_pow_mod_two_eq_zero
  two_pow_mod_two_eq_one)
end Omega.Nat
