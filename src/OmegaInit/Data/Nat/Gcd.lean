module
public import Init.Data.Nat.Gcd
public import OmegaInit.Data.Nat.Div.Basic
public import OmegaInit.Prelude

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega.Nat
export _root_.Nat (gcd gcd_add_one gcd_one_left gcd_one_right gcd_rec gcd_succ gcd_zero_left gcd_zero_right)
end Omega.Nat

namespace Omega.Nat
export _root_.Nat (dvdProdDvdOfDvdProd dvd_gcd eq_zero_of_gcd_eq_zero_left
  eq_zero_of_gcd_eq_zero_right gcd_assoc gcd_comm gcd_div gcd_dvd gcd_dvd_gcd_mul_left_left
  gcd_dvd_gcd_mul_left_right gcd_dvd_gcd_mul_right_right gcd_dvd_gcd_of_dvd_left
  gcd_dvd_gcd_of_dvd_right gcd_dvd_left gcd_dvd_right gcd_eq_left gcd_eq_zero_iff gcd_mul_left
  gcd_mul_left_left gcd_mul_right gcd_mul_right_dvd_mul_gcd gcd_mul_right_left gcd_mul_right_right
  gcd_pos_of_pos_left gcd_self)
end Omega.Nat

namespace Omega.Nat.gcd
export _root_.Nat.gcd (induction)
end Omega.Nat.gcd
