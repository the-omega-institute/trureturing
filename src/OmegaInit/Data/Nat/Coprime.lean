module
public import Init.Data.Nat.Coprime
public import OmegaInit.Data.Nat.Gcd

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega.Nat
export _root_.Nat (Coprime instDecidableCoprime coprime_iff_gcd_eq_one coprime_one_left coprime_one_right
  coprime_zero_left coprime_zero_right)
namespace Coprime
export _root_.Nat.Coprime (gcd_eq_one)
end Coprime
end Omega.Nat

namespace Omega.Nat
export _root_.Nat (coprime_comm coprime_div_gcd_div_gcd coprime_mul_iff_left coprime_mul_iff_right
  coprime_self exists_coprime exists_coprime' gcd_mul_gcd_of_coprime_of_mul_eq_mul
  not_coprime_of_dvd_of_dvd)
end Omega.Nat

namespace Omega.Nat.Coprime
export _root_.Nat.Coprime (coprime_div_left coprime_div_right coprime_dvd_left coprime_dvd_right
  coprime_mul_left coprime_mul_left_right coprime_mul_right coprime_mul_right_right
  dvd_of_dvd_mul_left dvd_of_dvd_mul_right eq_1 eq_one_of_dvd gcd_both gcd_left gcd_mul
  gcd_mul_left_cancel gcd_mul_left_cancel_right gcd_mul_right_cancel gcd_mul_right_cancel_right
  gcd_right mul_dvd_of_dvd_of_dvd mul_gcd mul_left mul_right pow pow_left pow_right symm)
end Omega.Nat.Coprime
