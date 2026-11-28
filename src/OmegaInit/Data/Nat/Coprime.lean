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
