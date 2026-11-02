/- GID: D5/S3/Arith/Mobius/GranvikMobiusRealPart
   generality: G
   mirror-B: D5/B/S3/Arith/Mobius/GranvikMobiusRealPart
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Granvik's real-part formula for the even-supported signed Mobius function. -/

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.IntervalCases

/-! The exact arithmetic real-part conjecture in OEIS A292273. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Mobius.GranvikMobiusRealPart

/-- The arithmetic definition of OEIS A292273 at positive indices. -/
def a (n : ℕ) : ℤ :=
  if n % 2 = 1 then 0 else -ArithmeticFunction.moebius n

/-- Granvik's A292273 conjecture, with the standard integer Mobius function
and ordinary natural powers of the complex imaginary unit. -/
theorem result (n : ℕ) (hn : 0 < n) :
    (a n : ℝ) = ((ArithmeticFunction.moebius n : ℂ) * Complex.I ^ n).re := by
  have hlt : n % 4 < 4 := Nat.mod_lt n (by decide)
  interval_cases h : n % 4
  · have hfour : 4 ∣ n := Nat.dvd_of_mod_eq_zero h
    have hmu : ArithmeticFunction.moebius n = 0 :=
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree (by
        intro hs
        exact Nat.squarefree_iff_prime_squarefree.mp hs 2 Nat.prime_two hfour)
    simp [a, hmu]
  · have htwo : n % 2 = 1 := by omega
    rw [Complex.I_pow_eq_pow_mod, h]
    simp [a, htwo, Complex.mul_re]
  · have htwo : n % 2 = 0 := by omega
    rw [Complex.I_pow_eq_pow_mod, h]
    simp [a, htwo, Complex.I_sq]
  · have htwo : n % 2 = 1 := by omega
    rw [Complex.I_pow_eq_pow_mod, h]
    simp [a, htwo, Complex.I_pow_three, Complex.mul_re]

end D5.S3.Arith.Mobius.GranvikMobiusRealPart
