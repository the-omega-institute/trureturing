/- GID: D5/S3/Factorization/KlineFactorialLcmTotient
   generality: I
   mirror-B: D5/B/S3/Factorization/KlineFactorialLcmTotient
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.NumberTheory.Chebyshev, mathlib/module/Mathlib.Data.Nat.Totient, mathlib/module/Mathlib.Data.Nat.Prime.Nth, mathlib/module/Mathlib.Data.Nat.Prime.Factorial]
   utility: none
   digest: Kline's A025527 quotient equals the totient quotient at every one-based prime-minus-one index. -/

import Mathlib.NumberTheory.Chebyshev
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Factorization.KlineFactorialLcmTotient

/-- The independently defined A025527 quotient, with exact rational division. -/
def a (m : ℕ) : ℚ := (m.factorial : ℚ) / (Nat.lcmUpto m : ℚ)

/-- Kline's conjecture, including the first prime and every positive integer index. -/
theorem result : ∀ j : ℤ, 1 ≤ j →
    let p := Nat.nth Nat.Prime (j.toNat - 1)
    let m := p - 1
    a m = (Nat.totient m.factorial : ℚ) / (Nat.totient (Nat.lcmUpto m) : ℚ) := by
  intro j hj
  dsimp only
  let m := Nat.nth Nat.Prime (j.toNat - 1) - 1
  change a m = (Nat.totient m.factorial : ℚ) / (Nat.totient (Nat.lcmUpto m) : ℚ)
  have hs : m.factorial.primeFactors = (Nat.lcmUpto m).primeFactors := by
    rw [Nat.primeFactors_lcmUpto]
    ext q
    simp only [Nat.mem_primeFactors, Nat.mem_primesLE]
    constructor
    · rintro ⟨hq, hd, _⟩
      exact ⟨hq.dvd_factorial.mp hd, hq⟩
    · rintro ⟨hle, hq⟩
      exact ⟨hq, hq.dvd_factorial.mpr hle, Nat.factorial_ne_zero m⟩
  have hL : (Nat.lcmUpto m : ℚ) ≠ 0 := by
    exact_mod_cast Nat.lcmUpto_ne_zero m
  have hT : (Nat.totient (Nat.lcmUpto m) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.lcmUpto_pos m)).ne'
  unfold a
  apply (div_eq_div_iff hL hT).mpr
  rw [Nat.totient_eq_mul_prod_factors, Nat.totient_eq_mul_prod_factors, hs]
  ring

#check result
#print axioms result

end D5.S3.Factorization.KlineFactorialLcmTotient
