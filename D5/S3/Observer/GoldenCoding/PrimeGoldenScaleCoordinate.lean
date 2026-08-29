/- GID: D5/S3/Observer/GoldenCoding/PrimeGoldenScaleCoordinate
   generality: I
   mirror-B: D5/B/S3/Observer/GoldenCoding/PrimeGoldenScaleCoordinate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prime logarithmic lengths admit a golden scale coordinate. -/

import D5.S3.CompletionDynamics.GoldenMobius.GoldenScaleHelix
import Mathlib.NumberTheory.SumPrimeReciprocals

/-!
This module introduces only a coordinate bridge:

`p ↦ log p / (2 log φ)`.

It does not assert that prime dynamics is semiconjugate to golden Möbius
dynamics.  Such a wormhole would require an independently specified prime
update and a commuting-square proof.

The machine layer closes positivity and prime-power scaling of the coordinate.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Observer.GoldenCoding.PrimeGoldenScaleCoordinate

open D5.S3.CompletionDynamics.GoldenMobius.GoldenScaleHelix

/-- Golden-normalized logarithmic coordinate of a positive real scale. -/
def goldenScaleCoordinate (scale : ℝ) : ℝ :=
  Real.log scale / goldenScalePeriod

/-- Golden-normalized logarithmic coordinate of a prime. -/
def primeGoldenScaleCoordinate (prime : Nat.Primes) : ℝ :=
  goldenScaleCoordinate prime.1

/-- Every prime has a positive golden scale coordinate. -/
theorem prime_golden_scale_coordinate_pos
    (prime : Nat.Primes) :
    0 < primeGoldenScaleCoordinate prime := by
  unfold primeGoldenScaleCoordinate goldenScaleCoordinate
  exact div_pos
    (Real.log_pos (by exact_mod_cast prime.2.one_lt))
    golden_scale_period_pos

/-- Prime powers advance linearly in the lifted golden scale coordinate. -/
theorem prime_power_golden_scale_coordinate
    (prime : Nat.Primes) (exponent : ℕ) :
    goldenScaleCoordinate ((prime.1 : ℝ) ^ exponent) =
      exponent * primeGoldenScaleCoordinate prime := by
  unfold primeGoldenScaleCoordinate goldenScaleCoordinate
  rw [Real.log_pow]
  ring

/-- The coordinate of the first power is the prime coordinate itself. -/
@[simp] theorem prime_one_golden_scale_coordinate
    (prime : Nat.Primes) :
    goldenScaleCoordinate (prime.1 : ℝ) =
      primeGoldenScaleCoordinate prime :=
  rfl

#print axioms prime_golden_scale_coordinate_pos
#print axioms prime_power_golden_scale_coordinate
#print axioms prime_one_golden_scale_coordinate

end D5.S3.Observer.GoldenCoding.PrimeGoldenScaleCoordinate
