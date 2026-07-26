/- GID: D5/S1/Digit/CompositeGasUnit
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Characteristic norm criterion for the parameterized digit-gas root. -/

import D5.S1.Digit.CompositeGasBeta

namespace D5.S1.Digit

/-- The other root of the characteristic polynomial `X^2 - X - c`.

This name deliberately records a characteristic root, rather than claiming an
algebraic conjugate when the characteristic polynomial is reducible.
-/
noncomputable def e6BetaConjChar (c : ℕ) : ℝ :=
  1 - e6Beta c

/-- The product of the two characteristic roots is the constant term `-c`. -/
theorem e6_beta_char_norm (c : ℕ) :
    e6Beta c * e6BetaConjChar c = -(c : ℝ) := by
  rw [e6BetaConjChar]
  nlinarith [e6_beta_sq c]

/-- The sum of the two characteristic roots is the linear coefficient `1`. -/
theorem e6_beta_char_trace (c : ℕ) :
    e6Beta c + e6BetaConjChar c = 1 := by
  simp [e6BetaConjChar]

/--
On the active parameter domain `c ≥ 1`, the characteristic norm has absolute
value one exactly at the golden parameter `c = 1`.

A full `IsUnit` statement in the integral ring `ℤ[β]` is deferred to L3b',
which must first supply the parameterized integral-ring carrier. This theorem
is the closed characteristic-norm core and does not reuse the fixed
`GoldenInt` carrier for `X^2 - X - 1`.
-/
theorem e6_beta_char_norm_unit_iff (c : ℕ) (hc : 1 ≤ c) :
    (|e6Beta c * e6BetaConjChar c| = 1) ↔ c = 1 := by
  have hc_real : (1 : ℝ) ≤ (c : ℝ) := by
    exact_mod_cast hc
  rw [e6_beta_char_norm, abs_neg, abs_of_nonneg (by linarith : 0 ≤ (c : ℝ))]
  norm_cast

end D5.S1.Digit
