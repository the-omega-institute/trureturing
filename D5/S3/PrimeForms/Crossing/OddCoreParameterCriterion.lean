/- GID: D5/S3/PrimeForms/Crossing/OddCoreParameterCriterion
   generality: G
   mirror-B: D5/B/S3/PrimeForms/Crossing/OddCoreParameterCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A positive square root has a unique exchange parameter iff twice it divides the gcd. -/

/- Library-search audit trail (2026-08-17):
   * Repository searches found no equivalent D5 declaration.
   * Pinned-Mathlib and smart-search queries found no theorem combining a square root,
     a gcd, divisibility, and a unique multiplier.
   * Loogle returned no match for the divisibility equivalence or the gcd equation.
     The only unique-multiplier hit was `uniq_inv_of_isField`, which is inapplicable here.
   * Mathlib's divisibility witness and positive natural multiplication cancellation are
     reused below; neither result is reproved.
-/

import Mathlib.Data.Nat.GCD.Basic

namespace D5.S3.PrimeForms.Crossing.OddCoreParameterCriterion

/-- Algebraic kernel of the odd-core double-cover criterion in residual E.44.

For a positive square root `x` of `m`, the exchange equation
`2 * x * y = gcd b c` has a unique natural parameter exactly when `2 * x`
divides `gcd b c`. This formalizes the square/gcd parameter criterion; it does
not assert the geodesic interpretation or the finite census recorded in E.44. -/
theorem odd_core_parameter_criterion (m b c : ℕ) :
    (∃ x : ℕ, x ^ 2 = m ∧ 0 < x ∧ ∃! y : ℕ, 2 * x * y = Nat.gcd b c) ↔
      ∃ x : ℕ, x ^ 2 = m ∧ 0 < x ∧ 2 * x ∣ Nat.gcd b c := by
  constructor
  · rintro ⟨x, hxSquare, hxPositive, y, hy, _⟩
    exact ⟨x, hxSquare, hxPositive, y, hy.symm⟩
  · rintro ⟨x, hxSquare, hxPositive, ⟨y, hy⟩⟩
    refine ⟨x, hxSquare, hxPositive, y, hy.symm, ?_⟩
    intro z hz
    exact mul_left_cancel₀
      (Nat.ne_of_gt (Nat.mul_pos (by decide) hxPositive)) (hz.trans hy)

#print axioms odd_core_parameter_criterion

end D5.S3.PrimeForms.Crossing.OddCoreParameterCriterion
