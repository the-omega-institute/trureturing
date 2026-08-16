/- GID: D5/S3/Weil/ZetaBridge/TwoDimensionalEvaluationNegativeDirection
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/TwoDimensionalEvaluationNegativeDirection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A full two-coordinate evaluation image contains a direction with negative cross value. -/

import D5.S3.Weil.ZetaBridge.ConvolutionSquareOrbitBounds
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic

/- Library-search audit trail (2026-08-16):
   * Loogle query `Submodule.eq_top_of_finrank_eq` found the exact maximal-rank
     submodule theorem imported and applied below.
   * Loogle query for the complete implication from a two-dimensional complex
     evaluation image to a negative cross value found no declaration.
   * LeanSearch was reachable, but its public search endpoints returned no usable
     query response for the complete implication.
   * Repository searches found the same multiplicity-weighted cross expression in
     ConvolutionSquareOrbitBounds, but no equal-or-stronger existence theorem.
-/

namespace D5.S3.Weil.ZetaBridge.TwoDimensionalEvaluationNegativeDirection

open scoped ComplexConjugate

/-- The real cross value attached to a two-coordinate complex evaluation. -/
def crossValue (m : ℕ) (z : ℂ × ℂ) : ℝ :=
  4 * (m : ℝ) * (z.1 * conj z.2).re

/-- A complex-linear evaluation with two-dimensional image contains an input whose
positive-multiplicity cross value is strictly negative. -/
theorem two_dimensional_evaluation_has_negative_direction
    {T : Type*} [AddCommGroup T] [Module ℂ T]
    (E : T →ₗ[ℂ] ℂ × ℂ) (m : ℕ) (hm : 0 < m)
    (hdim : Module.finrank ℂ E.range = 2) :
    ∃ g : T, crossValue m (E g) < 0 := by
  have hrange : E.range = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    calc
      Module.finrank ℂ E.range = 2 := hdim
      _ = Module.finrank ℂ (ℂ × ℂ) := by simp [Module.finrank_prod]
  have hsurjective : Function.Surjective E := LinearMap.range_eq_top.mp hrange
  obtain ⟨g, hg⟩ := hsurjective (1, -1)
  refine ⟨g, ?_⟩
  rw [hg]
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  simpa [crossValue] using
    (neg_neg_of_pos (mul_pos (show (0 : ℝ) < 4 by norm_num) hm'))

/-- The hypotheses are jointly satisfiable for the identity evaluation on two
complex coordinates. -/
example :
    ∃ g : ℂ × ℂ, crossValue 1 ((LinearMap.id : (ℂ × ℂ) →ₗ[ℂ] ℂ × ℂ) g) < 0 := by
  apply two_dimensional_evaluation_has_negative_direction
  · norm_num
  · rw [LinearMap.range_id, finrank_top]
    simp [Module.finrank_prod]

end D5.S3.Weil.ZetaBridge.TwoDimensionalEvaluationNegativeDirection
