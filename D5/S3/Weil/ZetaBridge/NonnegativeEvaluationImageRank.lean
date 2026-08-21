/- GID: D5/S3/Weil/ZetaBridge/NonnegativeEvaluationImageRank
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/NonnegativeEvaluationImageRank
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A nonnegative two-coordinate cross form has image dimension at most one. -/

import D5.S3.Weil.ZetaBridge.TwoDimensionalEvaluationNegativeDirection

/- Library-search audit trail (2026-08-21):
   * Repository search found the exact predecessor
     `two_dimensional_evaluation_has_negative_direction`; it is imported and applied below.
   * Repository search found no existing contrapositive rank bound for the same `crossValue`.
   * Pinned Mathlib search found the supporting declaration `Submodule.finrank_le` in
     `LinearAlgebra/Dimension/Constructions.lean`, but no packaged theorem for this full claim.
   * The canonical `crossValue` is reused from the predecessor module; no sibling evaluation
     or quadratic-form object is redeclared here. -/

namespace D5.S3.Weil.ZetaBridge.NonnegativeEvaluationImageRank

open D5.S3.Weil.ZetaBridge.TwoDimensionalEvaluationNegativeDirection

/-- If the multiplicity-weighted cross form is nonnegative on every test, the evaluation
image has complex dimension at most one and cannot fill both mirror coordinates. -/
theorem nonnegative_evaluation_image_finrank_le_one
    {T : Type*} [AddCommGroup T] [Module ℂ T]
    (E : T →ₗ[ℂ] ℂ × ℂ) (m : ℕ) (hm : 0 < m)
    (hnonnegative : ∀ g : T, 0 ≤ crossValue m (E g)) :
    Module.finrank ℂ E.range ≤ 1 ∧ ¬ Function.Surjective E := by
  have hrank : Module.finrank ℂ E.range ≤ 1 := by
    by_contra hnot
    have hambient : Module.finrank ℂ E.range ≤ 2 := by
      calc
        Module.finrank ℂ E.range ≤ Module.finrank ℂ (ℂ × ℂ) := E.range.finrank_le
        _ = 2 := by simp [Module.finrank_prod]
    have hdim : Module.finrank ℂ E.range = 2 := by omega
    obtain ⟨g, hnegative⟩ :=
      two_dimensional_evaluation_has_negative_direction E m hm hdim
    exact (not_lt_of_ge (hnonnegative g)) hnegative
  refine ⟨hrank, ?_⟩
  intro hsurjective
  have hrange : E.range = ⊤ := LinearMap.range_eq_top.mpr hsurjective
  have hdim : Module.finrank ℂ E.range = 2 := by
    rw [hrange, finrank_top]
    simp [Module.finrank_prod]
  omega

/-- The nonnegativity hypothesis has a checked witness: the zero evaluation. -/
example :
    Module.finrank ℂ (0 : (ℂ × ℂ) →ₗ[ℂ] ℂ × ℂ).range ≤ 1 ∧
      ¬ Function.Surjective (0 : (ℂ × ℂ) →ₗ[ℂ] ℂ × ℂ) := by
  apply nonnegative_evaluation_image_finrank_le_one (m := 1)
  · norm_num
  · intro g
    simp [crossValue]

#print axioms nonnegative_evaluation_image_finrank_le_one

end D5.S3.Weil.ZetaBridge.NonnegativeEvaluationImageRank
