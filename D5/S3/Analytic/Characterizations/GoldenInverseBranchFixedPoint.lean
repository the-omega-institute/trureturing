/- GID: D5/S3/Analytic/Characterizations/GoldenInverseBranchFixedPoint
   generality: I
   mirror-B: D5/B/S3/Analytic/Characterizations/GoldenInverseBranchFixedPoint
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The positive fixed point of the first inverse branch is the inverse golden ratio. -/

import D5.S3.Analytic.Characterizations.GoldenTransferTriangle

/-!
Library-search audit trail (2026-08-31): the repository contains the reciprocal identity inside
`golden_transfer_triangle`, but no public theorem states the fixed-point equation or characterizes
its positive solution. Pinned Mathlib provides `Real.goldenRatio_sq` and the reciprocal identities,
but no theorem for the map `x ↦ 1 / (x + 1)`.
-/

namespace D5.S3.Analytic.Characterizations.GoldenInverseBranchFixedPoint

open D5.S3.Analytic.Characterizations.GoldenTransferTriangle

/-- A positive real number is fixed by the first inverse branch exactly when it is the inverse
golden ratio. -/
theorem golden_inverse_branch_positive_fixed_point_iff :
    ∀ x : ℝ, 0 < x →
      ((fun y : ℝ => 1 / (y + 1)) x = x ↔ x = Real.goldenRatio⁻¹) := by
  intro x hx
  have hinv : Real.goldenRatio - 1 = Real.goldenRatio⁻¹ :=
    golden_transfer_triangle.2.1
  constructor
  · intro hfixed
    have hden : x + 1 ≠ 0 := by linarith
    have hquad : 1 = x * (x + 1) := (div_eq_iff hden).mp hfixed
    calc
      x = Real.goldenRatio - 1 := by
        nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio]
      _ = Real.goldenRatio⁻¹ := hinv
  · rintro rfl
    have hsum : Real.goldenRatio⁻¹ + 1 = Real.goldenRatio := by linarith
    change 1 / (Real.goldenRatio⁻¹ + 1) = Real.goldenRatio⁻¹
    rw [hsum]
    simp only [one_div]

#print axioms golden_inverse_branch_positive_fixed_point_iff

end D5.S3.Analytic.Characterizations.GoldenInverseBranchFixedPoint
