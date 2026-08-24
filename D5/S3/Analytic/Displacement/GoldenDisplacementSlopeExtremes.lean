/- GID: D5/S3/Analytic/Displacement/GoldenDisplacementSlopeExtremes
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Identifies the attained extremal substitution-start ratios. -/

import D5.S3.Analytic.Displacement.GoldenDisplacementTwoConstraintRegion

/-! The extremal witnesses are the first two indices used by the merged theorem
`GoldenDisplacementTwoConstraintRegion.criterion_of_first_two`. That theorem supplies domination
of every positive-index criterion and is reused directly rather than restated here. The extremum
results below assert attainment, but do not assert uniqueness of either witness. -/

open D5.S1.Words
open GoldenDisplacementSurfaceNegativeBoundaryLinePositiveFailure

namespace GoldenDisplacementSlopeExtremes

noncomputable section

/-- Ratios of substitution starts at the nonzero indices. -/
def ratioSet : Set ℝ :=
  {r | ∃ v : ℕ, 1 ≤ v ∧ r = (goldenSubstStart v : ℝ) / (v : ℝ)}

/-- Every positive-index ratio is between three halves and two. -/
theorem ratio_bounds (v : ℕ) (hv : 1 ≤ v) :
    (3 : ℝ) / 2 ≤ (goldenSubstStart v : ℝ) / (v : ℝ) ∧
      (goldenSubstStart v : ℝ) / (v : ℝ) ≤ 2 := by
  have hv0 : (0 : ℝ) < (v : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt hv)
  have hlowerNat :=
    GoldenDisplacementTwoConstraintRegion.three_mul_le_two_mul_goldenSubstStart v hv
  have hlower : (3 : ℝ) * (v : ℝ) ≤ 2 * (goldenSubstStart v : ℝ) := by
    exact_mod_cast hlowerNat
  have hupperNat := goldenSubstStart_le_two_mul v
  have hupper : (goldenSubstStart v : ℝ) ≤ 2 * (v : ℝ) := by
    exact_mod_cast hupperNat
  constructor
  · apply (le_div_iff₀ hv0).2
    nlinarith
  · exact (div_le_iff₀ hv0).2 hupper

/-- The upper ratio bound is attained, hence is the greatest ratio. -/
theorem ratioSet_isGreatest : IsGreatest ratioSet 2 := by
  constructor
  · change ∃ v : ℕ, 1 ≤ v ∧ (2 : ℝ) =
      (goldenSubstStart v : ℝ) / (v : ℝ)
    refine ⟨1, by norm_num, ?_⟩
    norm_num [goldenSubstStart_one_eq_two]
  · intro r hr
    rcases hr with ⟨v, hv, rfl⟩
    exact (ratio_bounds v hv).2

/-- The lower ratio bound is attained, hence is the least ratio. -/
theorem ratioSet_isLeast : IsLeast ratioSet ((3 : ℝ) / 2) := by
  constructor
  · change ∃ v : ℕ, 1 ≤ v ∧ (3 : ℝ) / 2 =
      (goldenSubstStart v : ℝ) / (v : ℝ)
    refine ⟨2, by norm_num, ?_⟩
    have htwo : goldenSubstStart 2 = 3 := by decide
    norm_num [htwo]
  · intro r hr
    rcases hr with ⟨v, hv, rfl⟩
    exact (ratio_bounds v hv).1

end

end GoldenDisplacementSlopeExtremes
