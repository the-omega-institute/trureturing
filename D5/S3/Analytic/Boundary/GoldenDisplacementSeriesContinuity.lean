/- GID: D5/S3/Analytic/Boundary/GoldenDisplacementSeriesContinuity
   generality: I
   mirror-B: D5/B/S3/Analytic/Boundary/GoldenDisplacementSeriesContinuity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Proves continuity of the golden displacement sum on its convergence region. -/

/- Library-search audit trail (2026-08-26):
   * Repository Lean and Blueprint searches found no continuity statement for the
     golden displacement sum and no locally uniform convergence statement for its terms.
   * Pinned Mathlib's `continuous_tsum` and `continuousOn_tsum` both require one
     summable majorant on their whole domain. Neither applies directly to this region.
   * `Real.rpow_le_rpow_of_exponent_le` supplies the coordinatewise domination below;
     `dTerm_summable_iff_two_constraints` keeps the series at each local lower
     corner summable.
-/

import D5.S3.Analytic.Displacement.GoldenDisplacementTwoConstraintRegion

set_option autoImplicit false
set_option relaxedAutoImplicit false

open GoldenDisplacementEulerProduct
open GoldenDisplacementTwoConstraintRegion
open GoldenDesubstitutionLength

namespace D5.S3.Analytic.Boundary.GoldenDisplacementSeriesContinuity

/-- The golden displacement sum is continuous throughout its exact convergence region. -/
theorem golden_displacement_series_continuousOn :
    ContinuousOn (fun p : ℝ × ℝ => ∑' n, dTerm p.1 p.2 n)
      {p : ℝ × ℝ | Summable (dTerm p.1 p.2)} := by
  apply continuousOn_of_forall_continuousAt
  rintro p hp
  have hpConstraints := (dTerm_summable_iff_two_constraints p.1 p.2).mp hp
  let delta : ℝ :=
    min ((2 * p.1 + p.2 - 1) / 6) ((3 * p.1 + 2 * p.2 - 1) / 10)
  have hdelta : 0 < delta := by
    dsimp [delta]
    exact lt_min (by linarith [hpConstraints.1]) (by linarith [hpConstraints.2])
  let corner : ℝ × ℝ := (p.1 - delta, p.2 - delta)
  have hcornerConstraints :
      1 < 2 * corner.1 + corner.2 ∧ 1 < 3 * corner.1 + 2 * corner.2 := by
    have hfirst : delta ≤ (2 * p.1 + p.2 - 1) / 6 := by
      exact min_le_left _ _
    have hsecond : delta ≤ (3 * p.1 + 2 * p.2 - 1) / 10 := by
      exact min_le_right _ _
    dsimp [corner]
    constructor <;> linarith
  have hcornerSummable : Summable (dTerm corner.1 corner.2) :=
    (dTerm_summable_iff_two_constraints corner.1 corner.2).mpr hcornerConstraints
  let upper : Set (ℝ × ℝ) := Set.Ici corner.1 ×ˢ Set.Ici corner.2
  have htermContinuous :
      ∀ n : ℕ, ContinuousOn (fun q : ℝ × ℝ => dTerm q.1 q.2 n) upper := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp only [dTerm_zero]
      fun_prop
    · unfold dTerm
      simp only [hn, ↓reduceIte]
      have hnCast : (n : ℝ) ≠ 0 := by
        exact_mod_cast hn
      have hnSCast : (nS n : ℝ) ≠ 0 := by
        exact_mod_cast GoldenSubstitutionOrbit.nS_ne_zero n
      exact
        (((Real.continuous_const_rpow hnSCast).comp
            (continuous_neg.comp continuous_fst)).mul
          ((Real.continuous_const_rpow hnCast).comp
            (continuous_neg.comp continuous_snd))).continuousOn
  have hdomination :
      ∀ n q, q ∈ upper → ‖dTerm q.1 q.2 n‖ ≤ dTerm corner.1 corner.2 n := by
    intro n q hq
    rw [Real.norm_of_nonneg (dTerm_nonneg q.1 q.2 n)]
    rcases eq_or_ne n 0 with rfl | hn
    · simp only [dTerm_zero]
      positivity
    · have hnOne : (1 : ℝ) ≤ n := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      have hnSOne : (1 : ℝ) ≤ nS n := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (GoldenSubstitutionOrbit.nS_ne_zero n)
      have hfirst :=
        Real.rpow_le_rpow_of_exponent_le hnSOne (neg_le_neg hq.1)
      have hsecond :=
        Real.rpow_le_rpow_of_exponent_le hnOne (neg_le_neg hq.2)
      unfold dTerm
      rw [if_neg hn, if_neg hn]
      exact mul_le_mul hfirst hsecond (by positivity) (by positivity)
  have hcontinuousUpper :
      ContinuousOn (fun q : ℝ × ℝ => ∑' n, dTerm q.1 q.2 n) upper :=
    continuousOn_tsum htermContinuous hcornerSummable hdomination
  have hupperNhd : upper ∈ nhds p := by
    apply prod_mem_nhds
    · exact le_mem_nhds (by dsimp [corner]; linarith)
    · exact le_mem_nhds (by dsimp [corner]; linarith)
  exact hcontinuousUpper.continuousAt hupperNhd

end D5.S3.Analytic.Boundary.GoldenDisplacementSeriesContinuity
