/- GID: D5/S1/Deficit/GoldenPhaseDistribution
   generality: I
   mirror-B: D5/B/S1/Deficit/GoldenPhaseDistribution
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Uniform golden phases give the exact three-valued deficit frequencies and mean. -/

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.NumberTheory.Real.GoldenRatio

namespace D5.S1.Deficit.GoldenPhaseDistribution

open intervalIntegral

/-- The area below the lower diagonal threshold in the uniform phase square,
computed by its vertical cross sections. -/
noncomputable def positiveFrequency : ℝ :=
  ∫ x in (0 : ℝ)..Real.goldenRatio⁻¹, (Real.goldenRatio⁻¹ - x)

/-- The area above the upper diagonal threshold in the uniform phase square.
After reflection, its legs have length `goldenRatio⁻²`. -/
noncomputable def negativeFrequency : ℝ :=
  ∫ x in (0 : ℝ)..Real.goldenRatio⁻¹ ^ 2,
    (Real.goldenRatio⁻¹ ^ 2 - x)

/-- Uniform golden phase sampling gives positive and negative deficit frequencies
`1 / (2 * phi^2)` and `1 / (2 * phi^4)`; their signed mean is
`1 / (2 * phi^3)`. -/
theorem limiting_deficit_distribution :
    positiveFrequency = 1 / (2 * Real.goldenRatio ^ 2) ∧
    negativeFrequency = 1 / (2 * Real.goldenRatio ^ 4) ∧
    positiveFrequency - negativeFrequency = 1 / (2 * Real.goldenRatio ^ 3) := by
  have hphi : Real.goldenRatio ≠ 0 := ne_of_gt Real.goldenRatio_pos
  have hsq : Real.goldenRatio ^ 2 = Real.goldenRatio + 1 :=
    Real.goldenRatio_sq
  have hpos : positiveFrequency = Real.goldenRatio⁻¹ ^ 2 / 2 := by
    rw [positiveFrequency]
    change (∫ x in (0 : ℝ)..Real.goldenRatio⁻¹,
      (fun _ : ℝ => Real.goldenRatio⁻¹) x - id x) = _
    rw [intervalIntegral.integral_sub
      (continuous_const.intervalIntegrable _ _) (continuous_id.intervalIntegrable _ _)]
    simp
    ring
  have hneg : negativeFrequency = Real.goldenRatio⁻¹ ^ 4 / 2 := by
    rw [negativeFrequency]
    change (∫ x in (0 : ℝ)..Real.goldenRatio⁻¹ ^ 2,
      (fun _ : ℝ => Real.goldenRatio⁻¹ ^ 2) x - id x) = _
    rw [intervalIntegral.integral_sub
      (continuous_const.intervalIntegrable _ _) (continuous_id.intervalIntegrable _ _)]
    simp
    ring
  rw [hpos, hneg]
  constructor
  · field_simp
  constructor
  · field_simp
  · field_simp
    ring_nf at hsq ⊢
    nlinarith

end D5.S1.Deficit.GoldenPhaseDistribution
