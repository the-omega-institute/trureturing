/- GID: D5/S1/Words/Patterns/Separable/OccupiedLogEnvelope
   generality: G
   mirror-B: D5/B/S1/Words/Patterns/Separable/OccupiedLogEnvelope
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: One logarithmic scale bounds both actual occupation masses at every integer. -/

import D5.S1.Words.Patterns.Separable.OccupiedResidualGain
import D5.S1.Words.Patterns.Separable.OccupiedNonlinearLoss
import D5.S1.Words.Patterns.Separable.OccupiedTailComparison

/-! The compensated linear gain and the weighted quadratic cost concern the same
actual logarithmic profile. Their comparison supplies a single global scale. -/

namespace D5.S1.Words.Patterns.Separable.OccupiedLogEnvelope

open D5.S0.Asymptotics.WeightedProbability.AbsoluteDiscrepancySeries (discrepancyProfile)
open OccupiedComparison OccupiedTailComparison OccupiedResidualGain OccupiedNonlinearLoss
open OccupiedActualPowerGenerator

private theorem profile_pos (z : ℤ) : 0 < discrepancyProfile z := by
  unfold discrepancyProfile
  have h : 1 < (2 : ℝ) + |(z : ℝ)| := by linarith [abs_nonneg (z : ℝ)]
  exact one_div_pos.mpr (mul_pos (Real.sqrt_pos.mpr (by linarith)) (Real.log_pos h))

private theorem profile_le_origin (z : ℤ) : discrepancyProfile z ≤ discrepancyProfile 0 := by
  unfold discrepancyProfile
  simp only [Int.cast_zero, abs_zero, add_zero]
  have hz : (2 : ℝ) ≤ 2 + |(z : ℝ)| := by linarith [abs_nonneg (z : ℝ)]
  apply one_div_le_one_div_of_le (mul_pos (Real.sqrt_pos.mpr (by norm_num))
    (Real.log_pos (by norm_num)))
  exact mul_le_mul (Real.sqrt_le_sqrt hz) (Real.log_le_log (by norm_num) hz)
    (Real.log_nonneg (by norm_num)) (Real.sqrt_nonneg _)

/-- The raw mass and its normalization satisfy global logarithmic lower bounds
at a common positive scale, with no starting position excluded. -/
theorem actual_raw_occupation_log_envelope :
    ∃ t > (0 : ℝ), ∀ z : ℤ,
      t * discrepancyProfile z ≤ rawOccupation z ∧
      (2 / a) * t * discrepancyProfile z ≤ occupation z := by
  obtain ⟨A, hA, N, hg⟩ := eventual_discrepancy_linear_gain
  obtain ⟨hsq, _, B, hB, hl⟩ := actual_loss_convolution_bound
  have htail (z : ℤ) (hz : (N : ℤ) < |z|) :
      A * discrepancyProfile z ^ 2 ≤ ∑' n : ℕ, kernelWeight n *
        (discrepancyProfile (z + (n + 1 : ℤ)) +
          discrepancyProfile (z - (n + 1 : ℤ)) - 2 * discrepancyProfile z) := by
    simpa only [actualGenerator, Nat.cast_add, Nat.cast_one] using hg z hz
  have hcost (z : ℤ) :
      (∑' n : ℕ, (lossWeight n * discrepancyProfile (z + (n + 1 : ℤ)) ^ 2 +
        lossWeight n * discrepancyProfile (z - (n + 1 : ℤ)) ^ 2)) ≤
          B * discrepancyProfile z ^ 2 := by
    simpa only [lossConvolution, lossSummand] using hl z
  obtain ⟨t, ht, H⟩ := actual_lower_from_tail_estimates discrepancyProfile
    (discrepancyProfile 0) A B N (profile_pos 0) hA hB
    (fun z => (profile_pos z).le) profile_le_origin hsq htail (fun z _ => hcost z)
  have ha : 0 < a := by
    unfold a b
    nlinarith [Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg (2 : ℝ)]
  refine ⟨t, ht, fun z => ⟨H z, ?_⟩⟩
  simpa only [occupation, mul_assoc] using
    (mul_le_mul_of_nonneg_left (H z) (show 0 ≤ 2 / a by positivity))

#print axioms actual_raw_occupation_log_envelope

end D5.S1.Words.Patterns.Separable.OccupiedLogEnvelope
