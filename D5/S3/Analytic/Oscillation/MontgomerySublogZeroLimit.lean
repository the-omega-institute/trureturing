/- GID: D5/S3/Analytic/Oscillation/MontgomerySublogZeroLimit
   generality: I
   mirror-B: D5/B/S3/Analytic/Oscillation/MontgomerySublogZeroLimit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The zero-frequency Montgomery sum attains the leading coefficient under sublogarithmic counting discrepancy. -/

import D5.S3.Analytic.Oscillation.MontgomerySublogCount
import D5.S3.Analytic.Oscillation.MontgomeryAlignmentLower

/-! At zero frequency every retained pair has the same phase. -/

open Filter
open scoped Topology

noncomputable section

namespace D5.S3.Analytic.Oscillation.MontgomerySublogZeroLimit

open OrdinateCounting (Spectrum)
open MontgomeryCountUpper (pairSum)
open MontgomeryWindow (montgomery_normalization)
open MontgomerySublogCount (countAsymptotic_of_sublog pairSum_le_of_sublog_discrepancy)
open MontgomeryAlignmentLower (eventually_montgomery_gt_of_phase_alignment)
open SmoothedSpectrumCounting.CutDensity (countMain)

private abbrev threshold : ℝ := 2 * Real.pi * (1 / (2 * Real.pi)) ^ 2

/-- The normalized ordered pair sum converges to the count coefficient at zero frequency. -/
theorem tendsto_pairSum_zero_of_sublog_discrepancy (S : Spectrum)
    (err : Tendsto (fun Y : ℝ => ((S.N Y : ℝ) - countMain (2 * Real.pi) Y) / Real.log Y)
      atTop (𝓝 0)) :
    Tendsto (fun Y : ℝ => pairSum S Y 0 / (Y * Real.log Y ^ 2)) atTop (𝓝 threshold) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    have h := eventually_montgomery_gt_of_phase_alignment S
      (countAsymptotic_of_sublog S err) ha
    filter_upwards [h, eventually_gt_atTop (1 : ℝ)] with Y hY hY1
    have hpos : 0 < Y * Real.log Y ^ 2 :=
      mul_pos (zero_lt_one.trans hY1) (pow_pos (Real.log_pos hY1) _)
    apply (lt_div_iff₀ hpos).2
    have h0 := hY 0 (by simp)
    rwa [← montgomery_normalization S hY1 0] at h0
  · intro b hb
    let ε := (b - threshold) / 2
    have hε : 0 < ε := by dsimp [ε]; linarith
    filter_upwards [pairSum_le_of_sublog_discrepancy S err hε,
      eventually_gt_atTop (1 : ℝ)] with Y hY hY1
    have hpos : 0 < Y * Real.log Y ^ 2 :=
      mul_pos (zero_lt_one.trans hY1) (pow_pos (Real.log_pos hY1) _)
    exact ((div_le_iff₀ hpos).2 (hY 0)).trans_lt (by dsimp [ε]; linarith)

end D5.S3.Analytic.Oscillation.MontgomerySublogZeroLimit
