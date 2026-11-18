/- GID: D5/S3/Arith/Robin/Analytic/OmegaSecond/PrimeExpansion
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/Analytic/OmegaSecond/PrimeExpansion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Prime-counting expansion and the exact second-threshold Rankin budget. -/

import D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Real Filter Asymptotics
open scoped Topology

namespace D5.S3.Arith.Robin.Analytic.OmegaSecond.PrimeExpansion
open D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel

/-- The three factorial terms of the real-endpoint prime count. -/
def countingThreeTerms (P : ℝ) : ℝ :=
  P / log P + P / log P ^ 2 + 2 * P / log P ^ 3

/-- The residual after the first three terms has fourth coefficient six. -/
theorem prime_counting_three_terms :
    Tendsto (fun P : ℝ =>
      (primeCount P - countingThreeTerms P) / (P / log P ^ 4))
      atTop (𝓝 6) := by
  have hi : Tendsto (fun P : ℝ => 1 / log P) atTop (𝓝 0) :=
    tendsto_log_atTop.const_div_atTop 1
  have h := (prime_counting_four_terms.mul hi).add_const 6
  norm_num only [mul_zero, zero_add] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with P hP
  dsimp only [countingPolynomial, countingThreeTerms]
  field_simp [(show P ≠ 0 by linarith), (log_pos hP).ne']
  <;> ring

/-- The budget after removing the second distinct-prime threshold at cutoff P. -/
def budget (P : ℝ) : ℝ :=
  P - Chebyshev.theta P +
    (primeCount P - (P / log P + P / log P ^ 2)) * log P

/-- The first two prime-counting coefficients cancel exactly, leaving two. -/
theorem budget_limit :
    Tendsto (fun P : ℝ => budget P / (P / log P ^ 2))
      atTop (𝓝 2) := by
  have hi : Tendsto (fun P : ℝ => 1 / log P) atTop (𝓝 0) :=
    tendsto_log_atTop.const_div_atTop 1
  have hθ := (theta_error_log_power 2).tendsto_div_nhds_zero
  have h := hθ.neg.add ((prime_counting_three_terms.mul hi).add_const 2)
  norm_num only [neg_zero, mul_zero, zero_add] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with P hP
  dsimp only [budget, countingThreeTerms]
  field_simp [(show P ≠ 0 by linarith), (log_pos hP).ne']
  <;> ring

end D5.S3.Arith.Robin.Analytic.OmegaSecond.PrimeExpansion
