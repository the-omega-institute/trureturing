/- GID: D5/S3/Arith/Robin/Analytic/OmegaSecond/PrimeExpansion
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/Analytic/OmegaSecond/PrimeExpansion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Prime-counting expansion and the exact second-threshold Rankin budget. -/

import D5.S3.Arith.Robin.Analytic.ExceptionCount.PrimeCutoff
import Mathlib.Analysis.Complex.ExponentialBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Real Filter Asymptotics Set
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

private lemma prime_counting_error_limit :
    Tendsto (fun P : ℝ =>
      (primeCount P - P / log P) / (P / log P ^ 2))
      atTop (𝓝 1) := by
  apply D5.S3.Arith.Robin.Analytic.ExceptionCount.PrimeCutoff.second_order_count.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with P hP
  field_simp [(show P ≠ 0 by linarith), (log_pos hP).ne']
  <;> ring

/-- A uniform eventual error bound for comparison on moving prime intervals. -/
theorem prime_counting_error_bound :
    ∀ᶠ P : ℝ in atTop,
      |primeCount P - P / log P| ≤ 3 * (P / log P ^ 2) := by
  have h := prime_counting_error_limit.abs
  norm_num only [abs_one] at h
  filter_upwards [h.eventually_lt_const (by norm_num : (1 : ℝ) < 3),
    eventually_gt_atTop (1 : ℝ)] with P hbound hP
  have hscale : 0 < P / log P ^ 2 := div_pos (by linarith) (sq_pos_of_pos (log_pos hP))
  rw [abs_div, abs_of_pos hscale] at hbound
  exact ((div_lt_iff₀ hscale).mp hbound).le

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

/-- The real prime count has almost constant density on the central interval.
The bound is uniform in the moving endpoint t, including both boundaries. -/
theorem central_prime_counting_bound :
    ∀ᶠ P : ℝ in atTop, ∀ t ∈ Icc (P / 2) (2 * P),
      |primeCount t - t / log P| ≤ 28 * (P / log P ^ 2) := by
  obtain ⟨X, hX⟩ := eventually_atTop.mp prime_counting_error_bound
  filter_upwards [eventually_ge_atTop (2 * max X 1),
    tendsto_log_atTop.eventually_ge_atTop 2] with P hP hlogP
  intro t ht
  have hP0 : 0 < P := by linarith [le_max_right X 1]
  have ht0 : 0 < t := by linarith [ht.1]
  have htX : X ≤ t := by linarith [le_max_left X 1, ht.1]
  have hl0 : 0 < log P := by linarith
  have hlog2 : log (2 : ℝ) < 1 := by linarith [log_two_lt_d9]
  have hloglo : log P - 1 ≤ log t := by
    have h := log_le_log (by positivity : 0 < P / 2) ht.1
    rw [log_div hP0.ne' (by norm_num : (2 : ℝ) ≠ 0)] at h
    linarith
  have hloghi : log t ≤ log P + 1 := by
    have h := log_le_log ht0 ht.2
    rw [log_mul (by norm_num : (2 : ℝ) ≠ 0) hP0.ne'] at h
    linarith
  have htlog : 0 < log t := by linarith
  have hhalf : log P / 2 ≤ log t := by linarith
  have hsq : log P ^ 2 / 4 ≤ log t ^ 2 := by nlinarith
  have hprod : log P ^ 2 / 2 ≤ log t * log P := by nlinarith
  have habs : |log P - log t| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have herror : |primeCount t - t / log t| ≤ 24 * (P / log P ^ 2) := by
    refine (hX t htX).trans ?_
    calc
      3 * (t / log t ^ 2) ≤ 3 * ((2 * P) / (log P ^ 2 / 4)) := by
        gcongr
        exact ht.2
      _ = 24 * (P / log P ^ 2) := by ring
  have hchange : |t / log t - t / log P| ≤ 4 * (P / log P ^ 2) := by
    have hid : t / log t - t / log P =
        t * (log P - log t) / (log t * log P) := by
      field_simp [htlog.ne', hl0.ne']
      <;> ring
    rw [hid, abs_div, abs_mul, abs_of_pos ht0,
      abs_of_pos (mul_pos htlog hl0)]
    calc
      t * |log P - log t| / (log t * log P) ≤
          (2 * P) / (log P ^ 2 / 2) := by
        apply div_le_div₀ (by positivity)
        · simpa only [mul_one] using
            mul_le_mul ht.2 habs (abs_nonneg _) (by positivity : 0 ≤ 2 * P)
        · positivity
        · exact hprod
      _ = 4 * (P / log P ^ 2) := by ring
  calc
    |primeCount t - t / log P| ≤
        |primeCount t - t / log t| + |t / log t - t / log P| :=
      abs_sub_le _ _ _
    _ ≤ 24 * (P / log P ^ 2) + 4 * (P / log P ^ 2) :=
      add_le_add herror hchange
    _ = _ := by ring


end D5.S3.Arith.Robin.Analytic.OmegaSecond.PrimeExpansion
