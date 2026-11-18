/- GID: D5/S3/Arith/Robin/Analytic/OmegaSecond/CentralCount
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/Analytic/OmegaSecond/CentralCount
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform prime-density error on a moving central interval. -/

import D5.S3.Arith.Robin.Analytic.OmegaSecond.PrimeExpansion
import Mathlib.Analysis.Complex.ExponentialBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Real Filter Set
open scoped Topology

namespace D5.S3.Arith.Robin.Analytic.OmegaSecond.CentralCount
open D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel
open PrimeExpansion

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

end D5.S3.Arith.Robin.Analytic.OmegaSecond.CentralCount
