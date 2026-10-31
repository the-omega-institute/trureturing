/- GID: D5/S3/Analytic/XuYangMillsRemainder/NormalizedRemainderOrders
   generality: G
   mirror-B: D5/B/S3/Analytic/XuYangMillsRemainder/NormalizedRemainderOrders
   mirror-E: none(waiver:kernel-checked-analytic-proof-no-external-evidence)
   anchors: [mathlib/module/Mathlib.Analysis.Calculus.Taylor]
   utility: none
   digest: Both strict normalized exponential-remainder orders. -/

import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import D5.S3.Analytic.XuYangMillsRemainder.Result

open Set Filter Real MeasureTheory
open scoped Topology ContDiff
noncomputable section

namespace D5.S3.Analytic.XuYangMillsRemainder.GeneralParameter

open D5.S3.Analytic.XuYangMillsRemainder.Result

/-! Signed finite exponential remainders: the two required multiplier orders. -/

theorem normalized_exp_remainder (r : ℕ) {y : ℝ} (hy : 0 < y) :
    (-1 : ℝ) ^ (r + 1) * D5.S3.Analytic.ExpRemainderDifferences.R r (-y) /
      y ^ (r + 1) =
      (∫ s in (0 : ℝ)..1, (1 - s) ^ r * exp (-s * y)) / r.factorial := by
  have hc : ContDiff ℝ (r + 1 : ℕ) exp := contDiff_exp.of_le (by exact_mod_cast le_top)
  have he (j : ℕ) : iteratedDeriv j exp = exp := by
    simpa using iteratedDeriv_exp_const_mul j 1
  have ht := taylor_integral_remainder (x := -y) (x₀ := 0) hc.contDiffOn
  have hpoly : taylorWithinEval exp r (uIcc 0 (-y)) 0 (-y) =
      ∑ j ∈ Finset.range (r + 1), (-y) ^ j / j.factorial := by
    rw [taylor_within_apply]
    apply Finset.sum_congr rfl
    intro j hj
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc (by linarith : (0 : ℝ) ≠ -y))
      ((contDiff_exp : ContDiff ℝ ω exp).of_le (by exact_mod_cast le_top)).contDiffAt
      left_mem_uIcc]
    simp [he, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [hpoly] at ht
  have hrepr : D5.S3.Analytic.ExpRemainderDifferences.R r (-y) =
      ∫ t in (0 : ℝ)..(-y), ((-y - t) ^ r / r.factorial) * exp t := by
    unfold D5.S3.Analytic.ExpRemainderDifferences.R
    rw [ht]
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc (by linarith : (0 : ℝ) ≠ -y))
      hc.contDiffAt ht]
    simp [he, smul_eq_mul]
  have hsub := intervalIntegral.smul_integral_comp_mul_right
    (fun t : ℝ => ((-y - t) ^ r / r.factorial) * exp t)
    (a := (0 : ℝ)) (b := 1) (-y)
  have hpoint (s : ℝ) : ((-y - s * -y) ^ r / r.factorial) * exp (s * -y) =
      ((-y) ^ r / r.factorial) * ((1 - s) ^ r * exp (-s * y)) := by
    rw [show -y - s * -y = -y * (1 - s) by ring, mul_pow,
      show s * -y = -s * y by ring]
    ring
  simp only [zero_mul, one_mul, smul_eq_mul, hpoint,
    intervalIntegral.integral_const_mul] at hsub
  rw [hrepr, ← hsub]
  have hsgn : (-1 : ℝ) ^ (r + 1) * (-y) ^ (r + 1) = y ^ (r + 1) := by
    rw [← mul_pow]
    congr 1
    ring
  have hy0 : y ≠ 0 := hy.ne'
  let J : ℝ := ∫ s in (0 : ℝ)..1, (1 - s) ^ r * exp (-s * y)
  change (-1 : ℝ) ^ (r + 1) * (-y * ((-y) ^ r / r.factorial * J)) /
    y ^ (r + 1) = J / r.factorial
  have hnum : (-1 : ℝ) ^ (r + 1) * (-y * ((-y) ^ r / r.factorial * J)) =
      y ^ (r + 1) * (J / r.factorial) := by
    calc
      _ = ((-1 : ℝ) ^ (r + 1) * (-y) ^ (r + 1)) * (J / r.factorial) := by
        rw [pow_succ (-y)]
        ring
      _ = _ := by rw [hsgn]
  rw [hnum, mul_div_cancel_left₀ _ (pow_ne_zero _ hy0)]

theorem exp_remainder_ratio_strict_anti (r : ℕ) :
    StrictAntiOn (fun y : ℝ =>
      (-1 : ℝ) ^ (r + 1) * D5.S3.Analytic.ExpRemainderDifferences.R r (-y) /
        y ^ (r + 1)) (Ioi 0) := by
  intro y hy z hz hyz
  dsimp only
  rw [normalized_exp_remainder r hy, normalized_exp_remainder r hz]
  apply div_lt_div_of_pos_right _ (by positivity : (0 : ℝ) < r.factorial)
  apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (by norm_num : (0 : ℝ) < 1) (by fun_prop) (by fun_prop)
  · intro s hs
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by linarith [hs.2]) _)
    apply exp_le_exp.mpr
    nlinarith [hs.1]
  · refine ⟨1 / 2, by norm_num, ?_⟩
    apply mul_lt_mul_of_pos_left _ (by positivity : (0 : ℝ) < (1 - 1 / 2) ^ r)
    apply exp_lt_exp.mpr
    linarith

private theorem lower_normalized_exp_remainder (r : ℕ) {y : ℝ} (hy : 0 < y) :
    (-1 : ℝ) ^ (r + 1) * D5.S3.Analytic.ExpRemainderDifferences.R r (-y) /
      y ^ r =
      (∫ q in (0 : ℝ)..y, (1 - q / y) ^ r * exp (-q)) / r.factorial := by
  have h := normalized_exp_remainder r hy
  have hsub := intervalIntegral.smul_integral_comp_mul_right
    (fun q : ℝ => (1 - q / y) ^ r * exp (-q))
    (a := (0 : ℝ)) (b := 1) y
  simp only [zero_mul, one_mul, smul_eq_mul, mul_div_cancel_right₀ _ hy.ne'] at hsub
  rw [← hsub]
  have hy0 : y ≠ 0 := hy.ne'
  have hf : (r.factorial : ℝ) ≠ 0 := by positivity
  field_simp at h ⊢
  rw [pow_succ] at h
  linear_combination h

theorem exp_remainder_ratio_strict_mono (r : ℕ) :
    StrictMonoOn (fun y : ℝ =>
      (-1 : ℝ) ^ (r + 1) * D5.S3.Analytic.ExpRemainderDifferences.R r (-y) /
        y ^ r) (Ioi 0) := by
  intro y hy z hz hyz
  dsimp only
  rw [lower_normalized_exp_remainder r hy, lower_normalized_exp_remainder r hz]
  apply div_lt_div_of_pos_right _ (by positivity : (0 : ℝ) < r.factorial)
  have hmono : (∫ q in (0 : ℝ)..y, (1 - q / y) ^ r * exp (-q)) ≤
      ∫ q in (0 : ℝ)..y, (1 - q / z) ^ r * exp (-q) := by
    apply intervalIntegral.integral_mono_on hy.le (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop)
    intro q hq
    apply mul_le_mul_of_nonneg_right _ (exp_nonneg _)
    apply pow_le_pow_left₀
    · exact sub_nonneg.mpr ((div_le_one hy).mpr hq.2)
    · have hdiv : q / z ≤ q / y := div_le_div_of_nonneg_left hq.1 (by exact hy) hyz.le
      linarith
  have htail : 0 < ∫ q in y..z, (1 - q / z) ^ r * exp (-q) := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on
      (by apply Continuous.intervalIntegrable; fun_prop) _ hyz
    intro q hq
    exact mul_pos (pow_pos (sub_pos.mpr ((div_lt_one hz).mpr hq.2)) _) (exp_pos _)
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (show IntervalIntegrable (fun q : ℝ => (1 - q / z) ^ r * exp (-q)) volume 0 y by
      apply Continuous.intervalIntegrable; fun_prop)
    (show IntervalIntegrable (fun q : ℝ => (1 - q / z) ^ r * exp (-q)) volume y z by
      apply Continuous.intervalIntegrable; fun_prop)
  linarith

end D5.S3.Analytic.XuYangMillsRemainder.GeneralParameter
