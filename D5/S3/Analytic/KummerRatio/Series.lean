/- GID: D5/S3/Analytic/KummerRatio/Series
   generality: G
   mirror-B: D5/B/S3/Analytic/KummerRatio/Series
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.SpecificLimits.Normed, mathlib/module/Mathlib.Analysis.Calculus.SmoothSeries]
   utility: none
   digest: Entire Kummer series, differential equation, positivity, and parameter recurrence. -/

import D5.S3.Analytic.KummerRatio.Defs
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Calculus.SmoothSeries

open Filter Topology
open D5.S3.Analytic.KummerRatio.Defs

namespace D5.S3.Analytic.KummerRatio.Series

private lemma coeff_zero (s c : ℝ) : kummerCoeff s c 0 = 1 := by
  simp [kummerCoeff]

private lemma coeff_succ (s : ℝ) {c : ℝ} (hc : 0 < c) (n : ℕ) :
    kummerCoeff s c (n + 1) =
      ((s + n) / (c + n) / (n + 1)) * kummerCoeff s c n := by
  have hpc := (ascPochhammer_pos n c hc).ne'
  have hcn : c + (n : ℝ) ≠ 0 := by positivity
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  have hfac : (n.factorial : ℝ) ≠ 0 := by positivity
  simp only [kummerCoeff, ascPochhammer_succ_eval, Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one]
  field_simp

private lemma summable_norm_kummer (s c x : ℝ) (hc : 0 < c) :
    Summable (fun n => ‖kummerCoeff s c n * x ^ n‖) := by
  have hq : Tendsto (fun n : ℕ => ((s + n) / (c + n) / (n + 1)) * x)
      atTop (𝓝 0) := by
    have hr := tendsto_add_mul_div_add_mul_atTop_nhds s c (1 : ℝ) (d := 1) one_ne_zero
    simp only [one_mul, div_one] at hr
    simpa [div_eq_mul_inv] using
      (hr.mul tendsto_one_div_add_atTop_nhds_zero_nat).mul_const x
  apply summable_of_ratio_norm_eventually_le (r := 1 / 2) (by norm_num)
  have hqn : Tendsto (fun n : ℕ => ‖((s + n) / (c + n) / (n + 1)) * x‖) atTop (𝓝 0) := by
    simpa using hq.norm
  filter_upwards [hqn.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2)] with n hn
  simp only [norm_norm]
  rw [coeff_succ s hc, pow_succ]
  have he : ((s + (n : ℝ)) / (c + n) / (n + 1) * kummerCoeff s c n) *
      (x ^ n * x) = (((s + n) / (c + n) / (n + 1)) * x) *
      (kummerCoeff s c n * x ^ n) := by ring
  rw [he, norm_mul]
  exact mul_le_mul_of_nonneg_right hn.le (norm_nonneg _)

/-- The defining Kummer series converges for every real argument. -/
theorem summable_kummer (s c x : ℝ) (hc : 0 < c) :
    Summable (fun n => kummerCoeff s c n * x ^ n) :=
  (summable_norm_kummer s c x hc).of_norm

/-- The constant term gives the value at zero. -/
theorem kummer_zero (s c : ℝ) : kummer s c 0 = 1 := by
  simp [kummer, kummerCoeff, zero_pow_eq]

private lemma coeff_nonneg {s c : ℝ} (hs : 0 ≤ s) (hc : 0 < c) (n : ℕ) :
    0 ≤ kummerCoeff s c n := by
  apply div_nonneg _ (mul_nonneg (ascPochhammer_pos n c hc).le (by positivity))
  rcases hs.eq_or_lt with he | hp
  · rw [← he, ascPochhammer_eval_zero]
    split_ifs <;> norm_num
  · exact (ascPochhammer_pos n s hp).le

/-- Nonnegative coefficients bound the function below by its constant term. -/
theorem one_le_kummer {s c x : ℝ} (hs : 0 ≤ s) (hc : 0 < c) (hx : 0 ≤ x) :
    1 ≤ kummer s c x := by
  have h := (summable_kummer s c x hc).sum_le_tsum ({0} : Finset ℕ)
    (fun n _ => mul_nonneg (coeff_nonneg hs hc n) (pow_nonneg hx n))
  simpa [kummer, coeff_zero] using h

end D5.S3.Analytic.KummerRatio.Series
