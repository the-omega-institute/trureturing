/- GID: D5/S3/Arith/Robin/Analytic/ExceptionCount/PrimeCutoff
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/Analytic/ExceptionCount/PrimeCutoff
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A prime cutoff with enough primes and a strict inverse-logarithmic gap. -/

import D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel
import Mathlib.Analysis.Calculus.Deriv.Slope

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Real Filter Asymptotics
open scoped Topology

namespace D5.S3.Arith.Robin.Analytic.ExceptionCount.PrimeCutoff
open D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel

lemma second_order_count :
    Tendsto (fun x : ℝ => log x * (log x * primeCount x / x - 1))
      atTop (𝓝 1) := by
  have hi : Tendsto (fun x : ℝ => 1 / log x) atTop (𝓝 0) :=
    tendsto_log_atTop.const_div_atTop 1
  have he := prime_counting_four_terms.mul (hi.pow 3)
  have h := ((((tendsto_const_nhds (x := (1 : ℝ)) (f := atTop)).add (hi.const_mul 2)).add
    ((hi.pow 2).const_mul 6)).add he)
  norm_num only [mul_one, one_mul, mul_zero, zero_add, zero_div, zero_pow, add_zero, exp_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  dsimp only [countingPolynomial]
  field_simp [(show x ≠ 0 by linarith), (log_pos hx).ne']
  <;> ring

/-- The cutoff is strictly below exp(t), with a prescribed logarithmic gap. -/
def cutoff (t : ℝ) : ℝ := exp (t - 1 / (2 * t))

lemma cutoff_top : Tendsto cutoff atTop atTop := by
  have hi : Tendsto (fun t : ℝ => 1 / (2 * t)) atTop (𝓝 0) :=
    (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2)).const_div_atTop 1
  apply tendsto_exp_atTop.comp
  apply tendsto_atTop_mono' atTop ?_
    (tendsto_atTop_add_const_right atTop (-1 : ℝ) tendsto_id)
  filter_upwards [hi.eventually_lt_const (by norm_num : (0 : ℝ) < 1)] with t ht
  change t + -1 ≤ t - 1 / (2 * t)
  linarith

private lemma exponential_gap :
    Tendsto (fun t : ℝ => (exp (-1 / (2 * t)) - 1) * t) atTop (𝓝 (-(1 / 2 : ℝ))) := by
  have hi : Tendsto (fun t : ℝ => -1 / (2 * t)) atTop (𝓝 0) := by
    have h := ((tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2)).const_div_atTop 1).neg
    simpa only [id_eq, neg_zero, neg_div] using h
  have hi' : Tendsto (fun t : ℝ => -1 / (2 * t)) atTop (𝓝[<] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hi, by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      exact div_neg_of_neg_of_pos (by norm_num : (-1 : ℝ) < 0) (by positivity)⟩
  have h := (hasDerivAt_exp (0 : ℝ)).tendsto_slope_zero_left.comp hi'
  have h' := h.mul_const (-(1 / 2 : ℝ))
  simp only [exp_zero, one_mul, smul_eq_mul, zero_add, Function.comp_def] at h'
  apply h'.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  field_simp [ht.ne']
  <;> ring

private lemma cutoff_ratio :
    Tendsto (fun t : ℝ => t / (t - 1 / (2 * t))) atTop (𝓝 1) := by
  have hi : Tendsto (fun t : ℝ => 1 / t) atTop (𝓝 0) :=
    tendsto_id.const_div_atTop 1
  have h := (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop)).div
    ((tendsto_const_nhds (x := (1 : ℝ)) (f := atTop)).sub ((hi.pow 2).div_const 2)) (by norm_num : (1 : ℝ) - 0 ^ 2 / 2 ≠ 0)
  norm_num only [mul_one, one_mul, mul_zero, zero_add, zero_div, zero_pow, add_zero, exp_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
  have hd : t - 1 / (2 * t) ≠ 0 := by
    have : 1 / (2 * t) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
    linarith
  dsimp only [Pi.div_apply, Pi.sub_apply, Pi.mul_apply]
  field_simp [ht.ne', hd]
  <;> ring

/-- There are eventually more than exp(t)/t primes below the cutoff. -/
theorem enough_primes :
    ∀ᶠ t : ℝ in atTop, exp t / t ≤ primeCount (cutoff t) := by
  have hi : Tendsto (fun t : ℝ => 1 / t) atTop (𝓝 0) :=
    tendsto_id.const_div_atTop 1
  have hg : Tendsto (fun t : ℝ => exp (-1 / (2 * t))) atTop (𝓝 1) := by
    have h := ((hi.div_const 2).neg).rexp
    norm_num only [mul_one, one_mul, mul_zero, zero_add, zero_div, zero_pow, add_zero, exp_zero] at h
    convert h using 1
    ext t
    congr 1
    ring
  have hs := second_order_count.comp cutoff_top
  have he : Tendsto (fun t : ℝ =>
      t * (primeCount (cutoff t) / (exp t / t) - 1)) atTop (𝓝 (1 / 2 : ℝ)) := by
    have hsmall := (((hi.div_const 2).mul cutoff_ratio).mul hg)
    have h := ((exponential_gap.add hsmall).add
      ((hs.mul (cutoff_ratio.pow 2)).mul hg))
    norm_num only [mul_one, one_mul, mul_zero, zero_add, zero_div, zero_pow, add_zero, exp_zero] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
    have hd : t - 1 / (2 * t) ≠ 0 := by
      have : 1 / (2 * t) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
      linarith
    simp only [cutoff, log_exp, Function.comp_def]
    have he : exp (t - 1 / (2 * t)) = exp t * exp (-1 / (2 * t)) := by
      rw [sub_eq_add_neg, exp_add]
      congr 1
      ring
    rw [he]
    have hden : -1 + t ^ 2 * 2 ≠ 0 := by nlinarith
    field_simp [ht.ne', hd, hden, exp_ne_zero t, exp_ne_zero (-1 / (2 * t))]
    <;> ring
    all_goals field_simp [hden] <;> ring
  filter_upwards [he.eventually_const_lt (by norm_num : (0 : ℝ) < 1 / 2),
    eventually_gt_atTop (1 : ℝ)] with t ht ht1
  have hratio : 1 < primeCount (cutoff t) / (exp t / t) := by
    have := (mul_pos_iff.mp ht)
    rcases this with h | h
    · linarith [h.2]
    · linarith [h.1]
  have hh := ((lt_div_iff₀ (div_pos (exp_pos _) (by linarith))).mp hratio)
  simpa only [one_mul] using hh.le

end D5.S3.Arith.Robin.Analytic.ExceptionCount.PrimeCutoff
