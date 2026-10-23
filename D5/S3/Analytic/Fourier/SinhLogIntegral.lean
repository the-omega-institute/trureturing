/- GID: D5/S3/Analytic/Fourier/SinhLogIntegral
   generality: G
   mirror-B: D5/B/S3/Analytic/Fourier/SinhLogIntegral
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp, mathlib/module/Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds, mathlib/module/Mathlib.Analysis.Convex.SpecificFunctions.Basic, mathlib/module/Mathlib.Analysis.SpecialFunctions.ImproperIntegrals, mathlib/module/Mathlib.Analysis.SpecialFunctions.Integrals.Basic, mathlib/module/Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd, mathlib/module/Mathlib.MeasureTheory.Integral.Prod, mathlib/module/Mathlib.MeasureTheory.Integral.DominatedConvergence]
   utility: none
   digest: The logarithmic integral of normalized hyperbolic sine and comparison of its positive densities. -/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Logarithmic integrals and parameter comparisons for normalized hyperbolic sine. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace D5.S3.Analytic.Fourier.SinhLogIntegral

/-- Normalized hyperbolic sine, with its removable singularity filled. -/
def E (a t : ℝ) : ℝ := if t = 0 then 1 else Real.sinh (a * t) / (a * t)

/-- The positive half-line density in the logarithmic representation. -/
def h (a s : ℝ) : ℝ := 1 / (Real.exp (Real.pi * s / a) - 1)

lemma h_pos {a s : ℝ} (ha : 0 < a) (hs : 0 < s) : 0 < h a s := by
  exact one_div_pos.mpr (sub_pos.mpr (Real.one_lt_exp_iff.mpr
    (div_pos (mul_pos Real.pi_pos hs) ha)))

/-- Increasing the scale increases the density at least in proportion to that scale. -/
theorem h_scale_le {a b s : ℝ} (ha : 0 < a) (hab : a ≤ b) (hs : 0 < s) :
    (b / a) * h a s ≤ h b s := by
  have hb := ha.trans_le hab
  have hr : 0 ≤ a / b := (div_pos ha hb).le
  have hr1 : a / b ≤ 1 := (div_le_one hb).mpr hab
  have hc := convexOn_exp.2 (mem_univ (0 : ℝ)) (mem_univ (Real.pi * s / a))
    (sub_nonneg.mpr hr1) hr (by ring : 1 - a / b + a / b = 1)
  have hid : (1 - a / b) * 0 + (a / b) * (Real.pi * s / a) =
      Real.pi * s / b := by field_simp; ring
  simp only [smul_eq_mul, hid, Real.exp_zero, mul_one] at hc
  have hd : 0 < Real.exp (Real.pi * s / a) - 1 := by
    exact sub_pos.mpr (Real.one_lt_exp_iff.mpr (by positivity))
  have he : 0 < Real.exp (Real.pi * s / b) - 1 := by
    exact sub_pos.mpr (Real.one_lt_exp_iff.mpr (by positivity))
  unfold h
  have hden : Real.exp (Real.pi * s / b) - 1 ≤
      a / b * (Real.exp (Real.pi * s / a) - 1) := by linarith
  have hm := mul_le_mul_of_nonneg_left hden hb.le
  have hm' : b * (Real.exp (Real.pi * s / b) - 1) ≤
      a * (Real.exp (Real.pi * s / a) - 1) := by
    convert hm using 1 <;> field_simp
  apply (le_div_iff₀ he).mpr
  field_simp
  nlinarith

lemma E_pos {a : ℝ} (ha : 0 < a) (t : ℝ) : 0 < E a t := by
  unfold E
  split_ifs with ht
  · norm_num
  · have hx := mul_ne_zero ha.ne' ht
    rcases lt_or_gt_of_ne hx with hx | hx
    · exact div_pos_of_neg_of_neg (Real.sinh_neg_iff.mpr hx) hx
    · exact div_pos (Real.sinh_pos_iff.mpr hx) hx

private lemma euler_sinh (x : ℝ) (hx : x ≠ 0) :
    Tendsto (fun N : ℕ => ∏ n ∈ Finset.range N,
      (1 + x ^ 2 / (Real.pi ^ 2 * ((n : ℝ) + 1) ^ 2)))
      atTop (𝓝 (Real.sinh x / x)) := by
  have H := Complex.tendsto_euler_sin_prod (((x / Real.pi : ℝ) : ℂ) * Complex.I)
  have hp (n : ℕ) :
      1 - (((x / Real.pi : ℝ) : ℂ) * Complex.I) ^ 2 / ((n : ℂ) + 1) ^ 2 =
        ((1 + x ^ 2 / (Real.pi ^ 2 * ((n : ℝ) + 1) ^ 2) : ℝ) : ℂ) := by
    push_cast
    rw [mul_pow, Complex.I_sq]
    field_simp
    <;> ring
  simp_rw [hp] at H
  have hpi : (Real.pi : ℂ) * (((x / Real.pi : ℝ) : ℂ) * Complex.I) =
      (x : ℂ) * Complex.I := by
    push_cast
    field_simp
  rw [hpi, Complex.sin_mul_I, ← Complex.ofReal_sinh] at H
  simp_rw [← Complex.ofReal_prod] at H
  have HH : Tendsto (fun N : ℕ => x * ∏ n ∈ Finset.range N,
      (1 + x ^ 2 / (Real.pi ^ 2 * ((n : ℝ) + 1) ^ 2)))
      atTop (𝓝 (Real.sinh x)) := by
    simpa only [Function.comp_def, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul, mul_zero, mul_one, add_zero,
      zero_add] using (Complex.continuous_im.tendsto _).comp H
  simpa only [mul_div_cancel_left₀ _ hx] using HH.div_const x

private lemma log_E_sum {a : ℝ} (ha : 0 < a) (t : ℝ) :
    HasSum (fun n : ℕ => Real.log
      (1 + (a * t) ^ 2 / (Real.pi ^ 2 * ((n : ℝ) + 1) ^ 2)))
      (Real.log (E a t)) := by
  have hp (n : ℕ) : 0 < 1 + (a * t) ^ 2 /
      (Real.pi ^ 2 * ((n : ℝ) + 1) ^ 2) := by positivity
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun n => Real.log_nonneg (by
    have hn : 0 ≤ (a * t) ^ 2 / (Real.pi ^ 2 * ((n : ℝ) + 1) ^ 2) := by positivity
    linarith)) _).mpr
  have HH : Tendsto (fun N : ℕ => ∏ n ∈ Finset.range N,
      (1 + (a * t) ^ 2 / (Real.pi ^ 2 * ((n : ℝ) + 1) ^ 2)))
      atTop (𝓝 (E a t)) := by
    by_cases ht : t = 0
    · subst t
      simp [E]
    · simpa only [E, ite_eq_right ht] using euler_sinh (a * t) (mul_ne_zero ha.ne' ht)
  convert (Real.continuousAt_log (E_pos ha t).ne').tendsto.comp HH using 1
  ext N
  exact (Real.log_prod (fun n _ => (hp n).ne')).symm

private lemma laplace_sin {b : ℝ} (hb : 0 < b) (u : ℝ) :
    (∫ s in Ioi (0 : ℝ), Real.exp (-b * s) * Real.sin (u * s)) =
      u / (b ^ 2 + u ^ 2) := by
  have hi := integrableOn_exp_mul_complex_Ioi
    (a := (-(b : ℂ) + (u : ℂ) * Complex.I)) (by simpa using neg_neg_of_pos hb) 0
  have he := integral_exp_mul_complex_Ioi
    (a := (-(b : ℂ) + (u : ℂ) * Complex.I)) (by simpa using neg_neg_of_pos hb) 0
  calc
    _ = ∫ s in Ioi (0 : ℝ),
        (Complex.exp ((-(b : ℂ) + (u : ℂ) * Complex.I) * s)).im := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro s _
      change _ = (Complex.exp _).im
      rw [show (-(b : ℂ) + (u : ℂ) * Complex.I) * s =
        ((-b * s : ℝ) : ℂ) + ((u * s : ℝ) : ℂ) * Complex.I by push_cast; ring]
      rw [Complex.exp_add_mul_I]
      rw [← Complex.ofReal_exp, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      simp only [Complex.mul_im, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_one, mul_zero, zero_mul, add_zero, zero_add]
    _ = (∫ s in Ioi (0 : ℝ),
        Complex.exp ((-(b : ℂ) + (u : ℂ) * Complex.I) * s)).im := by
      exact integral_im hi
    _ = u / (b ^ 2 + u ^ 2) := by
      rw [he]
      simp [Complex.normSq, sq, neg_div]

private lemma laplace_sin_prod_integrable {b : ℝ} (hb : 0 < b) (t : ℝ) :
    Integrable (fun p : ℝ × ℝ => Real.exp (-b * p.2) * Real.sin (p.1 * p.2))
      ((volume.restrict (uIoc 0 t)).prod (volume.restrict (Ioi 0))) := by
  have hd := (intervalIntegrable_const (c := (1 : ℝ)) (a := 0) (b := t) (μ := volume)).def'.mul_prod
    (integrableOn_exp_mul_Ioi (neg_neg_of_pos hb) 0)
  refine hd.mono' (by fun_prop) (Filter.Eventually.of_forall fun p => ?_)
  simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), one_mul]
  exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_sin_le_one _)

private lemma laplace_sin_interval (b t s : ℝ) (hs : 0 < s) :
    (∫ u in 0..t, Real.exp (-b * s) * Real.sin (u * s)) =
      (1 - Real.cos (t * s)) * Real.exp (-b * s) / s := by
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_right _ hs.ne', integral_sin]
  simp only [zero_mul, Real.cos_zero, smul_eq_mul]
  ring

private lemma laplace_log_integrable {b : ℝ} (hb : 0 < b) (t : ℝ) :
    IntegrableOn (fun s => (1 - Real.cos (t * s)) * Real.exp (-b * s) / s)
      (Ioi 0) := by
  have hi := (laplace_sin_prod_integrable hb t).integral_prod_right
  have hi' : Integrable (fun s => ∫ u in 0..t,
      Real.exp (-b * s) * Real.sin (u * s)) (volume.restrict (Ioi 0)) := by
    simpa only [intervalIntegral.intervalIntegral_eq_integral_uIoc, smul_eq_mul]
      using hi.const_mul (if 0 ≤ t then (1 : ℝ) else -1)
  exact hi'.congr (ae_restrict_mem measurableSet_Ioi |>.mono fun s hs =>
    laplace_sin_interval b t s hs)

private lemma laplace_log {b : ℝ} (hb : 0 < b) (t : ℝ) :
    2 * (∫ s in Ioi (0 : ℝ),
      (1 - Real.cos (t * s)) * Real.exp (-b * s) / s) =
        Real.log (1 + t ^ 2 / b ^ 2) := by
  have hs := intervalIntegral_integral_swap (f := fun u s : ℝ =>
    Real.exp (-b * s) * Real.sin (u * s)) (laplace_sin_prod_integrable hb t)
  have he : (∫ u in 0..t, u / (b ^ 2 + u ^ 2)) =
      ∫ s in Ioi (0 : ℝ), (1 - Real.cos (t * s)) * Real.exp (-b * s) / s := by
    calc
      _ = ∫ u in 0..t, ∫ s in Ioi (0 : ℝ),
          Real.exp (-b * s) * Real.sin (u * s) := by
        congr 1; ext u; exact (laplace_sin hb u).symm
      _ = _ := hs.trans (setIntegral_congr_fun measurableSet_Ioi
        fun s hs => laplace_sin_interval b t s hs)
  rw [← he, integral_id_div_sq_add_sq hb.ne']
  have hb2 : b ^ 2 ≠ 0 := pow_ne_zero _ hb.ne'
  rw [show 1 + t ^ 2 / b ^ 2 = (b ^ 2 + t ^ 2) / b ^ 2 by field_simp]
  rw [Real.log_div (by positivity) hb2]
  simp only [zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, add_zero]
  ring

private lemma h_bound_zero {a s : ℝ} (ha : 0 < a) (hs : 0 < s) :
    h a s ≤ a / (Real.pi * s) := by
  have hc : 0 < Real.pi * s / a := by positivity
  have he : Real.pi * s / a ≤ Real.exp (Real.pi * s / a) - 1 := by
    linarith [Real.add_one_le_exp (Real.pi * s / a)]
  calc
    h a s ≤ 1 / (Real.pi * s / a) := one_div_le_one_div_of_le hc he
    _ = a / (Real.pi * s) := by field_simp

lemma h_exp (a s : ℝ) :
    h a s = Real.exp (-(Real.pi / a) * s) /
      (1 - Real.exp (-(Real.pi / a) * s)) := by
  have hmul : -(Real.pi / a) * s = -(Real.pi * s / a) := by ring
  rw [hmul, Real.exp_neg]
  unfold h
  field_simp

private lemma h_bound_infty {a s : ℝ} (ha : 0 < a) (hs : 1 ≤ s) :
    h a s ≤ (1 / (1 - Real.exp (-(Real.pi / a)))) *
      Real.exp (-(Real.pi / a) * s) := by
  have hc : 0 < Real.pi / a := by positivity
  have he : Real.exp (-(Real.pi / a)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hm : Real.exp (-(Real.pi / a) * s) ≤ Real.exp (-(Real.pi / a)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  rw [h_exp a s]
  calc
    _ ≤ Real.exp (-(Real.pi / a) * s) / (1 - Real.exp (-(Real.pi / a))) :=
      div_le_div_of_nonneg_left (Real.exp_pos _).le (by linarith) (by linarith)
    _ = _ := by ring

/-- The density satisfies the half-line Levy integrability condition. -/
theorem integrable_levyWeight {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun s => min 1 (s ^ 2) * h a s / s) (Ioi 0) := by
  have hnn {s : ℝ} (hs : 0 < s) : 0 ≤ min 1 (s ^ 2) * h a s / s := by
    exact div_nonneg (mul_nonneg (le_min (by norm_num) (sq_nonneg s))
      (h_pos ha hs).le) hs.le
  have hsmall : IntegrableOn (fun s => min 1 (s ^ 2) * h a s / s) (Ioc 0 1) := by
    refine (integrableOn_const (μ := volume) (s := Ioc (0 : ℝ) 1) (C := a / Real.pi)
      (by simp)).mono' (by apply Measurable.aestronglyMeasurable; unfold h; fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn hs.1)]
    calc
      _ ≤ s ^ 2 * (a / (Real.pi * s)) / s := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul (min_le_right _ _) (h_bound_zero ha hs.1)
            (h_pos ha hs.1).le (sq_nonneg s)) hs.1.le
      _ = a / Real.pi := by field_simp [hs.1.ne']
  have hlarge : IntegrableOn (fun s => min 1 (s ^ 2) * h a s / s) (Ioi 1) := by
    refine ((integrableOn_exp_mul_Ioi (a := -(Real.pi / a)) (neg_neg_of_pos (div_pos Real.pi_pos ha)) 1).const_mul
      (1 / (1 - Real.exp (-(Real.pi / a))))).mono' (by apply Measurable.aestronglyMeasurable; unfold h; fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    change 1 < s at hs
    have hs0 : 0 < s := by linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn hs0)]
    calc
      _ ≤ h a s := by
        apply (div_le_iff₀ hs0).mpr
        have hm := mul_le_mul_of_nonneg_right (min_le_left (1 : ℝ) (s ^ 2))
          (h_pos ha hs0).le
        nlinarith [h_pos ha hs0]
      _ ≤ _ := h_bound_infty ha hs.le
  simpa only [Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)]
    using hsmall.union hlarge

/-- Every cosine deficit is absolutely integrable against the logarithmic density. -/
theorem integrable_logIntegrand {a : ℝ} (ha : 0 < a) (t : ℝ) :
    IntegrableOn (fun s => (1 - Real.cos (t * s)) * h a s / s) (Ioi 0) := by
  refine ((integrable_levyWeight ha).const_mul (t ^ 2 + 2)).mono'
    (by apply Measurable.aestronglyMeasurable; unfold h; fun_prop) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  change 0 < s at hs
  have hh := (h_pos ha hs).le
  have hd : 0 ≤ 1 - Real.cos (t * s) := sub_nonneg.mpr (Real.cos_le_one _)
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (mul_nonneg hd hh) hs.le)]
  have hcos : 1 - Real.cos (t * s) ≤ (t ^ 2 + 2) * min 1 (s ^ 2) := by
    rcases le_total 1 (s ^ 2) with hh | hh
    · rw [min_eq_left hh]
      nlinarith [Real.neg_one_le_cos (t * s), sq_nonneg t]
    · rw [min_eq_right hh]
      have H := Real.one_sub_sq_div_two_le_cos (x := t * s)
      nlinarith [sq_nonneg t, sq_nonneg s]
  calc
    _ ≤ ((t ^ 2 + 2) * min 1 (s ^ 2)) * h a s / s := by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcos hh) hs.le
    _ = _ := by ring

def rate (a : ℝ) (n : ℕ) : ℝ := Real.pi * ((n : ℝ) + 1) / a

private lemma rate_pos {a : ℝ} (ha : 0 < a) (n : ℕ) : 0 < rate a n := by
  unfold rate
  positivity

lemma hasSum_h {a s : ℝ} (ha : 0 < a) (hs : 0 < s) :
    HasSum (fun n : ℕ => Real.exp (-(rate a n) * s)) (h a s) := by
  have hc : 0 < Real.pi / a := by positivity
  have H := (hasSum_geometric_of_lt_one (Real.exp_pos (-(Real.pi / a) * s)).le
    (Real.exp_lt_one_iff.mpr (by nlinarith : -(Real.pi / a) * s < 0))).mul_right
      (Real.exp (-(Real.pi / a) * s))
  convert H using 1
  · ext n
    rw [show -(rate a n) * s = (n : ℝ) * (-(Real.pi / a) * s) +
      (-(Real.pi / a) * s) by unfold rate; ring, Real.exp_add, Real.exp_nat_mul]
  · rw [h_exp a s]
    ring

private def term (a t : ℝ) (n : ℕ) (s : ℝ) : ℝ :=
  (1 - Real.cos (t * s)) * Real.exp (-(rate a n) * s) / s

private lemma term_nonneg (a t : ℝ) (n : ℕ) {s : ℝ} (hs : 0 < s) :
    0 ≤ term a t n s := by
  unfold term
  exact div_nonneg (mul_nonneg (sub_nonneg.mpr (Real.cos_le_one _))
    (Real.exp_pos _).le) hs.le

private lemma hasSum_term {a s : ℝ} (ha : 0 < a) (hs : 0 < s) (t : ℝ) :
    HasSum (fun n => term a t n s) ((1 - Real.cos (t * s)) * h a s / s) := by
  convert (hasSum_h ha hs).mul_left ((1 - Real.cos (t * s)) / s) using 1
  · funext n; dsimp only [term]; ring
  · ring

/-- The logarithm of normalized hyperbolic sine is the cosine-deficit integral. -/
theorem log_E_eq_integral {a : ℝ} (ha : 0 < a) (t : ℝ) :
    Real.log (E a t) =
      2 * ∫ s in Ioi (0 : ℝ), (1 - Real.cos (t * s)) * h a s / s := by
  let μ := volume.restrict (Ioi (0 : ℝ))
  have hti (n : ℕ) : Integrable (term a t n) μ :=
    laplace_log_integrable (rate_pos ha n) t
  have hnn (n : ℕ) : ∀ᵐ s ∂μ, ‖term a t n s‖ ≤ term a t n s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact le_of_eq (Real.norm_of_nonneg (term_nonneg a t n hs))
  have hint : Integrable (fun s => ∑' n, term a t n s) μ := by
    refine (integrable_logIntegrand ha t).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (hasSum_term ha hs t).tsum_eq.symm
  have H := hasSum_integral_of_dominated_convergence (μ := μ) (term a t)
    (fun n => (hti n).aestronglyMeasurable) hnn
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
        exact (hasSum_term ha hs t).summable)
    hint
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
        exact hasSum_term ha hs t)
  have H2 := H.mul_left 2
  have Hlog := log_E_sum ha t
  apply HasSum.unique Hlog
  convert H2 using 1
  ext n
  change Real.log (1 + (a * t) ^ 2 / (Real.pi ^ 2 * ((n : ℝ) + 1) ^ 2)) =
    2 * ∫ s in Ioi (0 : ℝ), (1 - Real.cos (t * s)) * Real.exp (-(rate a n) * s) / s
  rw [laplace_log (rate_pos ha n) t]
  congr 2
  unfold rate
  field_simp

end D5.S3.Analytic.Fourier.SinhLogIntegral
