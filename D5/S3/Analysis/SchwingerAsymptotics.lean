/- GID: D5/S3/Analysis/SchwingerAsymptotics
   generality: G
   mirror-B: none(waiver:covered-by-null-diamond-schwinger4-d-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The logarithmic normalization of the first Schwinger moment follows from Euler's integral for the Euler–Mascheroni constant. -/

import OmegaBuild.Commands
import D5.S3.Analysis.SchwingerIntegral
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
Omega original.

The logarithmic normalization of the first Schwinger moment follows from
Euler's integral for the Euler–Mascheroni constant. Exponential coordinates
turn the Schwinger integrals into hyperbolic cosine integrals.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Omega

open Filter Set Real _root_.MeasureTheory
open scoped Topology

private def firstMomentKernel (t s : ℝ) : ℝ := s⁻¹ * exp (-s - t / s)

private lemma schwinger_exponent {t : ℝ} (ht : 0 < t) (r : ℝ) :
    -(sqrt t * exp r) - t / (sqrt t * exp r) = -(2 * sqrt t) * cosh r := by
  have hs := sqrt_pos_of_pos ht
  have he := exp_pos r
  rw [cosh_eq, exp_neg]
  field_simp
  nlinarith [sq_sqrt ht.le]

private lemma exp_scale_image_Ioi {a : ℝ} (ha : 0 < a) :
    (fun r : ℝ => a * exp r) '' Ioi (0 : ℝ) = Ioi a := by
  ext s
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact lt_mul_of_one_lt_right ha (one_lt_exp_iff.mpr hr)
  · intro hs
    have hs' : 0 < s := ha.trans hs
    refine ⟨log (s / a), log_pos ((lt_div_iff₀ ha).2 (by simpa using hs)), ?_⟩
    change a * exp (log (s / a)) = s
    rw [exp_log (div_pos hs' ha)]
    field_simp

private lemma integral_exp_scale_Ioi {a : ℝ} (ha : 0 < a) (f : ℝ → ℝ) :
    (∫ s in Ioi a, f s) =
      ∫ r in Ioi (0 : ℝ), (a * exp r) * f (a * exp r) := by
  rw [← exp_scale_image_Ioi ha]
  have h := integral_image_eq_integral_abs_deriv_smul (f := fun r : ℝ => a * exp r)
    (f' := fun r : ℝ => a * exp r) (measurableSet_Ioi (a := (0 : ℝ)))
    (fun r _ => ((hasDerivAt_exp r).const_mul a).hasDerivWithinAt)
    (fun r _ s _ hrs => exp_injective (mul_left_cancel₀ ha.ne' hrs)) f
  simpa only [abs_of_pos (mul_pos ha (exp_pos _)), smul_eq_mul] using h

private lemma firstMoment_full_line {t : ℝ} (ht : 0 < t) :
    (∫ s in Ioi (0 : ℝ), firstMomentKernel t s) =
      ∫ r : ℝ, exp (-(2 * sqrt t) * cosh r) := by
  have hs := sqrt_pos_of_pos ht
  rw [← integral_comp_exp]
  simp only [firstMomentKernel, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (exp_pos _).ne',
    one_mul]
  rw [← integral_add_right_eq_self (fun r => exp (-exp r - t / exp r)) (log (sqrt t))]
  simp_rw [exp_add, exp_log hs, mul_comm (exp _) (sqrt t), schwinger_exponent ht]

private lemma firstMoment_tail {t : ℝ} (ht : 0 < t) :
    (∫ s in Ioi (sqrt t), firstMomentKernel t s) =
      ∫ r in Ioi (0 : ℝ), exp (-(2 * sqrt t) * cosh r) := by
  have hs := sqrt_pos_of_pos ht
  rw [integral_exp_scale_Ioi hs]
  congr 1
  ext r
  rw [firstMomentKernel, ← mul_assoc, mul_inv_cancel₀ (mul_pos hs (exp_pos r)).ne',
    one_mul, schwinger_exponent ht]

/-- The first moment is twice the order-zero hyperbolic cosine integral. -/
theorem schwingerMoment_one_eq_cosh_integral {t : ℝ} (ht : 0 < t) :
    schwingerMoment 1 t =
      2 * ∫ r in Ioi (0 : ℝ), exp (-(2 * sqrt t) * cosh r) * cosh (0 * r) := by
  simp only [schwingerMoment, pow_one, zero_mul, cosh_zero, mul_one]
  change (∫ s in Ioi (0 : ℝ), firstMomentKernel t s) = _
  rw [firstMoment_full_line ht]
  have heven : (fun r : ℝ => exp (-(2 * sqrt t) * cosh |r|)) =
      (fun r : ℝ => exp (-(2 * sqrt t) * cosh r)) := by
    ext r
    rw [cosh_abs]
  conv_lhs => rw [← heven]
  exact integral_comp_abs (f := fun r => exp (-(2 * sqrt t) * cosh r))

private lemma firstMoment_twice_tail {t : ℝ} (ht : 0 < t) :
    (∫ s in Ioi (0 : ℝ), firstMomentKernel t s) =
      2 * ∫ s in Ioi (sqrt t), firstMomentKernel t s := by
  rw [firstMoment_tail ht]
  simpa only [schwingerMoment, pow_one, firstMomentKernel, zero_mul, cosh_zero, mul_one] using
    schwingerMoment_one_eq_cosh_integral ht

private lemma integrableOn_log_mul_exp_neg :
    IntegrableOn (fun s : ℝ => log s * exp (-s)) (Ioi 0) := by
  have hlog := (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
    (intervalIntegral.intervalIntegrable_log' (a := 0) (b := 1))
  have hsmall : IntegrableOn (fun s : ℝ => log s * exp (-s)) (Ioc 0 1) := by
    refine hlog.norm.mono' (measurable_log.mul measurable_id.neg.exp).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    rw [norm_mul, Real.norm_of_nonneg (exp_pos _).le]
    exact mul_le_of_le_one_right (norm_nonneg _) (exp_le_one_iff.mpr (neg_nonpos.mpr hs.1.le))
  have hbig : IntegrableOn (fun s : ℝ => log s * exp (-s)) (Ioi 1) := by
    have hg := GammaIntegral_convergent (s := 2) (by norm_num)
    simp only [show (2 : ℝ) - 1 = 1 by norm_num, rpow_one] at hg
    refine (hg.mono_set (Ioi_subset_Ioi zero_le_one)).mono'
      (measurable_log.mul measurable_id.neg.exp).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs' : 1 < s := hs
    rw [Real.norm_of_nonneg (mul_nonneg (log_nonneg hs'.le) (exp_pos _).le), mul_comm (exp (-s))]
    exact mul_le_mul_of_nonneg_right ((log_le_sub_one_of_pos (zero_lt_one.trans hs')).trans (by linarith))
      (exp_pos _).le
  simpa only [Ioc_union_Ioi_eq_Ioi (a := (0 : ℝ)) (b := 1) zero_le_one] using
    hsmall.union hbig

private lemma integrableOn_exp_neg_div {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun s : ℝ => s⁻¹ * exp (-s)) (Ioi a) := by
  refine ((integrableOn_exp_neg_Ioi a).const_mul a⁻¹).mono'
    (measurable_id.inv.mul measurable_id.neg.exp).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hs' : a < s := hs
  rw [Real.norm_of_nonneg (mul_nonneg (inv_nonneg.mpr (ha.trans hs').le) (exp_pos _).le)]
  exact mul_le_mul_of_nonneg_right (inv_anti₀ ha hs'.le) (exp_pos _).le

private lemma expint_tail_parts {a : ℝ} (ha : 0 < a) :
    (∫ s in Ioi a, s⁻¹ * exp (-s)) + log a =
      (∫ s in Ioi a, log s * exp (-s)) + (1 - exp (-a)) * log a := by
  have hd (s : ℝ) (hs : s ∈ Ici a) :
      HasDerivAt (fun r : ℝ => log r * exp (-r))
        (s⁻¹ * exp (-s) - log s * exp (-s)) s := by
    convert (hasDerivAt_log (ha.trans_le hs).ne').mul ((hasDerivAt_neg s).exp) using 1
    ring
  have h₀ : Tendsto (fun s : ℝ => log s * exp (-s)) atTop (𝓝 0) := by
    have hp : Tendsto (fun s : ℝ => s * exp (-s)) atTop (𝓝 0) := by
      simpa only [pow_one] using tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hp ?_ ?_
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs
      exact mul_nonneg (log_nonneg hs) (exp_pos _).le
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs
      have hlog := log_le_sub_one_of_pos (zero_lt_one.trans_le hs)
      exact mul_le_mul_of_nonneg_right (by linarith) (exp_pos _).le
  have hi := integrableOn_log_mul_exp_neg.mono_set (Ioi_subset_Ioi ha.le)
  have hj := integrableOn_exp_neg_div ha
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' hd (hj.sub hi) h₀
  rw [integral_sub hj hi] at h
  linarith

private lemma expint_tail_limit :
    Tendsto (fun a : ℝ => (∫ s in Ioi a, s⁻¹ * exp (-s)) + log a)
      (𝓝[>] 0) (𝓝 (-eulerMascheroniConstant)) := by
  have hlog : Tendsto (fun a : ℝ => log a * a) (𝓝[>] 0) (𝓝 0) := by
    simpa only [rpow_one] using tendsto_log_mul_rpow_nhdsGT_zero (r := 1) zero_lt_one
  have hd : HasDerivAt (fun a : ℝ => exp (-a)) (-1) 0 := by
    simpa using (hasDerivAt_neg (0 : ℝ)).exp
  have hq : Tendsto (fun a : ℝ => (exp (-a) - 1) / a) (𝓝[>] 0) (𝓝 (-1)) := by
    simpa only [slope_fun_def_field, sub_zero, neg_zero, exp_zero] using
      (hd.tendsto_slope.mono_left (nhdsGT_le_nhdsNE (0 : ℝ)))
  have herr : Tendsto (fun a : ℝ => (1 - exp (-a)) * log a) (𝓝[>] 0) (𝓝 0) := by
    have h := hq.neg.mul hlog
    simp only [neg_neg, mul_zero] at h
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with a (ha : 0 < a)
    field_simp
    ring
  have h := integrableOn_log_mul_exp_neg.continuousWithinAt_Ici_primitive_Ioi.mono
    (s := Ioi (0 : ℝ)) Ioi_subset_Ici_self
  change Tendsto _ (𝓝[>] (0 : ℝ)) (𝓝 _) at h
  rw [eulerMascheroniConstant_eq_neg_integral_log, neg_neg]
  have hp := h.add herr
  simp only [add_zero] at hp
  exact hp.congr' (by
    filter_upwards [self_mem_nhdsWithin] with a (ha : 0 < a)
    exact (expint_tail_parts ha).symm)

private lemma schwinger_tail_error {t : ℝ} (ht : 0 < t) :
    0 ≤ (∫ s in Ioi (sqrt t), s⁻¹ * exp (-s)) -
        (∫ s in Ioi (sqrt t), firstMomentKernel t s) ∧
      (∫ s in Ioi (sqrt t), s⁻¹ * exp (-s)) -
        (∫ s in Ioi (sqrt t), firstMomentKernel t s) ≤ sqrt t := by
  have ha := sqrt_pos_of_pos ht
  have hi := integrableOn_exp_neg_div ha
  have h_nonneg (s : ℝ) (hs : s ∈ Ioi (sqrt t)) :
      0 ≤ firstMomentKernel t s := by
    have hsp := ha.trans hs
    exact mul_nonneg (inv_nonneg.mpr hsp.le) (exp_pos _).le
  have h_le (s : ℝ) (hs : s ∈ Ioi (sqrt t)) :
      firstMomentKernel t s ≤ s⁻¹ * exp (-s) := by
    have hsp := ha.trans hs
    unfold firstMomentKernel
    gcongr
    exact sub_le_self _ (div_nonneg ht.le hsp.le)
  have hj : IntegrableOn (firstMomentKernel t) (Ioi (sqrt t)) := by
    refine hi.mono' (measurable_id.inv.mul
      ((measurable_id.neg.sub (measurable_const.div measurable_id)).exp)).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    rw [Real.norm_of_nonneg (h_nonneg s hs)]
    exact h_le s hs
  constructor
  · apply sub_nonneg.mpr (integral_mono_ae hj hi ?_)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] using h_le
  · have hpow := integrableOn_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num) ha
    have h := integral_mono_ae (hi.sub hj) (hpow.const_mul t) ?_
    · simp only [Pi.sub_apply] at h
      rw [integral_sub hi hj, integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) ha] at h
      convert h using 1
      norm_num [rpow_neg_one]
      apply (eq_div_iff ha.ne').2
      nlinarith [sq_sqrt ht.le]
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      have hsp := ha.trans hs
      have hs0 : 0 ≤ t / s := div_nonneg ht.le hsp.le
      have hone : 0 ≤ 1 - exp (-(t / s)) := sub_nonneg.mpr (exp_le_one_iff.mpr (neg_nonpos.mpr hs0))
      have he : 1 - exp (-(t / s)) ≤ t / s := by linarith [add_one_le_exp (-(t / s))]
      change s⁻¹ * exp (-s) - firstMomentKernel t s ≤ t * s ^ (-2 : ℝ)
      rw [firstMomentKernel, sub_eq_add_neg (-s), exp_add]
      calc
        _ = s⁻¹ * (exp (-s) * (1 - exp (-(t / s)))) := by ring
        _ ≤ s⁻¹ * (1 * (t / s)) := by
          gcongr
          exact exp_le_one_iff.mpr (neg_nonpos.mpr hsp.le)
        _ = t * s ^ (-2 : ℝ) := by
          rw [rpow_neg hsp.le]
          norm_num [rpow_natCast, div_eq_mul_inv, pow_two]
          ring

/-- The negative first moment minus the logarithm tends to twice Euler's constant. -/
theorem tendsto_neg_schwingerMoment_one_sub_log :
    Tendsto (fun t : ℝ => -schwingerMoment 1 t - log t)
      (𝓝[>] 0) (𝓝 (2 * eulerMascheroniConstant)) := by
  have hsq : Tendsto sqrt (𝓝[>] (0 : ℝ)) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.2
    refine ⟨?_, ?_⟩
    · simpa only [sqrt_zero] using
        (continuous_sqrt.continuousAt (x := 0)).tendsto.mono_left
          (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
      exact sqrt_pos_of_pos ht
  have herror : Tendsto (fun t : ℝ =>
      (∫ s in Ioi (sqrt t), s⁻¹ * exp (-s)) - (∫ s in Ioi (sqrt t), firstMomentKernel t s))
      (𝓝[>] 0) (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (hsq.mono_right nhdsWithin_le_nhds) ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
      exact (schwinger_tail_error ht).1
    · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
      exact (schwinger_tail_error ht).2
  have hl := tendsto_const_nhds.mul ((expint_tail_limit.comp hsq).sub herror)
    (f := fun _ : ℝ => (-2 : ℝ))
  simp only [sub_zero, neg_mul_neg, Function.comp_def] at hl
  apply hl.congr'
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  simp only [schwingerMoment, pow_one]
  change _ = -(∫ s in Ioi (0 : ℝ), firstMomentKernel t s) - log t
  rw [firstMoment_twice_tail ht, log_sqrt ht.le]
  ring

end Omega
