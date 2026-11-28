/- GID: D5/S3/Analysis/SchwingerIntegral
   generality: G
   mirror-B: none(waiver:covered-by-null-diamond-schwinger4-d-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Inverse-power moments of the Schwinger kernel give the derivatives of its integral. -/

import OmegaBuild.Commands
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
Omega original.

Inverse-power moments of the Schwinger kernel give the derivatives of its
integral. The first two spatial boundary values of the kernel determine the
second-order equation by improper integration.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace Omega

private def schwingerIntegrand (n : ℕ) (t s : ℝ) : ℝ :=
  s⁻¹ ^ n * Real.exp (-s - t / s)

/-- The inverse-power moments of the Schwinger kernel on the positive half-line. -/
def schwingerMoment (n : ℕ) (t : ℝ) : ℝ :=
  ∫ s in Ioi (0 : ℝ), s⁻¹ ^ n * Real.exp (-s - t / s)

/-- The Schwinger integral on the positive half-line. -/
def schwingerIntegral (t : ℝ) : ℝ :=
  ∫ s in Ioi (0 : ℝ), Real.exp (-s - t / s)

private lemma schwingerIntegrand_measurable (n : ℕ) (t : ℝ) :
    Measurable (schwingerIntegrand n t) :=
  (measurable_id.inv.pow_const n).mul
    (measurable_id.neg.sub (measurable_const.div measurable_id)).exp

private lemma schwingerIntegrand_le (n : ℕ) {t s : ℝ} (ht : 0 < t) (hs : 0 < s) :
    schwingerIntegrand n t s ≤ (n.factorial : ℝ) / t ^ n * Real.exp (-s) := by
  have hn : 0 < (n.factorial : ℝ) := by positivity
  have hp := (div_le_iff₀ hn).mp
    (Real.pow_div_factorial_le_exp (t / s) (div_nonneg ht.le hs.le) n)
  calc
    schwingerIntegrand n t s =
        (t / s) ^ n * ((t ^ n)⁻¹ * Real.exp (-s - t / s)) := by
      rw [schwingerIntegrand, div_eq_mul_inv, mul_pow]
      field_simp [ne_of_gt ht]
    _ ≤ ((n.factorial : ℝ) * Real.exp (t / s)) *
        ((t ^ n)⁻¹ * Real.exp (-s - t / s)) := by
      exact mul_le_mul_of_nonneg_right (by simpa only [mul_comm] using hp) (by positivity)
    _ = (n.factorial : ℝ) / t ^ n * (Real.exp (t / s) * Real.exp (-s - t / s)) := by
      simp only [div_eq_mul_inv]
      ring
    _ = _ := by rw [← Real.exp_add, show t / s + (-s - t / s) = -s by ring]

/-- Every inverse-power moment is integrable when the parameter is positive. -/
theorem schwingerMoment_integrable (n : ℕ) {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun s : ℝ => s⁻¹ ^ n * Real.exp (-s - t / s)) (Ioi 0) := by
  change Integrable _ (volume.restrict (Ioi 0))
  refine ((integrableOn_exp_neg_Ioi 0).const_mul ((n.factorial : ℝ) / t ^ n)).mono'
    (schwingerIntegrand_measurable n t).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hs' : 0 < s := hs
  change ‖schwingerIntegrand n t s‖ ≤ _
  rw [Real.norm_of_nonneg (by dsimp [schwingerIntegrand]; positivity)]
  exact schwingerIntegrand_le n ht hs'

/-- A parameter derivative inserts a negative inverse power into the integral. -/
theorem hasDerivAt_schwingerMoment (n : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (schwingerMoment n) (-schwingerMoment (n + 1) t) t := by
  have hm (r : ℝ) : AEStronglyMeasurable (schwingerIntegrand n r)
      (volume.restrict (Ioi (0 : ℝ))) := (schwingerIntegrand_measurable n r).aestronglyMeasurable
  have hm' : AEStronglyMeasurable (fun s => -schwingerIntegrand (n + 1) t s)
      (volume.restrict (Ioi (0 : ℝ))) :=
    (schwingerIntegrand_measurable (n + 1) t).neg.aestronglyMeasurable
  have hdom : ∀ᵐ s ∂volume.restrict (Ioi (0 : ℝ)), ∀ r ∈ Ioi (t / 2),
      ‖-schwingerIntegrand (n + 1) r s‖ ≤ schwingerIntegrand (n + 1) (t / 2) s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs r hr
    have hs' : 0 < s := hs
    have hr' : t / 2 < r := hr
    simp only [schwingerIntegrand, norm_neg]
    rw [Real.norm_of_nonneg (by positivity)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Real.exp_le_exp.mpr (sub_le_sub_left (div_le_div_of_nonneg_right hr'.le hs'.le) _)
  have hdiff : ∀ᵐ s ∂volume.restrict (Ioi (0 : ℝ)), ∀ r ∈ Ioi (t / 2),
      HasDerivAt (fun t => schwingerIntegrand n t s) (-schwingerIntegrand (n + 1) r s) r := by
    filter_upwards with s r _
    have h := (((hasDerivAt_id' r).div_const s).const_sub (-s)).exp.const_mul (s⁻¹ ^ n)
    have he : -(s⁻¹ ^ (n + 1) * Real.exp (-s - r / s)) =
        s⁻¹ ^ n * (Real.exp (-s - r / s) * -(1 / s)) := by
      rw [pow_succ, one_div]
      ring
    simpa only [schwingerIntegrand, he] using h
  have h := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Ioi_mem_nhds (show t / 2 < t by linarith))
    (Eventually.of_forall hm) (schwingerMoment_integrable n ht) hm' hdom
    (schwingerMoment_integrable (n + 1) (half_pos ht)) hdiff).2
  change HasDerivAt (fun r => ∫ s in Ioi (0 : ℝ), schwingerIntegrand n r s)
    (-(∫ s in Ioi (0 : ℝ), schwingerIntegrand (n + 1) t s)) t
  rw [← integral_neg]
  exact h

/-- The first derivative of the Schwinger integral is the negative first moment. -/
theorem hasDerivAt_schwingerIntegral {t : ℝ} (ht : 0 < t) :
    HasDerivAt schwingerIntegral (-schwingerMoment 1 t) t := by
  have he : schwingerMoment 0 = schwingerIntegral := by
    funext r
    simp [schwingerMoment, schwingerIntegral]
  simpa only [he, zero_add] using hasDerivAt_schwingerMoment 0 ht

/-- Integrating the spatial derivative yields the Schwinger differential equation. -/
theorem schwingerIntegral_eq_mul_moment_two {t : ℝ} (ht : 0 < t) :
    schwingerIntegral t = t * schwingerMoment 2 t := by
  let f (s : ℝ) := if s = 0 then 0 else Real.exp (-s - t / s)
  let f' (s : ℝ) := t * (s⁻¹ ^ 2 * Real.exp (-s - t / s)) - Real.exp (-s - t / s)
  have hderiv : ∀ s ∈ Ioi (0 : ℝ), HasDerivAt f (f' s) s := by
    intro s hs
    have hs' : 0 < s := hs
    have hd := ((hasDerivAt_id s).neg.sub ((hasDerivAt_inv (ne_of_gt hs')).const_mul t)).exp
    have hd' : HasDerivAt (fun r : ℝ => Real.exp (-r - t / r)) (f' s) s := by
      convert hd using 1
      · ext r
        simp [div_eq_mul_inv]
      · dsimp [f']
        rw [← inv_pow, div_eq_mul_inv]
        ring
    apply hd'.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hs'] with r hr
    simp [f, ne_of_gt (show 0 < r from hr)]
  have hf' : IntegrableOn f' (Ioi (0 : ℝ)) := by
    have h0 : IntegrableOn (fun s : ℝ => Real.exp (-s - t / s)) (Ioi 0) := by
      simpa using schwingerMoment_integrable 0 ht
    exact ((schwingerMoment_integrable 2 ht).const_mul t).sub h0
  have hzero : ContinuousWithinAt f (Ici 0) 0 := by
    rw [← continuousWithinAt_Ioi_iff_Ici]
    change Tendsto f (𝓝[Ioi 0] 0) (𝓝 (f 0))
    have hlim : Tendsto (fun x : ℝ => t / x) (𝓝[Ioi 0] 0) atTop := by
      simpa only [div_eq_mul_inv] using tendsto_inv_nhdsGT_zero.const_mul_atTop ht
    have hupper : Tendsto (fun s : ℝ => Real.exp (-(t / s))) (𝓝[Ioi 0] 0) (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp hlim
    have hf0 : f 0 = 0 := by simp [f]
    rw [hf0]
    refine squeeze_zero' (Eventually.of_forall fun s => ?_) ?_ hupper
    · by_cases hs : s = 0 <;> simp [f, hs, Real.exp_nonneg]
    · filter_upwards [self_mem_nhdsWithin] with s hs
      have hs' : 0 < s := hs
      simp only [f, hs'.ne', ite_false, Real.exp_le_exp]
      linarith
  have htop : Tendsto f atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun s => ?_) ?_ Real.tendsto_exp_neg_atTop_nhds_zero
    · by_cases hs : s = 0 <;> simp [f, hs, Real.exp_nonneg]
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
      simp only [f, hs.ne', ite_false, Real.exp_le_exp]
      exact sub_le_self _ (div_nonneg ht.le hs.le)
  have h := integral_Ioi_of_hasDerivAt_of_tendsto hzero hderiv hf' htop
  have h0 : IntegrableOn (fun s : ℝ => Real.exp (-s - t / s)) (Ioi 0) := by
    simpa using schwingerMoment_integrable 0 ht
  rw [show f 0 = 0 by simp [f], sub_zero] at h
  change (∫ s in Ioi (0 : ℝ), t * (s⁻¹ ^ 2 * Real.exp (-s - t / s)) -
    Real.exp (-s - t / s)) = 0 at h
  rw [integral_sub ((schwingerMoment_integrable 2 ht).const_mul t) h0, integral_const_mul] at h
  exact (sub_eq_zero.mp h).symm

/-- The right endpoint value comes from domination by `exp (-s)`. -/
theorem tendsto_schwingerIntegral_zero :
    Tendsto schwingerIntegral (𝓝[Ioi 0] (0 : ℝ)) (𝓝 1) := by
  rw [← integral_exp_neg_Ioi_zero]
  apply tendsto_integral_filter_of_dominated_convergence (fun s : ℝ => Real.exp (-s))
  · exact Eventually.of_forall fun t =>
      (measurable_id.neg.sub (measurable_const.div measurable_id)).exp.aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with t ht
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have ht' : 0 < t := ht
    have hs' : 0 < s := hs
    rw [Real.norm_of_nonneg (Real.exp_nonneg _), Real.exp_le_exp]
    exact sub_le_self _ (div_nonneg ht'.le hs'.le)
  · exact integrableOn_exp_neg_Ioi 0
  · filter_upwards with s
    have hc : Continuous (fun t : ℝ => Real.exp (-s - t / s)) := by fun_prop
    have h : Tendsto (fun t : ℝ => Real.exp (-s - t / s)) (𝓝[Ioi 0] (0 : ℝ))
        (𝓝 (Real.exp (-s - 0 / s))) := hc.continuousAt.continuousWithinAt
    simpa only [zero_div, sub_zero] using h

end Omega
