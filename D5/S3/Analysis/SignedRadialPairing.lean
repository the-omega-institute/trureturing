/- GID: D5/S3/Analysis/SignedRadialPairing
   generality: G
   mirror-B: none(waiver:covered-by-null-diamond-profile-fourier4-d-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The distance and sign kernels paired with derivatives of compact radial tests. -/

import OmegaBuild.Commands
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.Deriv.Support

/-!
Omega original.

The distance and sign kernels paired with derivatives of compact radial tests.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace Omega

/-- The oriented sign kernel, with the negative value on the diagonal. -/
def radialSign (s : ℝ) : ℂ := if 0 < s then 1 else -1

private theorem measurable_radialSign : Measurable radialSign :=
  Measurable.ite measurableSet_Ioi measurable_const measurable_const

private theorem norm_radialSign (s : ℝ) : ‖radialSign s‖ = 1 := by
  unfold radialSign
  split <;> simp

/-- The sign kernel gives the local evaluation of the undifferentiated test. -/
theorem integral_radialSign_deriv {g : ℝ → ℂ} (hg : ContDiff ℝ 1 g)
    (hgc : HasCompactSupport g) (s : ℝ) :
    (∫ t, radialSign (s - t) * deriv g t) = 2 * g s := by
  have hgi : Integrable (deriv g) :=
    (hg.continuous_deriv le_rfl).integrable_of_hasCompactSupport hgc.deriv
  have hl : (∫ t in Iio s, radialSign (s - t) * deriv g t) = g s := by
    calc
      _ = ∫ t in Iio s, deriv g t := setIntegral_congr_fun measurableSet_Iio fun t ht => by
        simp [radialSign, sub_pos.mpr (mem_Iio.mp ht)]
      _ = _ := by
        rw [← integral_Iic_eq_integral_Iio, hgc.integral_Iic_deriv_eq hg]
  have hr : (∫ t in Ici s, radialSign (s - t) * deriv g t) = g s := by
    calc
      _ = ∫ t in Ici s, -(deriv g t) := setIntegral_congr_fun measurableSet_Ici fun t ht => by
        simp [radialSign, not_lt.mpr (sub_nonpos.mpr (mem_Ici.mp ht))]
      _ = _ := by
        rw [integral_neg, integral_Ici_eq_integral_Ioi, hgc.integral_Ioi_deriv_eq hg, neg_neg]
  have hsign : Measurable (fun t : ℝ => radialSign (s - t)) :=
    measurable_radialSign.comp (measurable_const.sub measurable_id)
  have hi : Integrable (fun t => radialSign (s - t) * deriv g t) := by
    refine hgi.norm.mono' (hsign.aestronglyMeasurable.mul hgi.aestronglyMeasurable) ?_
    exact .of_forall fun t => by simp only [norm_mul, norm_radialSign, one_mul, le_refl]
  rw [← integral_add_compl measurableSet_Iio hi, compl_Iio, hl, hr, two_mul]

/-- The first integration by parts for the distance kernel gives a sign kernel. -/
theorem integral_abs_sub_deriv {g : ℝ → ℂ} (hg : ContDiff ℝ 1 g)
    (hgc : HasCompactSupport g) (s : ℝ) :
    (∫ t : ℝ, ((|s - t| : ℝ) : ℂ) * deriv g t) = ∫ t, radialSign (s - t) * g t := by
  let u : ℝ → ℂ := fun t => ((s - t : ℝ) : ℂ)
  have hu (t : ℝ) : HasDerivAt u (-1) t := by
    have h : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 (s - t) :=
      Complex.ofRealCLM.hasFDerivAt.hasDerivAt
    have hh : HasDerivAt (fun x : ℝ => s - x) (-1) t := by
      exact (hasDerivAt_id t).const_sub s
    simpa [u, Function.comp_def] using h.scomp t hh
  have hα : Continuous (fun t : ℝ => ((|s - t| : ℝ) : ℂ)) := by fun_prop
  have hg' := hg.continuous_deriv le_rfl
  have hi₁ : Integrable (fun t : ℝ => ((|s - t| : ℝ) : ℂ) * deriv g t) :=
    (hα.mul hg').integrable_of_hasCompactSupport hgc.deriv.mul_left
  have hgi : Integrable g := hg.continuous.integrable_of_hasCompactSupport hgc
  have hi₂ : Integrable (fun t => radialSign (s - t) * g t) := by
    have hs : Measurable (fun t : ℝ => radialSign (s - t)) :=
      measurable_radialSign.comp (measurable_const.sub measurable_id)
    apply hgi.norm.mono' (hs.aestronglyMeasurable.mul hgi.aestronglyMeasurable)
    exact .of_forall fun t => by
      change ‖radialSign (s - t) * g t‖ ≤ ‖g t‖
      simp only [norm_mul, norm_radialSign, one_mul, le_refl]
  let P : ℝ → ℂ := fun t => u t * g t
  have hPc : HasCompactSupport P := hgc.mul_left
  have hPs : ContDiff ℝ 1 P := by
    apply ContDiff.mul _ hg
    exact Complex.ofRealCLM.contDiff.comp (contDiff_const.sub contDiff_id)
  have hPd (t : ℝ) : deriv P t = -g t + u t * deriv g t := by
    exact (((hu t).mul (hg.differentiable one_ne_zero t).hasDerivAt).deriv).trans (by ring)
  have hU : Continuous u := Complex.continuous_ofReal.comp (continuous_const.sub continuous_id)
  have hgi' : Integrable (fun t => u t * deriv g t) :=
    (hU.mul hg').integrable_of_hasCompactSupport hgc.deriv.mul_left
  have hleft : (∫ t in Iic s, u t * deriv g t) = ∫ t in Iic s, g t := by
    have h := hPc.integral_Iic_deriv_eq hPs s
    rw [show deriv P = fun t => -g t + u t * deriv g t from funext hPd] at h
    rw [integral_add (f := fun t => -g t) hgi.neg.integrableOn hgi'.integrableOn,
      integral_neg] at h
    have hz : P s = 0 := by simp [P, u]
    rw [hz, neg_add_eq_zero] at h
    exact h.symm
  have hright : (∫ t in Ioi s, u t * deriv g t) = ∫ t in Ioi s, g t := by
    have h := hPc.integral_Ioi_deriv_eq hPs s
    rw [show deriv P = fun t => -g t + u t * deriv g t from funext hPd] at h
    rw [integral_add (f := fun t => -g t) hgi.neg.integrableOn hgi'.integrableOn,
      integral_neg] at h
    have hz : P s = 0 := by simp [P, u]
    rw [hz, neg_zero, neg_add_eq_zero] at h
    exact h.symm
  rw [← integral_add_compl measurableSet_Iic hi₁,
    ← integral_add_compl measurableSet_Iic hi₂, compl_Iic]
  have h₁ : (∫ t in Iic s, ((|s - t| : ℝ) : ℂ) * deriv g t) =
      ∫ t in Iic s, u t * deriv g t := by
    apply setIntegral_congr_fun measurableSet_Iic
    intro t ht
    simp only [u, abs_of_nonneg (sub_nonneg.mpr (mem_Iic.mp ht))]
  have h₂ : (∫ t in Ioi s, ((|s - t| : ℝ) : ℂ) * deriv g t) =
      -(∫ t in Ioi s, u t * deriv g t) := by
    rw [← integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    simp only [u, abs_of_neg (sub_neg.mpr (mem_Ioi.mp ht)), Complex.ofReal_neg, neg_mul]
  rw [h₁, h₂, hleft, hright]
  congr 1
  · rw [integral_Iic_eq_integral_Iio, integral_Iic_eq_integral_Iio]
    apply setIntegral_congr_fun measurableSet_Iio
    intro t ht
    simp [radialSign, sub_pos.mpr (mem_Iio.mp ht)]
  · rw [← integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    simp [radialSign, not_lt.mpr (sub_nonpos.mpr (mem_Ioi.mp ht).le)]


/-- Two integrations by parts reduce the distance pairing to the local term. -/
theorem integral_abs_sub_deriv_pairing {f g : ℝ → ℂ}
    (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) :
    (∫ s : ℝ, deriv f s * ∫ t : ℝ, ((|s - t| : ℝ) : ℂ) * deriv g t) =
      -(2 : ℂ) * ∫ t, f t * g t := by
  have hfi : Integrable (deriv f) :=
    (hf.continuous_deriv le_rfl).integrable_of_hasCompactSupport hfc.deriv
  have hgi : Integrable g := hg.continuous.integrable_of_hasCompactSupport hgc
  have hi : Integrable (fun p : ℝ × ℝ => deriv f p.1 * (radialSign (p.1 - p.2) * g p.2))
      ((volume : Measure ℝ).prod volume) := by
    have hm := (hfi.aestronglyMeasurable.comp_fst).mul
      ((measurable_radialSign.comp (measurable_fst.sub measurable_snd)).aestronglyMeasurable.mul
        hgi.aestronglyMeasurable.comp_snd)
    apply (hfi.norm.mul_prod hgi.norm).mono' hm
    exact .of_forall fun p => by
      change ‖deriv f p.1 * (radialSign (p.1 - p.2) * g p.2)‖ ≤
        ‖deriv f p.1‖ * ‖g p.2‖
      simp only [norm_mul, norm_radialSign, one_mul, le_refl]
  have hflip (t : ℝ) : (∫ s, deriv f s * (radialSign (s - t) * g t)) = -2 * (f t * g t) := by
    have hne : ∀ᵐ s : ℝ, s ≠ t := by rw [ae_iff]; simp
    calc
      _ = ∫ s : ℝ, -(radialSign (t - s) * deriv f s) * g t := by
        apply integral_congr_ae
        filter_upwards [hne] with s hs
        rcases lt_or_gt_of_ne hs with hs | hs
        · simp [radialSign, sub_pos.mpr hs, not_lt.mpr (sub_nonpos.mpr hs.le)]
        · simp [radialSign, sub_pos.mpr hs, not_lt.mpr (sub_nonpos.mpr hs.le)]
      _ = _ := by
        rw [integral_mul_const, integral_neg, integral_radialSign_deriv hf hfc]
        ring
  simp_rw [integral_abs_sub_deriv hg hgc, ← integral_const_mul]
  rw [integral_integral_swap (f := fun s t => deriv f s * (radialSign (s - t) * g t)) hi]
  simp only [hflip, integral_const_mul]

end Omega

