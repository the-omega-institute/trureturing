/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/OriginalAngularResolvent
   generality: G
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/OriginalAngularResolvent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The angular inverse resolvent has exact exponential quarter normalization at every real lag. -/

import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic

/-!
The angular-resolvent formula uses the Fourier convention of Mathlib.
Its auxiliary declarations are consumed by the final integral theorems.

Upstream suppliers: Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679,
Analysis/Fourier/Inversion.lean (Sebastien Gouezel, copyright 2024),
Analysis/Fourier/FourierTransform.lean and
Analysis/SpecialFunctions/ImproperIntegrals.lean (David Loeffler, copyright 2023).
Those upstream files are released under Apache 2.0; their proofs are imported,
not copied. This source is also offered under Apache 2.0.

Mathlib's forward phase is exp(-2*pi*i*t*xi). The transform of
exp(-abs(t)/2) is 4/(1+4*(2*pi*xi)^2). Inversion followed by w=2*pi*xi
therefore gives the exact factor 1/(2*pi) and the value exp(-abs(s)/2)/4.
There is no sign restriction on s, and no removal of the s=0 case.
-/

noncomputable section

open Set MeasureTheory
open scoped Topology FourierTransform

namespace OriginalAngularResolvent

private def decay (t : ℝ) : ℂ := (Real.exp (-|t| / 2) : ℂ)

private def weight (w : ℝ) : ℝ := (1 + 4 * w ^ 2)⁻¹

private def forwardIntegrand (w t : ℝ) : ℂ :=
  Complex.exp (-Complex.I * (w : ℂ) * (t : ℂ)) * decay t

private def angularIntegrand (s w : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((w * s : ℝ) : ℂ)) * (weight w : ℂ)

private lemma denom_pos (w : ℝ) : 0 < 1 + 4 * w ^ 2 := by positivity

private lemma weight_integrable : Integrable weight := by
  have he : weight = fun w : ℝ => (1 + (2 * w) ^ 2)⁻¹ := by
    funext w
    dsimp [weight]
    congr 1
    ring
  rw [he]
  exact integrable_inv_one_add_mul_sq (by norm_num : (2 : ℝ) ≠ 0)

private lemma left_phase (w t : ℝ) (ht : t ≤ 0) :
    forwardIntegrand w t =
      Complex.exp (((1 : ℂ) / 2 - Complex.I * (w : ℂ)) * (t : ℂ)) := by
  dsimp [forwardIntegrand, decay]
  rw [abs_of_nonpos ht, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma right_phase (w t : ℝ) (ht : 0 ≤ t) :
    forwardIntegrand w t =
      Complex.exp ((-(1 : ℂ) / 2 - Complex.I * (w : ℂ)) * (t : ℂ)) := by
  dsimp [forwardIntegrand, decay]
  rw [abs_of_nonneg ht, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma left_integrable (w : ℝ) :
    IntegrableOn (forwardIntegrand w) (Iic (0 : ℝ)) := by
  have ha : 0 < ((1 : ℂ) / 2 - Complex.I * (w : ℂ)).re := by
    norm_num [Complex.mul_re, Complex.div_re]
  exact (integrableOn_exp_mul_complex_Iic ha 0).congr_fun
    (fun t ht => (left_phase w t ht).symm) measurableSet_Iic

private lemma right_integrable (w : ℝ) :
    IntegrableOn (forwardIntegrand w) (Ioi (0 : ℝ)) := by
  have ha : (-(1 : ℂ) / 2 - Complex.I * (w : ℂ)).re < 0 := by
    norm_num [Complex.mul_re, Complex.div_re]
  exact (integrableOn_exp_mul_complex_Ioi ha 0).congr_fun
    (fun t ht => (right_phase w t ht.le).symm) measurableSet_Ioi

private lemma forward_integrable (w : ℝ) : Integrable (forwardIntegrand w) := by
  have h := (left_integrable w).union (right_integrable w)
  simpa only [Iic_union_Ioi, integrableOn_univ] using h

private lemma decay_integrable : Integrable decay := by
  have h := forward_integrable 0
  convert h using 1
  funext t
  simp [forwardIntegrand, decay]

private lemma decay_continuous : Continuous decay := by
  unfold decay
  fun_prop

/-- The rational identity after both genuinely convergent half-line integrals. -/
private lemma rational_identity (w : ℝ) :
    1 / ((1 : ℂ) / 2 - Complex.I * (w : ℂ)) -
      1 / (-(1 : ℂ) / 2 - Complex.I * (w : ℂ)) =
      4 * (weight w : ℂ) := by
  have ha : (1 : ℂ) / 2 - Complex.I * (w : ℂ) ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    norm_num [Complex.mul_re, Complex.div_re] at hr
  have hb : -(1 : ℂ) / 2 - Complex.I * (w : ℂ) ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    norm_num [Complex.mul_re, Complex.div_re] at hr
  have hd : (1 : ℂ) + 4 * (w : ℂ) ^ 2 ≠ 0 := by
    exact_mod_cast (denom_pos w).ne'
  have hdiff :
      (-(1 : ℂ) / 2 - Complex.I * (w : ℂ)) -
        ((1 : ℂ) / 2 - Complex.I * (w : ℂ)) = -1 := by ring
  have hprod :
      ((1 : ℂ) / 2 - Complex.I * (w : ℂ)) *
        (-(1 : ℂ) / 2 - Complex.I * (w : ℂ)) =
          -(((1 : ℂ) + 4 * (w : ℂ) ^ 2) / 4) := by
    ring_nf <;> simp [Complex.I_sq] <;> ring
  rw [div_sub_div 1 1 ha hb]
  simp only [one_mul, mul_one]
  rw [hdiff, hprod]
  dsimp [weight]
  push_cast
  field_simp [hd] <;> ring

private lemma forward_integral (w : ℝ) :
    (∫ t : ℝ, forwardIntegrand w t) = 4 * (weight w : ℂ) := by
  have hl :
      (∫ t : ℝ in Iic 0, forwardIntegrand w t) =
        1 / ((1 : ℂ) / 2 - Complex.I * (w : ℂ)) := by
    calc
      _ = ∫ t : ℝ in Iic 0,
          Complex.exp (((1 : ℂ) / 2 - Complex.I * (w : ℂ)) * (t : ℂ)) :=
        setIntegral_congr_fun measurableSet_Iic (fun t ht => left_phase w t ht)
      _ = _ := by
        rw [integral_exp_mul_complex_Iic (by
          norm_num [Complex.mul_re, Complex.div_re])]
        simp
  have hr :
      (∫ t : ℝ in Ioi 0, forwardIntegrand w t) =
        -(1 / (-(1 : ℂ) / 2 - Complex.I * (w : ℂ))) := by
    calc
      _ = ∫ t : ℝ in Ioi 0,
          Complex.exp ((-(1 : ℂ) / 2 - Complex.I * (w : ℂ)) * (t : ℂ)) :=
        setIntegral_congr_fun measurableSet_Ioi (fun t ht => right_phase w t ht.le)
      _ = _ := by
        rw [integral_exp_mul_complex_Ioi (by
          norm_num [Complex.mul_re, Complex.div_re])]
        rw [neg_div]
        norm_num [Complex.exp_zero, one_div]
  rw [← intervalIntegral.integral_Iic_add_Ioi (left_integrable w) (right_integrable w), hl, hr]
  simpa only [sub_eq_add_neg] using rational_identity w

/-- Convert the angular forward computation to Mathlib's cyclic convention. -/
private lemma fourier_decay (ξ : ℝ) :
    𝓕 decay ξ = (4 : ℂ) * (weight (2 * Real.pi * ξ) : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  calc
    _ = ∫ t : ℝ, forwardIntegrand (2 * Real.pi * ξ) t := by
      apply integral_congr_ae
      filter_upwards with t
      dsimp [forwardIntegrand]
      congr 1
      congr 1
      push_cast
      ring
    _ = _ := forward_integral _

private lemma fourier_decay_integrable : Integrable (𝓕 decay) := by
  have hscale : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hwc : Integrable (fun w : ℝ => (weight w : ℂ)) := weight_integrable.ofReal
  have hscale' : Integrable (fun ξ : ℝ => (weight (2 * Real.pi * ξ) : ℂ)) :=
    hwc.comp_mul_left' hscale
  have h : Integrable (fun ξ : ℝ => (4 : ℂ) * (weight (2 * Real.pi * ξ) : ℂ)) :=
    hscale'.const_mul (4 : ℂ)
  have he : 𝓕 decay = fun ξ : ℝ => (4 : ℂ) * (weight (2 * Real.pi * ξ) : ℂ) :=
    funext fourier_decay
  simpa only [he] using h

private lemma angular_integrable (s : ℝ) : Integrable (angularIntegrand s) := by
  have hc : Continuous (fun w : ℝ => Complex.exp (Complex.I * ((w * s : ℝ) : ℂ))) := by
    fun_prop
  exact weight_integrable.ofReal.bdd_mul hc.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun w =>
      (Complex.norm_exp_I_mul_ofReal (w * s)).le))

private lemma integrand_literal (s w : ℝ) :
    angularIntegrand s w =
      Complex.exp (Complex.I * (w : ℂ) * (s : ℂ)) /
        ((1 + 4 * w ^ 2 : ℝ) : ℂ) := by
  simp [angularIntegrand, weight, div_eq_mul_inv, mul_assoc]

/-- Fourier inversion at every real s, followed by the Haar/Jacobian factor.
No desired resolvent integral appears among the premises. -/
private lemma normalized_integral (s : ℝ) :
    (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
      (∫ w : ℝ, angularIntegrand s w) = decay s / 4 := by
  have hinv := decay_integrable.fourierInv_fourier_eq fourier_decay_integrable
    (decay_continuous.continuousAt (x := s))
  rw [Real.fourierInv_eq'] at hinv
  simp only [Real.inner_apply, smul_eq_mul] at hinv
  have hphase (ξ : ℝ) :
      Complex.exp (((2 * Real.pi * (ξ * s) : ℝ) : ℂ) * Complex.I) * 𝓕 decay ξ =
        (4 : ℂ) * angularIntegrand s (2 * Real.pi * ξ) := by
    rw [fourier_decay]
    dsimp [angularIntegrand]
    have he : (((2 * Real.pi * (ξ * s) : ℝ) : ℂ) * Complex.I) =
        Complex.I * (((2 * Real.pi * ξ) * s : ℝ) : ℂ) := by
      push_cast
      ring
    rw [he]
    ring
  simp_rw [hphase] at hinv
  rw [integral_const_mul] at hinv
  have hp : 0 < 2 * Real.pi := by positivity
  have hchange :
      (∫ ξ : ℝ, angularIntegrand s (2 * Real.pi * ξ)) =
        (((1 / (2 * Real.pi) : ℝ) : ℂ)) * (∫ w : ℝ, angularIntegrand s w) := by
    simpa only [abs_of_pos (inv_pos.mpr hp), Complex.real_smul, one_div] using
      (Measure.integral_comp_mul_left (angularIntegrand s) (2 * Real.pi))
  rw [hchange] at hinv
  apply (eq_div_iff (by norm_num : (4 : ℂ) ≠ 0)).mpr
  calc
    _ = (4 : ℂ) *
        ((((1 / (2 * Real.pi) : ℝ) : ℂ)) * (∫ w : ℝ, angularIntegrand s w)) := by ring
    _ = decay s := hinv

/-- Exact angular Cauchy-resolvent integral, with absolute integrability.
The statement retains the complex phase and all real s, including zero. -/
theorem angular_resolvent (s : ℝ) :
    Integrable (fun w : ℝ =>
      Complex.exp (Complex.I * (w : ℂ) * (s : ℂ)) /
        ((1 + 4 * w ^ 2 : ℝ) : ℂ)) ∧
    (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
      (∫ w : ℝ, Complex.exp (Complex.I * (w : ℂ) * (s : ℂ)) /
        ((1 + 4 * w ^ 2 : ℝ) : ℂ)) = (Real.exp (-|s| / 2) : ℂ) / 4 := by
  constructor
  · simpa only [integrand_literal] using
      (angular_integrable s : Integrable (fun w : ℝ => angularIntegrand s w))
  · simpa only [integrand_literal, decay] using normalized_integral s

private lemma integrand_re (s w : ℝ) :
    (angularIntegrand s w).re = Real.cos (w * s) / (1 + 4 * w ^ 2) := by
  dsimp [angularIntegrand]
  rw [Complex.re_mul_ofReal, mul_comm Complex.I (((w * s : ℝ) : ℂ)),
    Complex.exp_ofReal_mul_I_re]
  simp only [weight, div_eq_mul_inv]

/-- Real part of the same normalized integral, for the original S kernel.
This uses no parity hypothesis on a spectral measure. -/
theorem cosine_resolvent (s : ℝ) :
    Integrable (fun w : ℝ => Real.cos (w * s) / (1 + 4 * w ^ 2)) ∧
    (1 / (2 * Real.pi)) *
      (∫ w : ℝ, Real.cos (w * s) / (1 + 4 * w ^ 2)) = Real.exp (-|s| / 2) / 4 := by
  have hi : Integrable (fun w : ℝ => (angularIntegrand s w).re) :=
    (angular_integrable s).re
  have he : (fun w : ℝ => (angularIntegrand s w).re) =
      fun w : ℝ => Real.cos (w * s) / (1 + 4 * w ^ 2) := funext (integrand_re s)
  rw [he] at hi
  refine ⟨hi, ?_⟩
  have hr := congrArg Complex.re (normalized_integral s)
  have hint : (∫ w : ℝ, angularIntegrand s w).re =
      ∫ w : ℝ, Real.cos (w * s) / (1 + 4 * w ^ 2) := by
    calc
      (∫ w : ℝ, angularIntegrand s w).re =
          ∫ w : ℝ, (angularIntegrand s w).re :=
        (integral_re (angular_integrable s)).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with w
        exact integrand_re s w
  have hr' : (1 / (2 * Real.pi)) *
      (∫ w : ℝ, Real.cos (w * s) / (1 + 4 * w ^ 2)) =
      Real.exp (-|s| / 2) / 4 := by
    change (↑(1 / (2 * Real.pi)) * ∫ w : ℝ, angularIntegrand s w).re =
      ((Real.exp (-|s| / 2) : ℂ) / (4 : ℂ)).re at hr
    norm_num [Complex.mul_re, Complex.div_re] at hr
    have harg : (-(↑(|s| : ℝ) : ℂ) / 2) = ((-|s| / 2 : ℝ) : ℂ) := by
      push_cast
      ring
    have hreal : (Complex.exp (-(↑(|s| : ℝ) : ℂ) / 2)).re =
        Real.exp (-|s| / 2) := by
      rw [harg, Complex.exp_ofReal_re]
    rw [hreal] at hr
    rw [hint] at hr
    simpa using hr
  exact hr'

end OriginalAngularResolvent
