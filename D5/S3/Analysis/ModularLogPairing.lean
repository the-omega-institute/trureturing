/- GID: D5/S3/Analysis/ModularLogPairing
   generality: G
   mirror-B: none(waiver:covered-by-null-diamond-profile-fourier4-d-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The radial logarithmic form decomposes into the distance, logarithmic tail and oriented sign pairings. -/

import OmegaBuild.Commands
import D5.S3.Analysis.FourierTestSeparation
import D5.S3.Analysis.LogarithmicFourierTail
import D5.S3.Analysis.SignedRadialPairing
import D5.S3.Analysis.LogisticCoordinate
import D5.S3.Analysis.RightHalfPlaneLogIntegral
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
Omega original.

The radial logarithmic form decomposes into the distance, logarithmic tail and
oriented sign pairings. This calculation uses the Fourier convention with
frequency parameter ξ and angular frequency 2πξ.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter MeasureTheory MeasureTheory.Measure Set
open scoped FourierTransform Convolution

namespace Omega

/-- The three ordinary radial integrals defining the modular logarithmic pairing. -/
def modularLogPairing (f g : SchwartzMap ℝ ℂ) : ℂ :=
  -(∫ s : ℝ, star (deriv f s) * ∫ t : ℝ, ((|s - t| : ℝ) : ℂ) * deriv g t) +
    (Real.pi : ℂ)⁻¹ *
      (∫ s : ℝ, star (deriv f s) * ∫ t : ℝ, logTail (s - t) * deriv g t) -
    (Complex.I / 2) *
      (∫ s : ℝ, star (deriv f s) * ∫ t : ℝ, radialSign (s - t) * deriv g t)

private theorem fourier_deriv_schwartz (f : SchwartzMap ℝ ℂ) (ξ : ℝ) :
    𝓕 (SchwartzMap.derivCLM ℂ ℂ f) ξ =
      (Complex.I * ((2 * Real.pi * ξ : ℝ) : ℂ)) * 𝓕 f ξ := by
  rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe]
  change 𝓕 (deriv (f : ℝ → ℂ)) ξ = _
  rw [Real.fourier_deriv f.integrable f.differentiable
    (show Integrable (deriv (f : ℝ → ℂ)) from (SchwartzMap.derivCLM ℂ ℂ f).integrable)]
  simp only [smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_ofNat]
  ring

private theorem logTail_fourier (ξ : ℝ) :
    𝓕 logTail ξ = ((𝓕 logTail ξ).re : ℂ) := by
  have h := logarithmic_mode_integral (2 * Real.pi * ξ)
  have he : 𝓕 logTail ξ =
      ∫ s : ℝ, Complex.exp (-Complex.I * ((2 * Real.pi * ξ : ℝ) : ℂ) * s) *
        logTail s := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    apply integral_congr_ae
    filter_upwards with s
    rw [smul_eq_mul]
    push_cast
    congr 2
    ring
  rw [he, h, ← Complex.ofReal_tsum, Complex.ofReal_re]

/-- The modular logarithmic pairing has the real symbol obtained from the
distance value, the Fourier transform of the tail, and the orientation term. -/
theorem modularLogPairing_eq_fourier (f g : SchwartzMap ℝ ℂ)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g) :
    modularLogPairing f g =
      (∫ ξ : ℝ, star (𝓕 f ξ) *
        ((2 + ((2 * Real.pi * ξ) ^ 2 / Real.pi) * (𝓕 logTail ξ).re -
          2 * Real.pi * ξ : ℝ) : ℂ) * 𝓕 g ξ) := by
  let f' := SchwartzMap.derivCLM ℂ ℂ f
  let g' := SchwartzMap.derivCLM ℂ ℂ g
  let B := ContinuousLinearMap.mul ℂ ℂ
  let C := (g' : ℝ → ℂ) ⋆[B] logTail
  have hC : Integrable C := g'.integrable.integrable_convolution B integrable_logTail
  have hconv (s : ℝ) : (∫ t : ℝ, logTail (s - t) * deriv g t) = C s := by
    change _ = ∫ t : ℝ, deriv g t * logTail (s - t)
    exact integral_congr_ae (.of_forall fun t => mul_comm _ _)
  have hd (ξ : ℝ) : 𝓕 C ξ = 𝓕 g' ξ * 𝓕 logTail ξ := by
    exact Real.fourier_mul_convolution_eq g'.integrable integrable_logTail ξ
  let cf := SchwartzMap.postcompCLM Complex.conjCLE.toContinuousLinearMap f
  have hcf : (cf : ℝ → ℂ) = fun t => star (f t) := rfl
  have hcf' (t : ℝ) : deriv (cf : ℝ → ℂ) t = star (deriv f t) := by
    exact (Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t
      (f.hasDerivAt t)).deriv
  have hcfc : HasCompactSupport cf := by
    rw [hcf]
    exact hf.comp_left (star_zero ℂ)
  have hdist := integral_abs_sub_deriv_pairing (cf.smooth 1) hcfc (g.smooth 1) hg
  simp_rw [hcf', hcf] at hdist
  have hsign (s : ℝ) : (∫ t : ℝ, radialSign (s-t) * deriv g t) = 2 * g s :=
    integral_radialSign_deriv (g.smooth 1) hg s
  have htail : (∫ s : ℝ, star (deriv f s) * C s) =
      ∫ ξ : ℝ, star (𝓕 f' ξ) * (𝓕 g' ξ * 𝓕 logTail ξ) := by
    have h := integral_fourier_inner_test hC f'
    simp_rw [hd] at h
    exact h
  have hlocal := integral_fourier_inner_test g.integrable f
  have hlocal' := integral_fourier_inner_test g.integrable f'
  have hsgn : (∫ s : ℝ, star (deriv f s) * ∫ t : ℝ, radialSign (s - t) * deriv g t) =
      (2 : ℂ) * ∫ s, star (f' s) * g s := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with s
    rw [hsign s]
    change star (f' s) * (2 * g s) = _
    ring
  have hpositive : modularLogPairing f g =
      (2 : ℂ) * (∫ ξ : ℝ, star (𝓕 f ξ) * 𝓕 g ξ) +
        (Real.pi : ℂ)⁻¹ * (∫ ξ : ℝ, star (𝓕 f' ξ) * (𝓕 g' ξ * 𝓕 logTail ξ)) -
        Complex.I * (∫ ξ : ℝ, star (𝓕 f' ξ) * 𝓕 g ξ) := by
    unfold modularLogPairing
    rw [hdist, hsgn]
    simp_rw [hconv]
    rw [htail, hlocal, hlocal']
    simp only [SchwartzMap.fourier_coe]
    ring
  -- Bring the three Fourier terms under one integral.
  have hfirst : Integrable (fun ξ : ℝ => star (𝓕 f ξ) * 𝓕 g ξ) := by
    have hm := (𝓕 f : SchwartzMap ℝ ℂ).continuous.star.mul
      (𝓕 g : SchwartzMap ℝ ℂ).continuous
    refine ((𝓕 g : SchwartzMap ℝ ℂ).integrable.norm.const_mul
      (SchwartzMap.seminorm ℝ 0 0 (𝓕 f))).mono' hm.aestronglyMeasurable ?_
    filter_upwards with ξ
    rw [norm_mul, norm_star]
    exact mul_le_mul_of_nonneg_right ((𝓕 f : SchwartzMap ℝ ℂ).norm_le_seminorm ℝ ξ)
      (norm_nonneg _)
  have hthird : Integrable (fun ξ : ℝ => star (𝓕 f' ξ) * 𝓕 g ξ) := by
    have hm := (𝓕 f' : SchwartzMap ℝ ℂ).continuous.star.mul
      (𝓕 g : SchwartzMap ℝ ℂ).continuous
    refine ((𝓕 g : SchwartzMap ℝ ℂ).integrable.norm.const_mul
      (SchwartzMap.seminorm ℝ 0 0 (𝓕 f'))).mono' hm.aestronglyMeasurable ?_
    filter_upwards with ξ
    rw [norm_mul, norm_star]
    exact mul_le_mul_of_nonneg_right ((𝓕 f' : SchwartzMap ℝ ℂ).norm_le_seminorm ℝ ξ)
      (norm_nonneg _)
  have hsecond : Integrable (fun ξ : ℝ => star (𝓕 f' ξ) *
      (𝓕 g' ξ * 𝓕 logTail ξ)) := by
    have hCcont : Continuous (𝓕 C) :=
      VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
        (innerSL ℝ).continuous₂ hC
    simp_rw [← hd]
    apply ((𝓕 f' : SchwartzMap ℝ ℂ).integrable.norm.mul_const (∫ x, ‖C x‖)).mono'
      (((𝓕 f' : SchwartzMap ℝ ℂ).continuous.star).mul hCcont).aestronglyMeasurable
    filter_upwards with ξ
    change ‖star (𝓕 f' ξ) * 𝓕 C ξ‖ ≤ _
    rw [norm_mul, norm_star]
    exact mul_le_mul_of_nonneg_left (Real.norm_fourier_le_integral_norm C ξ) (norm_nonneg _)
  rw [hpositive, ← integral_const_mul, ← integral_const_mul, ← integral_const_mul]
  rw [← integral_add (hfirst.const_mul _) (hsecond.const_mul _)]
  have hsum : Integrable (fun ξ : ℝ =>
      2 * (star (𝓕 f ξ) * 𝓕 g ξ) +
        (Real.pi : ℂ)⁻¹ * (star (𝓕 f' ξ) * (𝓕 g' ξ * 𝓕 logTail ξ))) :=
    (hfirst.const_mul 2).add (hsecond.const_mul (Real.pi : ℂ)⁻¹)
  rw [← integral_sub hsum (hthird.const_mul Complex.I)]
  apply integral_congr_ae
  filter_upwards with ξ
  rw [fourier_deriv_schwartz, fourier_deriv_schwartz, logTail_fourier]
  simp only [star_mul, Complex.star_def, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_re]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring


private def radius (s : ℝ) : ℝ := logistic (2 * Real.pi) s

private def oneRadiusTerm (s : ℝ) : ℝ :=
  Real.pi * s - Real.log (1 + Real.exp (2 * Real.pi * s))

/-- The affine boundary logarithm in modular coordinates. Its nonlocal part
is the hyperbolic logarithm with the oriented imaginary term. -/
theorem affine_log_in_modular_coordinates {s t : ℝ} (hst : s ≠ t) :
    Complex.log (Complex.I * ((2 * (logistic (2 * Real.pi) s -
      logistic (2 * Real.pi) t) : ℝ) : ℂ)) =
      (((Real.pi * |s - t| : ℝ) : ℂ) - logTail (s - t)) +
      ((Real.pi : ℂ) / 2) * Complex.I * radialSign (s - t) +
      ((oneRadiusTerm s + oneRadiusTerm t + Real.log 2 : ℝ) : ℂ) := by
  have hscale : (0 : ℝ) < 2 * Real.pi := by positivity
  have hmono := strictMono_logistic hscale
  have hn : radius s - radius t ≠ 0 := sub_ne_zero.mpr (hmono.injective.ne hst)
  have hl := log_logistic_sub hscale hst
  have hs : (2 * Real.pi / 2 : ℝ) = Real.pi := by ring
  have hpos : 0 < 2 * (radius s - radius t) ↔ 0 < s - t := by
    rw [mul_pos_iff_of_pos_left (by norm_num : (0 : ℝ) < 2), sub_pos, sub_pos]
    exact hmono.lt_iff_lt
  change Complex.log (Complex.I * ((2 * (radius s - radius t) : ℝ) : ℂ)) = _
  rw [log_I_mul_real (mul_ne_zero (by norm_num) hn), abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 2),
    Real.log_mul (by norm_num) (abs_ne_zero.mpr hn)]
  unfold radius at *
  rw [hl, hs]
  have hk := log_two_abs_sinh (s - t) (sub_ne_zero.mpr hst)
  unfold oneRadiusTerm
  push_cast
  rw [hk]
  by_cases hp : 0 < s - t
  · simp [radialSign, hp, hpos.mpr hp]
    ring
  · simp [radialSign, hp, mt hpos.mp hp]
    ring


private theorem integral_deriv_schwartz_eq_zero (f : SchwartzMap ℝ ℂ)
    (hf : HasCompactSupport f) : (∫ s, deriv f s) = 0 := by
  have hi : Integrable (deriv f) := (SchwartzMap.derivCLM ℂ ℂ f).integrable
  rw [← integral_add_compl (s := Iic (0 : ℝ)) measurableSet_Iic hi, compl_Iic,
    hf.integral_Iic_deriv_eq (f.smooth 1), hf.integral_Ioi_deriv_eq (f.smooth 1), add_neg_cancel]

/-- An affine derivative has zero integral when its transported derivative
has a compactly supported primitive. -/
theorem integral_affine_derivative_eq_zero (f : SchwartzMap ℝ ℂ)
    (hf : HasCompactSupport f) {F' : ℝ → ℂ}
    (hF : ∀ s, deriv f s = ((2 * Real.pi * (logistic (2 * Real.pi) s *
      (1 - logistic (2 * Real.pi) s)) : ℝ) : ℂ) * F' (logistic (2 * Real.pi) s)) :
    (∫ u in Ioo (0 : ℝ) 1, F' u) = 0 := by
  rw [integral_logistic_substitution (by positivity : 0 < 2 * Real.pi)]
  simp only [Complex.real_smul, ← hF, integral_deriv_schwartz_eq_zero f hf]

private abbrev radialVolume : Measure (ℝ × ℝ) := (volume : Measure ℝ).prod volume

private abbrev affineVolume : Measure (ℝ × ℝ) :=
  (volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))

/-- The principal logarithm of affine separation is integrable with bounded
measurable coefficients on the product of unit radial intervals. -/
theorem integrable_affine_log_mul {H : ℝ × ℝ → ℂ} (hH : Measurable H)
    {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ᵐ p ∂affineVolume, ‖H p‖ ≤ B) :
    Integrable (fun p : ℝ × ℝ => H p * Complex.log (Complex.I *
      ((2 * (p.1 - p.2) : ℝ) : ℂ))) affineVolume := by
  let x : ℝ × ℝ → ℝ := fun p => 2 * (p.1 - p.2)
  have hx : Measurable x := by dsimp [x]; fun_prop
  have hl : Measurable (fun p => Complex.log (Complex.I * (x p : ℂ))) :=
    Complex.measurable_log.comp (measurable_const.mul (Complex.continuous_ofReal.measurable.comp hx))
  have hi : Integrable (fun p : ℝ × ℝ => B * (|Real.log (|x p|)| + Real.pi / 2)) affineVolume :=
    (integrable_log_difference_unit.add (integrable_const (Real.pi / 2))).const_mul B
  apply hi.mono' (hH.mul hl).aestronglyMeasurable
  filter_upwards [hb] with p hp
  have hlog : ‖Complex.log (Complex.I * (x p : ℂ))‖ ≤ |Real.log (|x p|)| + Real.pi / 2 := by
    by_cases hz : x p = 0
    · simp [hz]
      positivity
    · rw [log_I_mul_real hz]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs]
      split <;> simp [abs_of_nonneg (by positivity : 0 ≤ Real.pi / 2)]
  change ‖H p * Complex.log (Complex.I * (x p : ℂ))‖ ≤ _
  rw [norm_mul]
  exact mul_le_mul hp hlog (norm_nonneg _) hB

private theorem affine_log_integrable {F' G' : ℝ → ℂ} (hF : Continuous F') (hG : Continuous G') :
    Integrable (fun p : ℝ × ℝ => star (F' p.1) * G' p.2 *
      Complex.log (Complex.I * ((2 * (p.1 - p.2) : ℝ) : ℂ))) affineVolume := by
  let H : ℝ × ℝ → ℂ := fun p => star (F' p.1) * G' p.2
  have hH : Continuous H := (hF.comp continuous_fst).star.mul (hG.comp continuous_snd)
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod isCompact_Icc :
    IsCompact (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)).exists_bound_of_continuousOn hH.continuousOn
  refine integrable_affine_log_mul hH.measurable (le_max_left (0 : ℝ) B) ?_
  have hμ : ∀ᵐ u ∂volume.restrict (Ioo (0 : ℝ) 1), u ∈ Ioo (0 : ℝ) 1 :=
    ae_restrict_mem measurableSet_Ioo
  have h := (ae_prod_iff_ae_ae (p := fun p : ℝ × ℝ => p ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)
    (measurableSet_Ioo.prod measurableSet_Ioo)).2
    (hμ.mono fun _ hu => hμ.mono fun _ hv => ⟨hu, hv⟩)
  exact h.mono fun p hp =>
    (hB p ⟨Ioo_subset_Icc_self hp.1, Ioo_subset_Icc_self hp.2⟩).trans (le_max_right _ _)

/-- Logistic substitution in both coordinates of an integrable affine pairing. -/
theorem integral_logistic_pair (K : ℝ × ℝ → ℂ)
    (hK : Integrable K affineVolume) :
    (∫ p, K p ∂affineVolume) =
      ∫ s : ℝ, ∫ t : ℝ,
        ((2 * Real.pi * (logistic (2 * Real.pi) s * (1 - logistic (2 * Real.pi) s)) : ℝ) : ℂ) *
        ((2 * Real.pi * (logistic (2 * Real.pi) t * (1 - logistic (2 * Real.pi) t)) : ℝ) : ℂ) *
        K (logistic (2 * Real.pi) s, logistic (2 * Real.pi) t) := by
  have hpos : (0 : ℝ) < 2 * Real.pi := by positivity
  rw [integral_prod _ hK, integral_logistic_substitution hpos]
  apply integral_congr_ae
  refine .of_forall fun s => ?_
  dsimp only
  rw [integral_logistic_substitution hpos, Complex.real_smul, ← integral_const_mul]
  apply integral_congr_ae
  exact .of_forall fun t => by
    dsimp only
    rw [Complex.real_smul]
    exact (mul_assoc _ _ _).symm


private theorem integral_modular_log_pairing (f g : SchwartzMap ℝ ℂ)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g) :
    -(Real.pi : ℂ)⁻¹ * (∫ s : ℝ, ∫ t : ℝ, star (deriv f s) * deriv g t *
      Complex.log (Complex.I * ((2 * (radius s - radius t) : ℝ) : ℂ))) =
      modularLogPairing f g := by
  let F : ℝ → ℂ := fun s => star (deriv f s)
  let G : SchwartzMap ℝ ℂ := SchwartzMap.derivCLM ℂ ℂ g
  let W : ℝ × ℝ → ℂ := fun p => F p.1 * G p.2
  let D : ℝ × ℝ → ℂ := fun p => W p * ((|p.1 - p.2| : ℝ) : ℂ)
  let T : ℝ × ℝ → ℂ := fun p => W p * logTail (p.1 - p.2)
  let S : ℝ × ℝ → ℂ := fun p => W p * radialSign (p.1 - p.2)
  let U : ℝ → ℂ := fun s => (oneRadiusTerm s : ℂ)
  let L : ℝ × ℝ → ℂ := fun p => W p *
    Complex.log (Complex.I * ((2 * (radius p.1 - radius p.2) : ℝ) : ℂ))
  have hFc : Continuous F := (SchwartzMap.derivCLM ℂ ℂ f).continuous.star
  have hFs : HasCompactSupport F := hf.deriv.comp_left (star_zero ℂ)
  have hGs : HasCompactSupport G := hg.deriv
  have hF : Integrable F := hFc.integrable_of_hasCompactSupport hFs
  have hG : Integrable G := G.integrable
  have hF0 : (∫ s, F s) = 0 := by
    simp only [F, Complex.star_def, integral_conj, integral_deriv_schwartz_eq_zero f hf, map_zero]
  have hG0 : (∫ t, G t) = 0 := integral_deriv_schwartz_eq_zero g hg
  have hW : Integrable W radialVolume := hF.mul_prod hG
  have hD : Integrable D radialVolume := by
    have hF₁ : Integrable (fun s => |s| * ‖F s‖) :=
      (continuous_abs.mul hFc.norm).integrable_of_hasCompactSupport hFs.norm.mul_left
    have hG₁ : Integrable (fun t => |t| * ‖G t‖) :=
      (continuous_abs.mul G.continuous.norm).integrable_of_hasCompactSupport hGs.norm.mul_left
    have hDc : Continuous D := by
      dsimp [D, W]
      fun_prop
    refine ((hF₁.mul_prod hG.norm).add (hF.norm.mul_prod hG₁)).mono'
      hDc.aestronglyMeasurable (.of_forall fun p => ?_)
    simp only [D, W, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_abs,
      Pi.add_apply]
    calc
      _ ≤ (‖F p.1‖ * ‖G p.2‖) * (|p.1| + |p.2|) := by
        gcongr
        exact abs_sub _ _
      _ = _ := by ring
  have hT : Integrable T radialVolume := by
    let B := ContinuousLinearMap.mul ℂ ℂ
    have h := hG.convolution_integrand B integrable_logTail (μ := (volume : Measure ℝ))
    change Integrable (fun p : ℝ × ℝ => G p.2 * logTail (p.1 - p.2)) radialVolume at h
    have hm : AEStronglyMeasurable T radialVolume := by
      have hm' := hF.aestronglyMeasurable.comp_fst.mul h.aestronglyMeasurable
      change AEStronglyMeasurable (fun p : ℝ × ℝ => F p.1 * (G p.2 * logTail (p.1 - p.2)))
        radialVolume at hm'
      simpa only [T, W, mul_assoc] using hm'
    refine (h.norm.const_mul (SchwartzMap.seminorm ℝ 0 0 (SchwartzMap.derivCLM ℂ ℂ f))).mono'
      hm (.of_forall fun p => ?_)
    simp only [T, W, norm_mul, mul_assoc]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    rw [show ‖F p.1‖ = ‖(SchwartzMap.derivCLM ℂ ℂ f) p.1‖ from norm_star _]
    exact (SchwartzMap.derivCLM ℂ ℂ f).norm_le_seminorm ℝ p.1
  have hS : Integrable S radialVolume := by
    have hm : Measurable radialSign := by
      unfold radialSign
      exact Measurable.ite measurableSet_Ioi measurable_const measurable_const
    have hnorm (r : ℝ) : ‖radialSign r‖ = 1 := by
      unfold radialSign
      split <;> simp
    refine hW.norm.mono' (hW.aestronglyMeasurable.mul
      (hm.comp (measurable_fst.sub measurable_snd)).aestronglyMeasurable) (.of_forall fun p => ?_)
    simp only [S, norm_mul, hnorm, mul_one, le_refl]
  have hU : Continuous U := by
    have h : Continuous (fun s : ℝ => Real.log (1 + Real.exp (2 * Real.pi * s))) :=
      (continuous_const.add (Real.continuous_exp.comp (continuous_const.mul continuous_id))).log
        (fun s => ne_of_gt (show 0 < 1 + Real.exp (2 * Real.pi * s) by positivity))
    exact Complex.continuous_ofReal.comp ((continuous_const.mul continuous_id).sub h)
  have hUF : Integrable (fun s => F s * U s) :=
    (hFc.mul hU).integrable_of_hasCompactSupport hFs.mul_right
  have hUG : Integrable (fun t => G t * U t) :=
    (G.continuous.mul hU).integrable_of_hasCompactSupport hGs.mul_right
  let F₁ : ℝ × ℝ → ℂ := fun p => (F p.1 * U p.1) * G p.2
  let G₁ : ℝ × ℝ → ℂ := fun p => F p.1 * (G p.2 * U p.2)
  let c : ℂ := Real.log 2
  let a : ℂ := Real.pi
  let b : ℂ := a / 2 * Complex.I
  have hne : ∀ᵐ p : ℝ × ℝ ∂radialVolume, p.1 ≠ p.2 := by
    apply (ae_prod_iff_ae_ae (measurableSet_eq_fun measurable_fst measurable_snd).compl).2
    exact .of_forall fun s => by rw [ae_iff]; simp
  have hL : L =ᵐ[radialVolume] fun p => a * D p - T p + b * S p + F₁ p + G₁ p + W p * c := by
    filter_upwards [hne] with p hp
    dsimp only [L, radius]
    rw [affine_log_in_modular_coordinates hp]
    dsimp only [D, T, S, F₁, G₁, U, W, a, b, c]
    push_cast
    ring
  have hDT := (hD.const_mul a).sub hT
  have hDTS := hDT.add (hS.const_mul b)
  have hF₁ : Integrable F₁ radialVolume := hUF.mul_prod hG
  have hG₁ : Integrable G₁ radialVolume := hF.mul_prod hUG
  have hL' : Integrable L radialVolume :=
    (((hDTS.add hF₁).add hG₁).add (hW.mul_const c)).congr hL.symm
  change -_ * (∫ s : ℝ, ∫ t : ℝ, L (s,t)) = _
  rw [← integral_prod _ hL', integral_congr_ae hL]
  have e₁ := integral_add ((hDTS.add hF₁).add hG₁) (hW.mul_const c)
  have e₂ := integral_add (hDTS.add hF₁) hG₁
  have e₃ := integral_add hDTS hF₁
  have e₄ := integral_add hDT (hS.const_mul b)
  have e₅ := integral_sub (hD.const_mul a) hT
  simp only [Pi.add_apply, Pi.sub_apply] at e₁ e₂ e₃ e₄ e₅
  rw [e₁, e₂, e₃, e₄, e₅]
  have hzero₁ : (∫ p, F₁ p ∂radialVolume) = 0 := by
    unfold F₁
    rw [integral_prod_mul (fun s => F s * U s) (G : ℝ → ℂ), hG0, mul_zero]
  have hzero₂ : (∫ p, G₁ p ∂radialVolume) = 0 := by
    unfold G₁
    rw [integral_prod_mul F (fun t => G t * U t), hF0, zero_mul]
  have hzero : (∫ p, W p ∂radialVolume) = 0 := by
    unfold W
    rw [integral_prod_mul, hF0, zero_mul]
  rw [integral_const_mul, integral_const_mul, integral_mul_const, hzero₁, hzero₂, hzero]
  simp only [add_zero, zero_mul]
  have hiter (k : ℝ × ℝ → ℂ) (hk : Integrable (fun p => W p * k p) radialVolume) :
      (∫ p, W p * k p ∂radialVolume) = ∫ s : ℝ, F s * ∫ t : ℝ, k (s,t) * G t := by
    rw [integral_prod _ hk]
    apply integral_congr_ae
    refine .of_forall fun s => ?_
    dsimp only
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact .of_forall fun t => by dsimp [W]; ring
  rw [hiter (fun p => ((|p.1 - p.2| : ℝ) : ℂ)) hD,
    hiter (fun p => logTail (p.1 - p.2)) hT, hiter (fun p => radialSign (p.1 - p.2)) hS]
  unfold modularLogPairing
  have hderiv (t : ℝ) : G t = deriv g t := rfl
  simp only [a, b, F, hderiv]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp [hpi]
  ring

/-- The affine logarithmic boundary pairing becomes the modular logarithmic
pairing after transporting both derivatives and canceling the one-radius terms. -/
theorem affine_log_pairing_eq_modular (f g : SchwartzMap ℝ ℂ)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g) {F' G' : ℝ → ℂ}
    (hFc : Continuous F') (hGc : Continuous G')
    (hF : ∀ s, deriv f s = ((2 * Real.pi * (logistic (2 * Real.pi) s *
      (1 - logistic (2 * Real.pi) s)) : ℝ) : ℂ) * F' (logistic (2 * Real.pi) s))
    (hG : ∀ t, deriv g t = ((2 * Real.pi * (logistic (2 * Real.pi) t *
      (1 - logistic (2 * Real.pi) t)) : ℝ) : ℂ) * G' (logistic (2 * Real.pi) t)) :
    -(Real.pi : ℂ)⁻¹ * (∫ p : ℝ × ℝ, star (F' p.1) * G' p.2 *
      Complex.log (Complex.I * ((2 * (p.1 - p.2) : ℝ) : ℂ)) ∂affineVolume) =
      modularLogPairing f g := by
  rw [integral_logistic_pair _ (affine_log_integrable hFc hGc)]
  refine (congrArg (fun z : ℂ => -(Real.pi : ℂ)⁻¹ * z) ?_).trans
    (integral_modular_log_pairing f g hf hg)
  apply integral_congr_ae
  refine .of_forall fun s => ?_
  apply integral_congr_ae
  refine .of_forall fun t => ?_
  simp only [hF s, hG t, star_mul, Complex.star_def, Complex.conj_ofReal, radius]
  ring

end Omega
