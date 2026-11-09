/- GID: D5/S3/Analytic/Fourier/GaussianKernel
   generality: G
   mirror-B: D5/B/S3/Analytic/Fourier/GaussianKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Gaussian kernels have explicit transforms and controlled half-line corrections. -/

import D5.S3.Analytic.Fourier.AngularFejerKernel
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic

/-! Gaussian transforms, vertical-line inversion, and half-line cosine correction. -/

namespace D5.S3.Analytic.Fourier.GaussianKernel

open MeasureTheory Set Filter
open scoped Topology

noncomputable def q (M v : ℝ) : ℝ :=
  M / Real.sqrt (2 * Real.pi) * Real.exp (-M ^ 2 * v ^ 2 / 2)

noncomputable def gaussianAverage (f : ℝ → ℝ) (M y : ℝ) : ℝ :=
  ∫ u in Set.Ici (0 : ℝ), f u * q M (y - u)

private lemma q_integrable {M : ℝ} (hM : 0 < M) : Integrable (q M) := by
  convert (integrable_exp_neg_mul_sq (show 0 < M ^ 2 / 2 by positivity)).const_mul
    (M / Real.sqrt (2 * Real.pi)) using 1
  ext v
  unfold q
  congr 2
  ring

private lemma q_nonneg {M : ℝ} (hM : 0 < M) (v : ℝ) : 0 ≤ q M v := by
  unfold q
  positivity

private lemma gaussian_normalization {M : ℝ} (hM : 0 < M) :
    M / Real.sqrt (2 * Real.pi) * Real.sqrt (Real.pi / (M ^ 2 / 2)) = 1 := by
  have hs : Real.sqrt (Real.pi / (M ^ 2 / 2)) = Real.sqrt (2 * Real.pi) / M := by
    apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr
    rw [div_pow, Real.sq_sqrt (by positivity)]
    field_simp
  rw [hs]
  field_simp

/-- The positive Gaussian is an integrable probability density. -/
theorem q_laws {M : ℝ} (hM : 0 < M) :
    Integrable (q M) ∧ (∀ v, 0 ≤ q M v) ∧ (∫ v, q M v) = 1 := by
  refine ⟨q_integrable hM, q_nonneg hM, ?_⟩
  have he : q M = fun v => M / Real.sqrt (2 * Real.pi) *
      Real.exp (-(M ^ 2 / 2) * v ^ 2) := by
    ext v
    unfold q
    congr 2
    ring
  rw [he, integral_const_mul, integral_gaussian]
  exact gaussian_normalization hM

private lemma complex_gaussian_factor {b : ℝ} (hb : 0 < b) :
    ((Real.pi : ℂ) / (b : ℂ)) ^ (1 / 2 : ℂ) = (Real.sqrt (Real.pi / b) : ℂ) := by
  rw [Real.sqrt_eq_rpow]
  simpa only [Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_one] using
    (Complex.ofReal_cpow (show 0 ≤ Real.pi / b by positivity) (1 / 2 : ℝ)).symm

private lemma complex_gaussian_transform {b : ℝ} (hb : 0 < b) (t : ℝ) :
    (∫ x : ℝ, (Real.exp (-b * x ^ 2) : ℂ) *
      Complex.exp (-Complex.I * (t : ℂ) * x)) =
    (Real.sqrt (Real.pi / b) * Real.exp (-t ^ 2 / (4 * b)) : ℝ) := by
  have h := fourierIntegral_gaussian (show 0 < (b : ℂ).re by simpa) (-t : ℝ)
  rw [complex_gaussian_factor hb] at h
  convert h using 1
  · apply integral_congr_ae
    filter_upwards with x
    push_cast
    rw [mul_comm]
    congr 2
    ring
  · push_cast
    simp

private lemma q_complex_transform {M : ℝ} (hM : 0 < M) (t : ℝ) :
    (∫ v : ℝ, (q M v : ℂ) * Complex.exp (-Complex.I * (t : ℂ) * v)) =
      (Real.exp (-t ^ 2 / (2 * M ^ 2)) : ℂ) := by
  have he (v : ℝ) : (q M v : ℂ) * Complex.exp (-Complex.I * (t : ℂ) * v) =
      (M / Real.sqrt (2 * Real.pi) : ℝ) *
        ((Real.exp (-(M ^ 2 / 2) * v ^ 2) : ℂ) *
          Complex.exp (-Complex.I * (t : ℂ) * v)) := by
    have he : -M ^ 2 * v ^ 2 / 2 = -(M ^ 2 / 2) * v ^ 2 := by ring
    simp only [q, he, Complex.ofReal_mul, mul_assoc]
  simp_rw [he]
  rw [integral_const_mul, complex_gaussian_transform (show 0 < M ^ 2 / 2 by positivity)]
  rw [← Complex.ofReal_mul]
  congr 1
  rw [← mul_assoc, gaussian_normalization hM, one_mul]
  congr 1
  field_simp
  ring

lemma bromwich_exponent (M c v t : ℝ) :
    ((c : ℂ) + t * Complex.I) * v + ((c : ℂ) + t * Complex.I) ^ 2 / (2 * M ^ 2) =
      -(1 / (2 * (M : ℂ) ^ 2)) * (t : ℂ) ^ 2 +
        (Complex.I * ((v : ℂ) + c / M ^ 2)) * t +
          ((c : ℂ) * v + c ^ 2 / (2 * M ^ 2)) := by
  by_cases hM : M = 0
  · subst M; simp; ring
  · have hMc : (M : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hM
    field_simp
    ring_nf
    simp only [Complex.I_sq]
    ring

/-- Every real vertical line gives an absolutely integrable Gaussian inversion integral. -/
theorem q_bromwich_integrable {M : ℝ} (hM : 0 < M) (c v : ℝ) :
    Integrable (fun t : ℝ => Complex.exp
      (((c : ℂ) + t * Complex.I) * v + ((c : ℂ) + t * Complex.I) ^ 2 / (2 * M ^ 2))) := by
  simp_rw [bromwich_exponent]
  have hb : 0 < (((1 / (2 * M ^ 2) : ℝ) : ℂ)).re := by
    exact (show 0 < (1 / (2 * M ^ 2) : ℝ) by positivity)
  push_cast at hb
  exact integrable_cexp_quadratic hb _ _

/-- Gaussian inversion along any vertical line, with angular-frequency normalization. -/
theorem q_bromwich {M : ℝ} (hM : 0 < M) (c v : ℝ) :
    (q M v : ℂ) = (1 / (2 * Real.pi) : ℂ) *
      ∫ t : ℝ, Complex.exp
        (((c : ℂ) + t * Complex.I) * v + ((c : ℂ) + t * Complex.I) ^ 2 / (2 * M ^ 2)) := by
  have hM0 : M ≠ 0 := ne_of_gt hM
  have hMc : (M : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hM0
  have hs : Real.sqrt (Real.pi / (1 / (2 * M ^ 2))) = M * Real.sqrt (2 * Real.pi) := by
    apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    field_simp
  have he : (c : ℂ) * v + c ^ 2 / (2 * M ^ 2) -
      (Complex.I * ((v : ℂ) + c / M ^ 2)) ^ 2 / (4 * (-(1 / (2 * M ^ 2)))) =
        ((-M ^ 2 * v ^ 2 / 2 : ℝ) : ℂ) := by
    push_cast
    field_simp
    simp only [Complex.I_sq]
    ring
  simp_rw [bromwich_exponent]
  have hb : (-(1 / (2 * (M : ℂ) ^ 2))).re < 0 := by
    have hb : 0 < (((1 / (2 * M ^ 2) : ℝ) : ℂ)).re := by
      exact (show 0 < (1 / (2 * M ^ 2) : ℝ) by positivity)
    push_cast at hb
    simpa only [Complex.neg_re, neg_lt_zero] using hb
  rw [integral_cexp_quadratic hb, neg_neg]
  have hfactor := complex_gaussian_factor (show 0 < 1 / (2 * M ^ 2) by positivity)
  push_cast at hfactor
  rw [hfactor, he, hs, ← Complex.ofReal_exp]
  push_cast
  unfold q
  push_cast
  have hsq : (Real.sqrt (2 * Real.pi) : ℂ) ^ 2 = 2 * Real.pi := by
    norm_cast
    exact Real.sq_sqrt (by positivity)
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hs0 : (Real.sqrt (2 * Real.pi) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.2 (by positivity)))
  field_simp
  rw [hsq]

/-- Convolution with a cosine multiplies its amplitude by the Gaussian transform. -/
theorem q_cos_convolution {M : ℝ} (hM : 0 < M) (γ y : ℝ) :
    (∫ u, Real.cos (γ * u) * q M (y - u)) =
      Real.exp (-γ ^ 2 / (2 * M ^ 2)) * Real.cos (γ * y) := by
  apply AngularFejerKernel.cosine_convolution (q_integrable hM)
    (w := fun t => Real.exp (-t ^ 2 / (2 * M ^ 2))) _ γ y
  exact q_complex_transform hM

private noncomputable def qd (M w : ℝ) : ℝ := -M ^ 2 * w * q M w

private noncomputable def qdd (M w : ℝ) : ℝ := (M ^ 4 * w ^ 2 - M ^ 2) * q M w

private lemma q_hasDerivAt (M w : ℝ) : HasDerivAt (q M) (qd M w) w := by
  convert (((((hasDerivAt_id w).pow 2).const_mul (-M ^ 2)).div_const 2).exp.const_mul
    (M / Real.sqrt (2 * Real.pi))) using 1
  · rfl
  · simp [q, qd]; ring

private lemma qd_hasDerivAt (M w : ℝ) : HasDerivAt (qd M) (qdd M w) w := by
  convert (((hasDerivAt_id w).const_mul (-M ^ 2)).mul (q_hasDerivAt M w)) using 1
  · rfl
  · simp [qdd, qd]; ring

private lemma qd_integrable {M : ℝ} (hM : 0 < M) : Integrable (qd M) := by
  convert (integrable_mul_exp_neg_mul_sq (show 0 < M ^ 2 / 2 by positivity)).const_mul
    (-M ^ 2 * (M / Real.sqrt (2 * Real.pi))) using 1
  ext w
  have he : -M ^ 2 * w ^ 2 / 2 = -(M ^ 2 / 2) * w ^ 2 := by ring
  simp only [qd, q, he]
  ring

private lemma qdd_integrable {M : ℝ} (hM : 0 < M) : Integrable (qdd M) := by
  have hi := integrable_rpow_mul_exp_neg_mul_sq (show 0 < M ^ 2 / 2 by positivity)
    (show (-1 : ℝ) < 2 by norm_num)
  simp only [Real.rpow_two] at hi
  convert (hi.const_mul (M ^ 4 * (M / Real.sqrt (2 * Real.pi)))).sub
    ((q_integrable hM).const_mul (M ^ 2)) using 1
  ext w
  have he : -M ^ 2 * w ^ 2 / 2 = -(M ^ 2 / 2) * w ^ 2 := by ring
  simp only [qdd, q, he, Pi.sub_apply]
  ring

private lemma q_tendsto {M : ℝ} (hM : 0 < M) : Tendsto (q M) atTop (𝓝 0) := by
  have hs : Tendsto (fun w : ℝ => w ^ 2) atTop atTop := tendsto_pow_atTop (by norm_num)
  have h := Real.tendsto_exp_atBot.comp
    ((tendsto_const_mul_atBot_of_neg (show -(M ^ 2 / 2) < 0 by nlinarith [sq_pos_of_pos hM])).2 hs)
  convert h.const_mul (M / Real.sqrt (2 * Real.pi)) using 1
  · ext w; unfold q; congr 2; ring
  · simp

private lemma qd_tendsto {M : ℝ} (hM : 0 < M) : Tendsto (qd M) atTop (𝓝 0) := by
  have hs : Tendsto (fun w : ℝ => w ^ 2) atTop atTop := tendsto_pow_atTop (by norm_num)
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 / 2)
    (M ^ 2 / 2) (by positivity)).comp hs
  have he : (fun w : ℝ => w * Real.exp (-(M ^ 2 / 2) * w ^ 2)) =ᶠ[atTop]
      (fun w : ℝ => (w ^ 2) ^ (1 / 2 : ℝ) * Real.exp (-(M ^ 2 / 2) * w ^ 2)) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with w hw
    rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hw]
  have h' := h.congr' he.symm
  convert h'.const_mul (-M ^ 2 * (M / Real.sqrt (2 * Real.pi))) using 1
  · ext w
    have hex : -M ^ 2 * w ^ 2 / 2 = -(M ^ 2 / 2) * w ^ 2 := by ring
    simp only [qd, q, hex]
    ring
  · simp

private lemma qdd_nonneg {M w : ℝ} (hM : 1 ≤ M) (hw : 1 ≤ w) : 0 ≤ qdd M w := by
  have hM0 : 0 < M := by linarith
  have hMs : 1 ≤ M ^ 2 := by nlinarith
  have hws : 1 ≤ w ^ 2 := by nlinarith
  have hprod : 1 ≤ M ^ 2 * w ^ 2 := by nlinarith [mul_le_mul_of_nonneg_right hMs (sq_nonneg w)]
  have hcoeff : 0 ≤ M ^ 4 * w ^ 2 - M ^ 2 := by nlinarith [sq_nonneg M]
  exact mul_nonneg hcoeff (q_nonneg hM0 w)

/-- Two integrations by parts control the missing negative half of a cosine convolution. -/
theorem gaussian_halfline_correction {M y γ : ℝ}
    (hM : 1 ≤ M) (hy : 1 ≤ y) (hγ : 0 < γ) :
    |∫ v in Set.Ici (0 : ℝ), Real.cos (γ * v) * q M (y + v)| ≤
      2 * M ^ 2 * y * q M y / γ ^ 2 := by
  have hM0 : 0 < M := by linarith
  have hi0 : Integrable (fun v => q M (y + v)) := (q_integrable hM0).comp_add_left y
  have hi1 : Integrable (fun v => qd M (y + v)) := (qd_integrable hM0).comp_add_left y
  have hi2 : Integrable (fun v => qdd M (y + v)) := (qdd_integrable hM0).comp_add_left y
  have hc : ∀ v : ℝ, ‖Real.cos (γ * v)‖ ≤ 1 := by
    intro v; exact Real.abs_cos_le_one _
  have hs : ∀ v : ℝ, ‖Real.sin (γ * v)‖ ≤ 1 := by
    intro v; exact Real.abs_sin_le_one _
  have hB := (hi0.bdd_mul (by fun_prop) (ae_of_all _ hc)).integrableOn (s := Ioi 0)
  have hJ := (hi1.bdd_mul (by fun_prop) (ae_of_all _ hs)).integrableOn (s := Ioi 0)
  have hK := (hi2.bdd_mul (by fun_prop) (ae_of_all _ hc)).integrableOn (s := Ioi 0)
  have hd0 (v : ℝ) : HasDerivAt (fun v => q M (y + v)) (qd M (y + v)) v := by
    simpa only [Function.comp_def, mul_one] using
      (q_hasDerivAt M (y + v)).comp v ((hasDerivAt_id v).const_add y)
  have hd1 (v : ℝ) : HasDerivAt (fun v => qd M (y + v)) (qdd M (y + v)) v := by
    simpa only [Function.comp_def, mul_one] using
      (qd_hasDerivAt M (y + v)).comp v ((hasDerivAt_id v).const_add y)
  have hshift : Tendsto (fun v : ℝ => y + v) atTop atTop :=
    tendsto_atTop_mono (fun v => le_add_of_nonneg_left (show 0 ≤ y by linarith)) tendsto_id
  have hl0 : Tendsto (fun v => q M (y + v)) atTop (𝓝 0) :=
    (q_tendsto hM0).comp hshift
  have hl1 : Tendsto (fun v => qd M (y + v)) atTop (𝓝 0) :=
    (qd_tendsto hM0).comp hshift
  have hfirst : γ * (∫ v in Ioi (0 : ℝ), Real.cos (γ * v) * q M (y + v)) +
      (∫ v in Ioi (0 : ℝ), Real.sin (γ * v) * qd M (y + v)) = 0 := by
    have hder (v : ℝ) : HasDerivAt (fun v => Real.sin (γ * v) * q M (y + v))
        (γ * (Real.cos (γ * v) * q M (y + v)) +
          Real.sin (γ * v) * qd M (y + v)) v := by
      convert ((((hasDerivAt_id v).const_mul γ).sin).mul (hd0 v)) using 1
      · rfl
      · simp only [id_eq, mul_one]; ring
    have h := integral_Ioi_of_hasDerivAt_of_tendsto' (fun v _ => hder v)
      ((hB.const_mul γ).add hJ)
      (bdd_le_mul_tendsto_zero' 1 (Eventually.of_forall (fun v => Real.abs_sin_le_one (γ * v))) hl0)
    simpa [integral_add (hB.const_mul γ) hJ, integral_const_mul] using h
  have hsecond : -γ * (∫ v in Ioi (0 : ℝ), Real.sin (γ * v) * qd M (y + v)) +
      (∫ v in Ioi (0 : ℝ), Real.cos (γ * v) * qdd M (y + v)) = -qd M y := by
    have hder (v : ℝ) : HasDerivAt (fun v => Real.cos (γ * v) * qd M (y + v))
        (-γ * (Real.sin (γ * v) * qd M (y + v)) +
          Real.cos (γ * v) * qdd M (y + v)) v := by
      convert ((((hasDerivAt_id v).const_mul γ).cos).mul (hd1 v)) using 1
      · rfl
      · simp only [id_eq, mul_one]; ring
    have h := integral_Ioi_of_hasDerivAt_of_tendsto' (fun v _ => hder v)
      ((hJ.const_mul (-γ)).add hK)
      (bdd_le_mul_tendsto_zero' 1 (Eventually.of_forall (fun v => Real.abs_cos_le_one (γ * v))) hl1)
    rw [integral_add (hJ.const_mul (-γ)) hK, integral_const_mul] at h
    simpa using h
  have hmass : (∫ v in Ioi (0 : ℝ), qdd M (y + v)) = -qd M y := by
    simpa using integral_Ioi_of_hasDerivAt_of_tendsto' (a := 0) (fun v _ => hd1 v)
      hi2.integrableOn hl1
  have hKbound : |∫ v in Ioi (0 : ℝ), Real.cos (γ * v) * qdd M (y + v)| ≤ -qd M y := by
    rw [← hmass]
    apply abs_integral_le_integral_abs.trans
    apply integral_mono_ae hK.abs hi2.integrableOn
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    have hpos := qdd_nonneg hM (show 1 ≤ y + v by linarith [hv.out])
    simpa only [abs_mul, abs_of_nonneg hpos, one_mul] using
      mul_le_mul_of_nonneg_right (Real.abs_cos_le_one (γ * v)) hpos
  rw [integral_Ici_eq_integral_Ioi]
  have hid : γ ^ 2 * (∫ v in Ioi (0 : ℝ), Real.cos (γ * v) * q M (y + v)) =
      -qd M y - (∫ v in Ioi (0 : ℝ), Real.cos (γ * v) * qdd M (y + v)) := by
    nlinarith [hfirst, hsecond]
  have hqd : qd M y ≤ 0 := by
    unfold qd
    have := q_nonneg hM0 y
    have hy0 : 0 ≤ y := by linarith
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg M)) hy0) this
  apply (le_div_iff₀ (sq_pos_of_pos hγ)).mpr
  rw [mul_comm, ← abs_of_pos (sq_pos_of_pos hγ), ← abs_mul, hid]
  calc
    _ ≤ |-qd M y| + |∫ v in Ioi (0 : ℝ), Real.cos (γ * v) * qdd M (y + v)| := by
      simpa using abs_sub_le (-qd M y) 0
        (∫ v in Ioi (0 : ℝ), Real.cos (γ * v) * qdd M (y + v))
    _ ≤ -qd M y + -qd M y := by rw [abs_of_nonneg (neg_nonneg.mpr hqd)]; linarith
    _ = _ := by unfold qd; ring

end D5.S3.Analytic.Fourier.GaussianKernel
