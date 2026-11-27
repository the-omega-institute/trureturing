/- GID: D5/S3/Fourier/InverseFourierSupport
   generality: I
   mirror-B: D5/B/S3/Fourier/InverseFourierSupport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sinc regularization gives support of the inverse Fourier transform. -/

import D5.S3.Fourier.InfiniteSincProduct
import D5.S3.Weil.ZetaGamma.FormCore.LineFourier
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-! Inverse Fourier support by sinc regularization and contour integration. -/

namespace D5.S3.Fourier.InverseFourierSupport

open Complex Filter MeasureTheory Set Topology
open scoped ENNReal FourierTransform RealInnerProductSpace
open D5.S3.Fourier.InfiniteSincProduct
open D5.S3.Weil.ZetaGamma.FormCore.LineFourier

noncomputable section

private theorem differentiable_complexSinc : Differentiable ℂ complexSinc := by
  have haway : DifferentiableOn ℂ complexSinc ((univ : Set ℂ) \ {0}) := by
    intro z hz
    have hz' : z ≠ 0 := by simpa using hz
    apply ((Complex.differentiable_sin z).div differentiableAt_id hz').differentiableWithinAt.congr
    · intro w hw
      exact complexSinc_of_ne_zero (by simpa using hw)
    · exact complexSinc_of_ne_zero hz'
  apply differentiableOn_univ.mp
  exact
    (Complex.differentiableOn_compl_singleton_and_continuousAt_iff
      (s := univ) (c := 0) (f := complexSinc) univ_mem).mp
        ⟨haway, continuous_complexSinc.continuousAt⟩

private theorem norm_sinc_strip {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
    ‖complexSinc ((ε : ℂ) * z)‖ ≤ Real.exp (ε * |z.im|) := by
  rw [← uniformIntervalFourierLaplace_eq_complexSinc hε, uniformIntervalFourierLaplace]
  calc
    ‖∫ x : ℝ, (uniformIntervalDensity ε x : ℂ) * exp (I * z * x)‖ ≤
        ∫ x : ℝ, Real.exp (ε * |z.im|) * uniformIntervalDensity ε x := by
      apply norm_integral_le_of_norm_le ((uniformIntervalDensity_integrable ε).const_mul _)
      filter_upwards [] with x
      by_cases hx : x ∈ Icc (-ε) ε
      · have he : (I * z * (x : ℂ)).re ≤ ε * |z.im| := by
          simp only [mul_re, I_re, I_im, ofReal_re, ofReal_im,
            zero_mul, mul_zero, one_mul, sub_zero, zero_sub]
          calc
            -z.im * x ≤ |z.im| * |x| := by simpa [abs_mul] using le_abs_self (-z.im * x)
            _ ≤ ε * |z.im| := by nlinarith [abs_le.mpr hx, abs_nonneg z.im]
        rw [norm_mul, Complex.norm_real,
          Real.norm_of_nonneg (uniformIntervalDensity_nonneg hε x), Complex.norm_exp]
        simpa [mul_comm] using mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he)
          (uniformIntervalDensity_nonneg hε x)
      · simp [uniformIntervalDensity, hx]
    _ = _ := by rw [integral_const_mul, integral_uniformIntervalDensity hε, mul_one]

private theorem norm_sinc_mul_one_add_norm {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
    ‖complexSinc ((ε : ℂ) * z)‖ * (1 + ‖z‖) ≤
      (1 + ε⁻¹) * Real.exp (ε * |z.im|) := by
  have hsin (w : ℂ) : ‖sin w‖ ≤ Real.exp |w.im| := by
    have hp : ‖exp (w * I)‖ ≤ Real.exp |w.im| := by
      rw [Complex.norm_exp]
      apply Real.exp_le_exp.mpr
      simpa using neg_le_abs w.im
    have hn : ‖exp (-(w * I))‖ ≤ Real.exp |w.im| := by
      rw [Complex.norm_exp]
      apply Real.exp_le_exp.mpr
      simpa using le_abs_self w.im
    rw [Complex.sin, norm_div, norm_mul, Complex.norm_I, mul_one,
      show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num, neg_mul]
    exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
      ((norm_sub_le _ _).trans (by linarith))
  have hinv : ‖complexSinc ((ε : ℂ) * z)‖ * ‖z‖ ≤ Real.exp (ε * |z.im|) * ε⁻¹ := by
    by_cases hz : z = 0
    · simp [hz, hε.le]
    · have hw : (ε : ℂ) * z ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr hε.ne') hz
      rw [complexSinc_of_ne_zero hw, norm_div, norm_mul, Complex.norm_of_nonneg hε.le]
      have hs := hsin ((ε : ℂ) * z)
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
        add_zero, abs_mul, abs_of_pos hε] at hs
      calc
        ‖sin ((ε : ℂ) * z)‖ / (ε * ‖z‖) * ‖z‖ = ‖sin ((ε : ℂ) * z)‖ * ε⁻¹ := by
          field_simp [hε.ne', norm_ne_zero_iff.mpr hz]
        _ ≤ _ := mul_le_mul_of_nonneg_right hs (inv_nonneg.mpr hε.le)
  nlinarith [norm_sinc_strip hε z]

/-- The sinc power compensates the entire function's polynomial growth. -/
private def sincRegularization (F : ℂ → ℂ) (m : ℕ) (ε : ℝ) (z : ℂ) : ℂ :=
  F z * complexSinc ((ε : ℂ) * z) ^ (m + 2)

private theorem differentiable_regularization {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (m : ℕ) (ε : ℝ) : Differentiable ℂ (sincRegularization F m ε) :=
  hF.mul ((differentiable_complexSinc.comp (differentiable_id.const_mul _)).pow _)

private theorem regularization_bound {F : ℂ → ℂ} {a C ε : ℝ} {m : ℕ}
    (hF : ∀ z : ℂ, ‖F z‖ ≤ C * (1 + ‖z‖) ^ m * Real.exp (a * |z.im|))
    (hε : 0 < ε) (z : ℂ) :
    ‖sincRegularization F m ε z‖ ≤
      (C * (1 + ε⁻¹) ^ (m + 2)) / (1 + ‖z‖) ^ 2 *
        Real.exp ((a + ↑(m + 2) * ε) * |z.im|) := by
  have hbase : 0 < 1 + ‖z‖ := by positivity
  have hs := pow_le_pow_left₀ (by positivity) (norm_sinc_mul_one_add_norm hε z) (m + 2)
  rw [mul_pow, mul_pow, ← Real.exp_nat_mul] at hs
  apply (mul_le_mul_iff_of_pos_right (pow_pos hbase 2)).mp
  calc
    ‖sincRegularization F m ε z‖ * (1 + ‖z‖) ^ 2 =
        ‖F z‖ * ‖complexSinc ((ε : ℂ) * z)‖ ^ (m + 2) * (1 + ‖z‖) ^ 2 := by
      rw [sincRegularization, norm_mul, norm_pow]
    _ ≤ (C * (1 + ‖z‖) ^ m * Real.exp (a * |z.im|)) *
        ‖complexSinc ((ε : ℂ) * z)‖ ^ (m + 2) * (1 + ‖z‖) ^ 2 := by gcongr; exact hF z
    _ = (C * Real.exp (a * |z.im|)) *
        (‖complexSinc ((ε : ℂ) * z)‖ ^ (m + 2) * (1 + ‖z‖) ^ (m + 2)) := by
      rw [pow_add (1 + ‖z‖) m 2]
      ring
    _ ≤ (C * Real.exp (a * |z.im|)) *
        ((1 + ε⁻¹) ^ (m + 2) * Real.exp (↑(m + 2) * (ε * |z.im|))) := by
      have hC : 0 ≤ C := by simpa using (norm_nonneg (F 0)).trans (hF 0)
      exact mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by
      rw [show (a + ↑(m + 2) * ε) * |z.im| = a * |z.im| + ↑(m + 2) * (ε * |z.im|) by ring,
        Real.exp_add]
      field_simp

private theorem integrable_decay : Integrable (fun x : ℝ => ((1 + ‖x‖) ^ 2)⁻¹) := by
  refine (integrable_one_add_norm (E := ℝ) (r := 2) (by norm_num [Module.finrank_self])).congr ?_
  filter_upwards [] with x
  rw [Real.rpow_neg (by positivity), show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

private theorem angular_integral_zero_of_pos {F : ℂ → ℂ} {b K t : ℝ}
    (hF : Differentiable ℂ F) (hK : 0 ≤ K) (ht : b < t)
    (hbound : ∀ z : ℂ, ‖F z‖ ≤ K / (1 + ‖z‖) ^ 2 * Real.exp (b * |z.im|)) :
    (∫ x : ℝ, exp (I * (t : ℂ) * (x : ℂ)) * F (x : ℂ)) = 0 := by
  let H : ℂ → ℂ := fun z => exp (I * (t : ℂ) * z) * F z
  have hH : Differentiable ℂ H :=
    ((differentiable_id.const_mul (I * (t : ℂ))).cexp).mul hF
  have hmajor (x y : ℝ) (hy : 0 ≤ y) :
      ‖H ((x : ℂ) + (y : ℂ) * I)‖ ≤
        (K * ((1 + ‖x‖) ^ 2)⁻¹) * Real.exp ((b - t) * y) := by
    let z : ℂ := (x : ℂ) + (y : ℂ) * I
    have hzx : z.re = x := by simp [z]
    have hzy : z.im = y := by simp [z]
    have hnorm : ‖x‖ ≤ ‖z‖ := by simpa only [Real.norm_eq_abs, hzx] using Complex.abs_re_le_norm z
    have he : (I * (t : ℂ) * z).re = -t * y := by
      simp [Complex.mul_re, Complex.mul_im, hzy, neg_mul]
    change ‖H z‖ ≤ _
    dsimp [H]
    rw [norm_mul, Complex.norm_exp, he]
    calc
      _ ≤ Real.exp (-t * y) * (K / (1 + ‖z‖) ^ 2 * Real.exp (b * |z.im|)) :=
        mul_le_mul_of_nonneg_left (hbound z) (Real.exp_pos _).le
      _ = K / (1 + ‖z‖) ^ 2 * Real.exp ((b - t) * y) := by
        rw [hzy, abs_of_nonneg hy, show (b - t) * y = -t * y + b * y by ring, Real.exp_add]
        ring
      _ ≤ _ := by
        rw [← div_eq_mul_inv]
        gcongr
        simpa only [Real.norm_eq_abs] using hnorm
  let line : ℝ → ℂ := fun y => ∫ x : ℝ, H ((x : ℂ) + (y : ℂ) * I)
  have hmeas (y : ℝ) : AEStronglyMeasurable (fun x : ℝ => H ((x : ℂ) + (y : ℂ) * I))
      volume :=
    (hH.continuous.comp
      (by fun_prop : Continuous fun x : ℝ => (x : ℂ) + (y : ℂ) * I)).aestronglyMeasurable
  have hline (y : ℝ) (hy : 0 ≤ y) :
      Integrable (fun x : ℝ => H ((x : ℂ) + (y : ℂ) * I)) :=
    ((integrable_decay.const_mul K).mul_const (Real.exp ((b - t) * y))).mono' (hmeas y)
      (Eventually.of_forall fun x => hmajor x y hy)
  have hshift (T : ℝ) (hT : 0 ≤ T) : line 0 = line T := by
    let side : ℝ → ℂ := fun x => ∫ y : ℝ in 0..T, H ((x : ℂ) + (y : ℂ) * I)
    have hside (x : ℝ) : ‖side x‖ ≤ (K * ((1 + ‖x‖) ^ 2)⁻¹) * T := by
      suffices ‖side x‖ ≤ (K * ((1 + ‖x‖) ^ 2)⁻¹) * |T - 0| by
        simpa only [sub_zero, abs_of_nonneg hT] using this
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro y hy
      rw [uIoc_of_le hT] at hy
      exact (hmajor x y hy.1.le).trans
        (mul_le_of_le_one_right (by positivity)
          (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht.le) hy.1.le)))
    have hdecay : Tendsto (fun R : ℝ => ((1 + ‖R‖) ^ 2)⁻¹) atTop (𝓝 0) := by
      have hi := (tendsto_inv_atTop_zero (𝕜 := ℝ)).comp
        (tendsto_atTop_add_const_left atTop 1 (tendsto_id : Tendsto (id : ℝ → ℝ) atTop atTop))
      have hpow : Tendsto (fun R : ℝ => ((1 + R) ^ 2)⁻¹) atTop (𝓝 0) := by
        simpa only [Function.comp_def, id, inv_pow, zero_pow (by decide : 2 ≠ 0)] using hi.pow 2
      refine hpow.congr' ?_
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
      rw [Real.norm_of_nonneg hR]
    have hlim (f : ℝ → ℂ) (hf : ∀ R, ‖f R‖ ≤ (K * ((1 + ‖R‖) ^ 2)⁻¹) * T) :
        Tendsto f atTop (𝓝 0) := by
      apply squeeze_zero_norm hf
      simpa using (hdecay.const_mul K).mul_const T
    have hright := hlim side hside
    have hleft := hlim (fun R => side (-R))
      (fun R => by simpa only [norm_neg] using hside (-R))
    have hbottom := intervalIntegral_tendsto_integral (hline 0 le_rfl)
      tendsto_neg_atTop_atBot tendsto_id
    have htop := intervalIntegral_tendsto_integral (hline T hT)
      tendsto_neg_atTop_atBot tendsto_id
    have hlimrect := ((hbottom.sub htop).add (hright.const_smul I)).sub (hleft.const_smul I)
    have hzero : (fun R : ℝ =>
        (∫ x : ℝ in -R..R, H ((x : ℂ) + (0 : ℝ) * I)) -
        (∫ x : ℝ in -R..R, H ((x : ℂ) + (T : ℝ) * I)) + I • side R - I • side (-R)) =
        fun _ => 0 := by
      funext R
      simpa [side] using
        integral_boundary_rect_eq_zero_of_differentiableOn H (-(R : ℂ))
          ((R : ℂ) + (T : ℂ) * I) hH.differentiableOn
    have hz : Tendsto (fun _ : ℝ => (0 : ℂ)) atTop (𝓝 (line 0 - line T)) := by
      simpa only [id, hzero, smul_zero, add_zero, sub_zero] using hlimrect
    exact sub_eq_zero.mp (tendsto_nhds_unique hz tendsto_const_nhds)
  have hheight : Tendsto (fun T : ℝ => Real.exp ((b - t) * T)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp ((tendsto_const_mul_atBot_of_neg (sub_neg.mpr ht)).mpr tendsto_id)
  have hline_zero : Tendsto line atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun T => (∫ x : ℝ, K * ((1 + ‖x‖) ^ 2)⁻¹) *
      Real.exp ((b - t) * T)) _ (by simpa using hheight.const_mul _)
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    rw [← integral_mul_const]
    exact norm_integral_le_of_norm_le
      ((integrable_decay.const_mul K).mul_const _) (Eventually.of_forall fun x => hmajor x T hT)
  have hsame : line =ᶠ[atTop] fun _ => line 0 := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT using (hshift T hT).symm
  have hz := tendsto_nhds_unique (hline_zero.congr' hsame) tendsto_const_nhds
  simpa [line, H] using hz.symm

private theorem angular_integral_zero {F : ℂ → ℂ} {b K t : ℝ}
    (hF : Differentiable ℂ F) (hK : 0 ≤ K) (ht : b < |t|)
    (hbound : ∀ z : ℂ, ‖F z‖ ≤ K / (1 + ‖z‖) ^ 2 * Real.exp (b * |z.im|)) :
    (∫ x : ℝ, exp (I * (t : ℂ) * (x : ℂ)) * F (x : ℂ)) = 0 := by
  by_cases ht0 : 0 ≤ t
  · exact angular_integral_zero_of_pos hF hK (by rwa [abs_of_nonneg ht0] at ht) hbound
  · have he := angular_integral_zero_of_pos (F := fun z => F (-z))
      (hF.comp differentiable_neg) hK (show b < -t by rwa [abs_of_neg (lt_of_not_ge ht0)] at ht)
      (fun z => by simpa using hbound (-z))
    rw [← integral_neg_eq_self (fun x : ℝ => exp (I * (t : ℂ) * (x : ℂ)) * F (x : ℂ)) volume]
    simpa only [ofReal_neg, mul_neg, neg_mul] using he

private theorem fourierInv_dilate_eq {F : ℂ → ℂ} (t : ℝ) :
    𝓕⁻ (fun ξ : ℝ => F (((2 * Real.pi) * ξ : ℝ) : ℂ)) t =
      ((2 * Real.pi)⁻¹ : ℝ) • ∫ x : ℝ, exp (I * (t : ℂ) * (x : ℂ)) * F (x : ℂ) := by
  rw [Real.fourierInv_eq', ← abs_of_pos (by positivity : 0 < (2 * Real.pi)⁻¹),
    ← Measure.integral_comp_mul_left]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [real_inner_comm, Real.inner_apply, smul_eq_mul, ofReal_mul]
  ring_nf

/-- The inverse of the damped entire function is supported on the interval of
half-width `a + (m + 2) * ε`. The frequency variable is rescaled by `2 * π`
for Mathlib's Fourier convention. -/
private theorem fourierInv_sincRegularization_eq_zero {F : ℂ → ℂ} {a C ε t : ℝ} {m : ℕ}
    (hF : Differentiable ℂ F)
    (hbound : ∀ z : ℂ, ‖F z‖ ≤ C * (1 + ‖z‖) ^ m * Real.exp (a * |z.im|))
    (hε : 0 < ε) (ht : a + ↑(m + 2) * ε < |t|) :
    𝓕⁻ (fun ξ : ℝ => sincRegularization F m ε (((2 * Real.pi) * ξ : ℝ) : ℂ)) t = 0 := by
  have hC : 0 ≤ C := by simpa using (norm_nonneg (F 0)).trans (hbound 0)
  rw [fourierInv_dilate_eq, angular_integral_zero (differentiable_regularization hF m ε)
    (by positivity) ht (regularization_bound hbound hε), smul_zero]

private theorem norm_regularization_real_le (F : ℂ → ℂ) (m : ℕ)
    {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    ‖sincRegularization F m ε (x : ℂ)‖ ≤ ‖F (x : ℂ)‖ := by
  have hs : ‖complexSinc ((ε : ℂ) * (x : ℂ))‖ ≤ 1 := by
    simpa using norm_sinc_strip hε (x : ℂ)
  rw [sincRegularization, norm_mul, norm_pow]
  exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hs)

/-- The angular-frequency restriction is written in the cycles convention of
the Fourier transform on `L²`. -/
def frequencyRestriction (F : ℂ → ℂ) (ξ : ℝ) : ℂ :=
  F (((2 * Real.pi) * ξ : ℝ) : ℂ)

private theorem continuous_frequencyRestriction {F : ℂ → ℂ} (hF : Differentiable ℂ F) :
    Continuous (frequencyRestriction F) :=
  hF.continuous.comp (by fun_prop : Continuous fun ξ : ℝ => (((2 * Real.pi) * ξ : ℝ) : ℂ))

private theorem memLp_frequencyRestriction {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (h₂ : MemLp (fun x : ℝ => F (x : ℂ)) 2 volume) :
    MemLp (frequencyRestriction F) 2 volume := by
  rw [memLp_two_iff_integrable_sq_norm (continuous_frequencyRestriction hF).aestronglyMeasurable]
  exact ((memLp_two_iff_integrable_sq_norm h₂.aestronglyMeasurable).mp h₂).comp_mul_left'
    (show 2 * Real.pi ≠ 0 by positivity)

private theorem integrable_regularized_restriction {F : ℂ → ℂ} {a C ε : ℝ} {m : ℕ}
    (hF : Differentiable ℂ F)
    (hbound : ∀ z : ℂ, ‖F z‖ ≤ C * (1 + ‖z‖) ^ m * Real.exp (a * |z.im|))
    (hε : 0 < ε) :
    Integrable (frequencyRestriction (sincRegularization F m ε)) := by
  let K : ℝ := C * (1 + ε⁻¹) ^ (m + 2)
  have hint : Integrable (fun x : ℝ => sincRegularization F m ε (x : ℂ)) := by
    apply (integrable_decay.const_mul K).mono'
      ((differentiable_regularization hF m ε).continuous.comp
        continuous_ofReal).aestronglyMeasurable
    filter_upwards [] with x
    simpa [K, div_eq_mul_inv] using regularization_bound hbound hε (x : ℂ)
  exact hint.comp_mul_left' (show 2 * Real.pi ≠ 0 by positivity)

private theorem fourierInv_ae_eq_L2_of_hasCompactSupport {g : ℝ → ℂ}
    (hg : Continuous g) (hg₁ : Integrable g) (hg₂ : MemLp g 2 volume)
    (hsupp : HasCompactSupport (𝓕⁻ g)) :
    (𝓕⁻ g : ℝ → ℂ) =ᵐ[volume] (Lp.fourierTransformₗᵢ ℝ ℂ).symm (hg₂.toLp g) := by
  let q : ℝ → ℂ := 𝓕⁻ g
  have hq : Continuous q := by
    have heq : q = fun t => 𝓕 g (-t) := funext (Real.fourierInv_eq_fourier_neg g)
    rw [heq]
    exact (continuous_raw_fourier hg₁).comp continuous_neg
  have hq₁ : Integrable q := hq.integrable_of_hasCompactSupport hsupp
  have hq₂ : MemLp q 2 volume := hq.memLp_of_hasCompactSupport hsupp
  have hfg : Integrable (𝓕 g) := by
    simpa only [q, Real.fourierInv_eq_fourier_neg, neg_neg] using hq₁.comp_neg
  have heq : 𝓕 (hq₂.toLp q) = hg₂.toLp g := by
    apply Lp.ext
    exact (raw_fourier_ae_eq_L2 hq₁ hq₂).symm.trans
      ((EventuallyEq.of_eq (hg.fourier_fourierInv_eq hg₁ hfg)).trans hg₂.coeFn_toLp.symm)
  have hinv : hq₂.toLp q = (Lp.fourierTransformₗᵢ ℝ ℂ).symm (hg₂.toLp g) := by
    rw [← heq]
    exact ((Lp.fourierTransformₗᵢ ℝ ℂ).symm_apply_apply _).symm
  rw [← hinv]
  exact hq₂.coeFn_toLp.symm

private theorem tendsto_toLp_of_enorm_le {g : ℝ → ℂ} {gε : ℕ → ℝ → ℂ}
    (hg : MemLp g 2 volume) (hgε : ∀ n, MemLp (gε n) 2 volume)
    (hbound : ∀ n x, ‖gε n x‖ ≤ ‖g x‖)
    (hlim : ∀ x, Tendsto (fun n => gε n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => (hgε n).toLp (gε n)) atTop (𝓝 (hg.toLp g)) := by
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ hgε _ hg).mpr
  have hDCT : Tendsto (fun n => ∫⁻ x, ‖gε n x - g x‖ₑ ^ (2 : ℕ)) atTop (𝓝 0) := by
    have hfinite : (∫⁻ x, (2 * ‖g x‖ₑ) ^ (2 : ℕ)) ≠ ∞ := by
      simp_rw [mul_pow]
      rw [lintegral_const_mul'' _ (hg.aestronglyMeasurable.enorm.pow_const 2),
        squared_mass_eq_eLpNorm g hg.aestronglyMeasurable]
      exact ENNReal.mul_ne_top (by norm_num) (ENNReal.pow_ne_top hg.eLpNorm_lt_top.ne)
    have hdom (n : ℕ) : ∀ᵐ x : ℝ, ‖gε n x - g x‖ₑ ^ (2 : ℕ) ≤ (2 * ‖g x‖ₑ) ^ (2 : ℕ) := by
      filter_upwards [] with x
      apply pow_le_pow_left' _ 2
      calc
        ‖gε n x - g x‖ₑ ≤ ‖gε n x‖ₑ + ‖g x‖ₑ := enorm_sub_le
        _ ≤ ‖g x‖ₑ + ‖g x‖ₑ := add_le_add_left (enorm_le_iff_norm_le.mpr (hbound n x)) _
        _ = _ := (two_mul _).symm
    simpa using
      (tendsto_lintegral_of_dominated_convergence' (fun x => (2 * ‖g x‖ₑ) ^ (2 : ℕ))
        (f := fun _ => 0)
        (fun n => ((hgε n).sub hg).aestronglyMeasurable.enorm.pow_const _)
        hdom hfinite (Eventually.of_forall fun x => by
          simpa [ENNReal.rpow_ofNat] using ((hlim x).sub_const (g x)).enorm.ennrpow_const 2))
  have he (n : ℕ) : eLpNorm (gε n - g) 2 volume =
      (∫⁻ x, ‖gε n x - g x‖ₑ ^ (2 : ℕ)) ^ (1 / 2 : ℝ) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
      ((hgε n).sub hg).aestronglyMeasurable]
    norm_num [ENNReal.rpow_ofNat]
  simp_rw [he]
  simpa using hDCT.ennrpow_const (1 / 2 : ℝ)

/-- If an entire function has polynomially weighted directional growth of
half-width `a` and an `L²` real restriction, its inverse Fourier class vanishes
almost everywhere off `[-a, a]`. -/
theorem inverse_fourier_L2_support {F : ℂ → ℂ} {a C : ℝ} {m : ℕ}
    (hF : Differentiable ℂ F)
    (h₂ : MemLp (fun x : ℝ => F (x : ℂ)) 2 volume)
    (hbound : ∀ z : ℂ, ‖F z‖ ≤ C * (1 + ‖z‖) ^ m * Real.exp (a * |z.im|)) :
    let g := frequencyRestriction F
    ∃ hg : MemLp g 2 volume,
      ∀ᵐ t : ℝ, a < |t| → ((Lp.fourierTransformₗᵢ ℝ ℂ).symm (hg.toLp g)) t = 0 := by
  let g := frequencyRestriction F
  let ε : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹
  let gε : ℕ → ℝ → ℂ := fun n => frequencyRestriction (sincRegularization F m (ε n))
  have hεpos (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hεlim : Tendsto ε atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hg : MemLp g 2 volume := memLp_frequencyRestriction hF h₂
  have hcont (n : ℕ) : Continuous (gε n) :=
    continuous_frequencyRestriction (differentiable_regularization hF m (ε n))
  have hcontraction (n : ℕ) (ξ : ℝ) : ‖gε n ξ‖ ≤ ‖g ξ‖ :=
    norm_regularization_real_le F m (hεpos n) _
  have hgε (n : ℕ) : MemLp (gε n) 2 volume :=
    hg.mono (hcont n).aestronglyMeasurable (Eventually.of_forall (hcontraction n))
  have hgεlim (ξ : ℝ) : Tendsto (fun n => gε n ξ) atTop (𝓝 (g ξ)) := by
    have hz : Tendsto (fun n => (ε n : ℂ) * (((2 * Real.pi) * ξ : ℝ) : ℂ)) atTop (𝓝 0) := by
      simpa only [Function.comp_apply, ofReal_zero, zero_mul] using
        (continuous_ofReal.continuousAt.tendsto.comp hεlim).mul_const
          (((2 * Real.pi) * ξ : ℝ) : ℂ)
    have hs := (continuous_complexSinc.continuousAt.tendsto.comp hz).pow (m + 2)
    simpa [gε, g, frequencyRestriction, sincRegularization, Function.comp_def] using
      hs.const_mul (g ξ)
  let inverse := (Lp.fourierTransformₗᵢ ℝ ℂ).symm
  let uε : ℕ → Lp ℂ 2 (volume : Measure ℝ) := fun n => inverse ((hgε n).toLp (gε n))
  let u : Lp ℂ 2 (volume : Measure ℝ) := inverse (hg.toLp g)
  have hlim : Tendsto uε atTop (𝓝 u) :=
    inverse.continuous.continuousAt.tendsto.comp
      (tendsto_toLp_of_enorm_le hg hgε hcontraction hgεlim)
  have hzero (n : ℕ) (t : ℝ) (ht : a + ↑(m + 2) * ε n < |t|) : 𝓕⁻ (gε n) t = 0 :=
    fourierInv_sincRegularization_eq_zero hF hbound (hεpos n) ht
  have hsupp (n : ℕ) : HasCompactSupport (𝓕⁻ (gε n)) := by
    refine HasCompactSupport.of_support_subset_isCompact
      (isCompact_Icc (a := -(a + ↑(m + 2) * ε n)) (b := a + ↑(m + 2) * ε n)) ?_
    intro t ht
    apply abs_le.mp
    exact le_of_not_gt (fun h => ht (hzero n t h))
  have hsame (n : ℕ) : (𝓕⁻ (gε n) : ℝ → ℂ) =ᵐ[volume] uε n :=
    fourierInv_ae_eq_L2_of_hasCompactSupport (hcont n)
      (integrable_regularized_restriction hF hbound (hεpos n)) (hgε n) (hsupp n)
  have hwidth : Tendsto (fun n => a + ↑(m + 2) * ε n) atTop (𝓝 a) := by
    simpa using (hεlim.const_mul (↑(m + 2) : ℝ)).const_add a
  obtain ⟨ns, hns, hpoint⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
  refine ⟨hg, ?_⟩
  filter_upwards [ae_all_iff.mpr hsame, hpoint] with t hsame_t hpoint_t
  intro ht
  have htail : ∀ᶠ n in atTop, uε (ns n) t = 0 := by
    filter_upwards [(hwidth.comp hns.tendsto_atTop).eventually_lt_const ht] with n hn
    rw [← hsame_t (ns n)]
    exact hzero (ns n) t hn
  exact tendsto_nhds_unique hpoint_t (tendsto_congr' htail |>.mpr tendsto_const_nhds)

#print axioms fourierInv_sincRegularization_eq_zero
#print axioms inverse_fourier_L2_support

end
end D5.S3.Fourier.InverseFourierSupport
