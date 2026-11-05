/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/SpectralAverage
   generality: G
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/SpectralAverage
   mirror-E: none(waiver:analytic-integral-estimate)
   anchors: []
   utility: none
   digest: A low/high frequency Gaussian average estimate for the complete countable signed spectrum. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.GaussianWindow
import D5.S3.Weil.Mertens.IntegratedExplicit.CountableResolvent
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Low frequencies use closed-window complex cancellation. High frequencies
stay on the positive window and use the exact polynomial-exponential moment.
The spectrum is countable and complete; there is no integral-budget premise.
These are uniform analytic estimates, not certified finite instances. -/

set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory MeasureTheory.Measure Filter
open scoped BigOperators Topology

namespace D5.S3.Weil.Mertens.IntegratedExplicit.SpectralAverage

open D5.S3.Weil.Mertens.IntegratedExplicit.GaussianWindow
open D5.S3.Weil.Mertens.IntegratedExplicit.CountableResolvent

private lemma high_moment_polynomial_le {y : ℝ} (hy : 1 ≤ y) :
    exp (-y) * (2 / y + 3 / y ^ 2 + 2 / y ^ 3) ≤ 7 * exp (-y) / y := by
  have hy0 : 0 < y := by linarith
  have h2 : 1 / y ^ 2 ≤ 1 / y :=
    one_div_le_one_div_of_le hy0 (by nlinarith)
  have h3 : 1 / y ^ 3 ≤ 1 / y := by
    apply one_div_le_one_div_of_le hy0
    have hh := mul_le_mul_of_nonneg_left (show 1 ≤ y ^ 2 by nlinarith) hy0.le
    nlinarith only [hh]
  have hh := mul_le_mul_of_nonneg_left (show 2 / y + 3 / y ^ 2 + 2 / y ^ 3 ≤ 7 / y by
    simp only [div_eq_mul_inv, one_mul] at h2 h3 ⊢
    linarith only [h2, h3]) (exp_nonneg (-y))
  convert hh using 1 <;> ring

private def highPrimitive (y s : ℝ) : ℝ :=
  -((s ^ 2 + s) / y + (2 * s + 1) / y ^ 2 + 2 / y ^ 3) * exp (-y * s)

private lemma highPrimitive_derivative {y : ℝ} (hy : 0 < y) (s : ℝ) :
    HasDerivAt (highPrimitive y) (laplacePolynomial s * exp (-s * y)) s := by
  have hp := ((((hasDerivAt_id s).pow 2).add (hasDerivAt_id s)).div_const y).add
    ((((hasDerivAt_id s).const_mul 2).add_const 1).div_const (y ^ 2))
  have hd := ((hp.add_const (2 / y ^ 3)).neg).mul
    (((hasDerivAt_id s).const_mul (-y)).exp)
  change HasDerivAt (highPrimitive y) _ s at hd
  convert hd using 1
  dsimp [laplacePolynomial]
  rw [show -s * y = -y * s by ring]
  field_simp [hy.ne'] <;> ring

private lemma highPrimitive_tendsto {y : ℝ} (hy : 0 < y) :
    Tendsto (highPrimitive y) atTop (𝓝 0) := by
  have h0 : Tendsto (fun s : ℝ => exp (-y * s)) atTop (𝓝 0) := by
    simpa only [Real.rpow_zero, one_mul] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 y hy
  have h1 : Tendsto (fun s : ℝ => s * exp (-y * s)) atTop (𝓝 0) := by
    simpa only [Real.rpow_one] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 y hy
  have h2 : Tendsto (fun s : ℝ => s ^ 2 * exp (-y * s)) atTop (𝓝 0) := by
    simpa only [Real.rpow_two] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 y hy
  have h := ((((h2.add h1).div_const y).add
    (((h1.const_mul 2).add h0).div_const (y ^ 2))).add
      (h0.const_mul (2 / y ^ 3))).neg
  convert h using 1
  · funext s; dsimp [highPrimitive]; ring
  · simp

private lemma high_tail_integrable {y : ℝ} (hy : 0 < y) :
    IntegrableOn (fun s : ℝ => laplacePolynomial s * exp (-s * y)) (Ioi 1) :=
  (laplace_weight_integrable hy).mono_set (Ioi_subset_Ioi (by norm_num))

private theorem high_tail_moment {y : ℝ} (hy : 0 < y) :
    (∫ s : ℝ in Ioi 1, laplacePolynomial s * exp (-s * y)) =
      exp (-y) * (2 / y + 3 / y ^ 2 + 2 / y ^ 3) := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun s (_ : s ∈ Ici (1 : ℝ)) => highPrimitive_derivative hy s)
    (high_tail_integrable hy) (highPrimitive_tendsto hy)
  rw [h]
  norm_num [highPrimitive]
  ring

private lemma low_polynomial_integrable : IntegrableOn laplacePolynomial (Ioc 0 1) := by
  have hc : Continuous laplacePolynomial := by unfold laplacePolynomial; fun_prop
  exact (hc.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self

private lemma low_polynomial_integral : (∫ s : ℝ in Ioc 0 1, laplacePolynomial s) = 5 / 6 := by
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have he : laplacePolynomial = fun s : ℝ => s + s ^ 2 := by
    funext s; unfold laplacePolynomial; ring
  rw [he]
  calc
    _ = (∫ s : ℝ in (0 : ℝ)..1, s) + ∫ s : ℝ in (0 : ℝ)..1, s ^ 2 :=
      intervalIntegral.integral_add (continuous_id.intervalIntegrable 0 1)
        ((continuous_id.pow 2).intervalIntegrable 0 1)
    _ = _ := by norm_num [integral_pow, integral_id]

private lemma split_positive_integral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {f : ℝ → E}
    (hf : IntegrableOn f (Ioi 0)) :
    (∫ s : ℝ in Ioi 0, f s) =
      (∫ s : ℝ in Ioc 0 1, f s) + ∫ s : ℝ in Ioi 1, f s := by
  have h := intervalIntegral.integral_Ioi_sub_Ioi hf (by norm_num : (0 : ℝ) ≤ 1)
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] at h
  simpa only [add_comm] using sub_eq_iff_eq_add.mp h

def window (H : ℝ) : Set ℝ := Icc H (4 * (H + 20) ^ 2)

def windowMeasure (H : ℝ) : Measure ℝ := (gaussian (H + 20)).restrict (window H)

def cancellationError (H : ℝ) : ℝ :=
  exp (-25 * (H + 20) ^ 2) + exp (-H ^ 2) + exp (-4 * (H + 20) ^ 2)

instance windowMeasure_isFiniteMeasure (H : ℝ) : IsFiniteMeasure (windowMeasure H) := by
  dsimp [windowMeasure]
  infer_instance

private lemma windowMeasure_mass (H : ℝ) : (windowMeasure H).real univ ≤ 1 := by
  simpa only [windowMeasure, measureReal_def, Measure.restrict_apply_univ] using
    (measureReal_le_one (μ := gaussian (H + 20)) (s := window H))

private lemma cancellationError_nonneg (H : ℝ) : 0 ≤ cancellationError H := by
  unfold cancellationError; positivity

private lemma negative_denominator_frequency (z : ℂ) (s : ℝ) :
    -denominator z s = frequency (s + 1 - z.re) z.im := by
  apply Complex.ext <;> simp [denominator, frequency] <;> ring

private lemma window_kernel_integrable {z : ℂ} (hz : z.re ≤ 1) (hγ : 10 ≤ |z.im|)
    {H : ℝ} (hH : 0 < H) :
    Integrable (fun p : ℝ × ℝ => resolventKernel z p.1 p.2)
      ((volume.restrict (Ioi 0)).prod (windowMeasure H)) := by
  refine (((laplace_weight_integrable hH).div_const 10).comp_fst
    (windowMeasure H)).mono' ?_ ?_
  · exact (show Continuous (fun p : ℝ × ℝ => resolventKernel z p.1 p.2) by
      unfold resolventKernel
      apply Continuous.mul
      · exact (show Continuous (fun p : ℝ × ℝ => (laplacePolynomial p.1 : ℂ)) by
          unfold laplacePolynomial; fun_prop).div
          (show Continuous (fun p : ℝ × ℝ => denominator z p.1) by
            unfold denominator; fun_prop) (fun p => denominator_ne hγ p.1)
      · unfold denominator; fun_prop).aestronglyMeasurable
  · apply (ae_prod_iff_ae_ae (by
      unfold resolventKernel denominator laplacePolynomial
      measurability)).2
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    change ∀ᵐ y : ℝ ∂(gaussian (H + 20)).restrict (window H), _
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    calc
      _ ≤ laplacePolynomial s * exp (-s * y) / 10 :=
        resolventKernel_norm_bound hz hγ hs.le (hH.trans_le hy.1).le
      _ ≤ laplacePolynomial s * exp (-s * H) / 10 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
          (exp_le_exp.mpr (by nlinarith [mul_nonneg hs.le (sub_nonneg.mpr hy.1)]))
          (laplacePolynomial_nonneg hs.le)) (by norm_num)

private def averagedKernel (z : ℂ) (H s : ℝ) : ℂ :=
  ∫ y : ℝ, resolventKernel z s y ∂windowMeasure H

private lemma averagedKernel_integrable {z : ℂ} (hz : z.re ≤ 1) (hγ : 10 ≤ |z.im|)
    {H : ℝ} (hH : 0 < H) : IntegrableOn (averagedKernel z H) (Ioi 0) :=
  (window_kernel_integrable hz hγ hH).integral_prod_left

private lemma mode_average_exchange {z : ℂ} (hz : z.re ≤ 1) (hγ : 10 ≤ |z.im|)
    {H : ℝ} (hH : 0 < H) :
    (∫ y : ℝ, resolventMode z y ∂windowMeasure H) =
      ∫ s : ℝ in Ioi 0, averagedKernel z H s := by
  exact (integral_integral_swap (window_kernel_integrable hz hγ hH)).symm

private lemma window_kernel_bound {z : ℂ} (hz : z.re ≤ 1) (hγ : 10 ≤ |z.im|)
    {H : ℝ} (hH : 0 < H) {s y : ℝ} (hs : 0 ≤ s) (hy : y ∈ window H) :
    ‖resolventKernel z s y‖ ≤ laplacePolynomial s * exp (-s * H) / 10 := by
  calc
    _ ≤ laplacePolynomial s * exp (-s * y) / 10 :=
      resolventKernel_norm_bound hz hγ hs (hH.trans_le hy.1).le
    _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
      (exp_le_exp.mpr (by nlinarith [mul_nonneg hs (sub_nonneg.mpr hy.1)]))
      (laplacePolynomial_nonneg hs)) (by norm_num)

private lemma averagedKernel_absolute_bound {z : ℂ} (hz : z.re ≤ 1) (hγ : 10 ≤ |z.im|)
    {H : ℝ} (hH : 0 < H) {s : ℝ} (hs : 0 ≤ s) :
    (∫ y : ℝ, ‖resolventKernel z s y‖ ∂windowMeasure H) ≤
      laplacePolynomial s * exp (-s * H) / 10 := by
  have hi : Integrable (fun y : ℝ => ‖resolventKernel z s y‖) (windowMeasure H) := by
    apply (integrable_const (laplacePolynomial s * exp (-s * H) / 10)).mono'
    · exact (show Continuous (fun y : ℝ => ‖resolventKernel z s y‖) by
        unfold resolventKernel; fun_prop).aestronglyMeasurable
    · change ∀ᵐ y : ℝ ∂(gaussian (H + 20)).restrict (window H), _
      filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
      simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using
        window_kernel_bound hz hγ hH hs hy
  have hb : (∫ y : ℝ, ‖resolventKernel z s y‖ ∂windowMeasure H) ≤
      ∫ _y : ℝ, laplacePolynomial s * exp (-s * H) / 10 ∂windowMeasure H := by
    apply integral_mono_ae hi (integrable_const _)
    change ∀ᵐ y : ℝ ∂(gaussian (H + 20)).restrict (window H), _
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    exact window_kernel_bound hz hγ hH hs hy
  calc
    _ ≤ _ := hb
    _ = (laplacePolynomial s * exp (-s * H) / 10) *
        (windowMeasure H).real univ := by simp [mul_comm]
    _ ≤ _ := mul_le_of_le_one_right (by positivity [laplacePolynomial_nonneg hs])
      (windowMeasure_mass H)

private lemma averagedKernel_low_bound {z : ℂ} (hβ : 0 < z.re ∧ z.re < 1)
    (hγ : 10 ≤ |z.im|) {H : ℝ} (hH : 20000 ≤ H) {s : ℝ} (hs : s ∈ Ioc 0 1) :
    ‖averagedKernel z H s‖ ≤ laplacePolynomial s / 10 * cancellationError H := by
  have ha0 : 0 ≤ s + 1 - z.re := by linarith [hs.1, hβ.2]
  have ha2 : s + 1 - z.re ≤ 2 := by linarith [hs.2, hβ.1]
  have hcancel := truncated_gaussian_cancellation H (s + 1 - z.re) z.im hH ha0 ha2 hγ
  have he : averagedKernel z H s =
      ((laplacePolynomial s : ℂ) / denominator z s) *
        ∫ y : ℝ in window H, Complex.exp (frequency (s + 1 - z.re) z.im * y)
          ∂gaussian (H + 20) := by
    dsimp [averagedKernel, windowMeasure, resolventKernel]
    rw [integral_const_mul, negative_denominator_frequency]
  rw [he, norm_mul]
  apply mul_le_mul _ hcancel (norm_nonneg _) (by positivity [laplacePolynomial_nonneg hs.1.le])
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (laplacePolynomial_nonneg hs.1.le)]
  exact div_le_div_of_nonneg_left (laplacePolynomial_nonneg hs.1.le)
    (by norm_num) (denominator_norm hγ s)

private lemma low_mode_average_bound {z : ℂ} (hβ : 0 < z.re ∧ z.re < 1)
    (hγ : 10 ≤ |z.im|) {H : ℝ} (hH : 20000 ≤ H) :
    ‖∫ s : ℝ in Ioc 0 1, averagedKernel z H s‖ ≤ cancellationError H / 12 := by
  have hb := norm_integral_le_of_norm_le
    ((low_polynomial_integrable.div_const 10).mul_const (cancellationError H)) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      exact averagedKernel_low_bound hβ hγ hH hs)
  rw [integral_mul_const, integral_div, low_polynomial_integral] at hb
  convert hb using 1 <;> ring

private lemma high_mode_average_bound {z : ℂ} (hz : z.re ≤ 1) (hγ : 10 ≤ |z.im|)
    {H : ℝ} (hH : 1 ≤ H) :
    ‖∫ s : ℝ in Ioi 1, averagedKernel z H s‖ ≤ (7 / 10 : ℝ) * (exp (-H) / H) := by
  have hH0 : 0 < H := by linarith
  have hb := norm_integral_le_of_norm_le ((high_tail_integrable hH0).div_const 10) (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (norm_integral_le_integral_norm _).trans
      (averagedKernel_absolute_bound hz hγ hH0 (le_trans (by norm_num : (0 : ℝ) ≤ 1) hs.le)))
  rw [integral_div, high_tail_moment hH0] at hb
  calc
    _ ≤ _ := hb
    _ ≤ (7 * exp (-H) / H) / 10 := div_le_div_of_nonneg_right
      (high_moment_polynomial_le hH) (by norm_num)
    _ = _ := by ring

private lemma complete_mode_average_bound {z : ℂ} (hβ : 0 < z.re ∧ z.re < 1)
    (hγ : 10 ≤ |z.im|) {H : ℝ} (hH : 20000 ≤ H) :
    ‖∫ y : ℝ, resolventMode z y ∂windowMeasure H‖ ≤
      cancellationError H / 12 + (7 / 10 : ℝ) * (exp (-H) / H) := by
  rw [mode_average_exchange hβ.2.le hγ (by linarith),
    split_positive_integral (averagedKernel_integrable hβ.2.le hγ (by linarith))]
  exact (norm_add_le _ _).trans (add_le_add
    (low_mode_average_bound hβ hγ hH)
    (high_mode_average_bound hβ.2.le hγ (by linarith)))

/-- Complete spectral average from cancellation, high-frequency decay and
countable dominated convergence, without any assumed mean bound. -/
theorem spectral_average_bound (S : CountableSpectrum) {H : ℝ} (hH : 20000 ≤ H) :
    ‖∫ y : ℝ, spectralTail S y ∂windowMeasure H‖ ≤
      cancellationError H / 6 + (7 / 5 : ℝ) * (exp (-H) / H) := by
  have hH0 : 0 < H := by linarith
  let K : ℝ := W H / 10
  let B : ℝ := cancellationError H / 12 + (7 / 10 : ℝ) * (exp (-H) / H)
  let f : ℕ → ℝ → ℂ := fun k y => S.coeff k * resolventMode (S.zero k) y
  have hpoint (k : ℕ) (y : ℝ) (hy : y ∈ window H) :
      ‖f k y‖ ≤ ‖S.coeff k‖ * K := by
    dsimp [f, K]
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact (resolventMode_bound (S.strip k).2.le (S.height k).le (hH0.trans_le hy.1)).trans
      (div_le_div_of_nonneg_right (W_antitone hH0 hy.1) (by norm_num))
  have hlim : ∀ᵐ y : ℝ ∂windowMeasure H, HasSum (fun k => f k y) (spectralTail S y) := by
    change ∀ᵐ y : ℝ ∂(gaussian (H + 20)).restrict (window H), _
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    have hs : Summable (fun k => f k y) := Summable.of_norm_bounded
      (S.summable_norm.mul_right K) (fun k => hpoint k y hy)
    rw [countable_resolvent_identity S (hH0.trans_le hy.1)]
    exact hs.hasSum
  have hm : ∀ k, AEStronglyMeasurable (f k) (windowMeasure H) := by
    intro k
    exact (((resolventMode_continuousOn (S.strip k).2 hH0).const_mul _).mono
      (fun y hy => hy.1)).aestronglyMeasurable measurableSet_Icc
  have hb : ∀ k, ∀ᵐ y : ℝ ∂windowMeasure H, ‖f k y‖ ≤ ‖S.coeff k‖ * K := by
    intro k
    change ∀ᵐ y : ℝ ∂(gaussian (H + 20)).restrict (window H), _
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    exact hpoint k y hy
  have hsum := hasSum_integral_of_dominated_convergence
    (fun k (_y : ℝ) => ‖S.coeff k‖ * K) hm hb
    (ae_of_all _ (fun _ => S.summable_norm.mul_right K))
    (by simpa only [tsum_mul_right] using
      (integrable_const ((∑' k : ℕ, ‖S.coeff k‖) * K) :
        Integrable (fun _ : ℝ => (∑' k : ℕ, ‖S.coeff k‖) * K) (windowMeasure H))) hlim
  have hn : ‖∫ y : ℝ, spectralTail S y ∂windowMeasure H‖ ≤
      (∑' k : ℕ, ‖S.coeff k‖) * B := by
    apply hsum.norm_le_of_bounded (S.summable_norm.hasSum.mul_right B)
    intro k
    dsimp [f]
    rw [integral_const_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left
      (complete_mode_average_bound (S.strip k) (S.height k).le hH) (norm_nonneg _)
  calc
    _ ≤ _ := hn
    _ ≤ 2 * B := mul_le_mul_of_nonneg_right S.mass_le (by
      dsimp [B]; positivity [cancellationError_nonneg H])
    _ = _ := by dsimp [B]; ring

end D5.S3.Weil.Mertens.IntegratedExplicit.SpectralAverage
