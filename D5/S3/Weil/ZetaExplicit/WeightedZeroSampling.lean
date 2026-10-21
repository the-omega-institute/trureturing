/- GID: D5/S3/Weil/ZetaExplicit/WeightedZeroSampling
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaExplicit/WeightedZeroSampling
   mirror-E: none(waiver:original-L2-sampling-domain-open)
   anchors: []
   utility: none
   digest: Support-aware convolution reproduction and two-family weighted zero sampling over the original ZeroConfig. -/

import D5.S3.Weil.ZeroInfinitude.WindowZero
import D5.S3.Weil.ZetaCore.ExplicitFormula
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L2Space

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex MeasureTheory Set Filter
open scoped BigOperators ComplexConjugate FourierTransform

namespace Zeta23.WeilEF.WeightedZeroSampling

open D5.S3.Weil.TestFunctions
open D5.S3.Weil.FourierLaplace
open D5.S3.Weil.TestFunctions.FourierLaplaceClosedStripDecay

private theorem integrable_of_memLp_Ioc {a : ℝ} {f : ℝ → ℂ}
    (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂(volume : Measure ℝ), x ∉ Ioc (-a) a → f x = 0) :
    Integrable f := by
  have heq : (Ioc (-a) a).indicator f =ᵐ[volume] f := by
    filter_upwards [hs] with x hx
    by_cases h : x ∈ Ioc (-a) a
    · simp [h]
    · simp [h, hx h]
  have hi : MemLp ((Ioc (-a) a).indicator f) 2 volume := (memLp_congr_ae heq).mpr hf
  have h1 : MemLp ((Ioc (-a) a).indicator f) 1 volume :=
    hi.mono_exponent_of_measure_support_ne_top
      (fun x hx => Set.indicator_of_notMem hx f) (by simp) (by norm_num)
  exact (memLp_one_iff_integrable.mp h1).congr heq

/-- The angular inverse kernel at an actual complex shift. -/
def stripKernel (b : WeilTestFunction) (β u : ℝ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) * Zeta23.paperFT b ((u : ℂ) + Complex.I * (β : ℂ))

private theorem continuous_stripKernel (b : WeilTestFunction) (β : ℝ) :
    Continuous (stripKernel b β) := by
  have hFT : Continuous (fun z : ℂ => Zeta23.paperFT b z) := by
    convert (fourierLaplace_entire b).continuous using 1
    funext z
    exact D5.S3.Weil.ZetaBridge.ClassicExplicitFormula.paperFT_eq_fourierLaplace b z
  exact continuous_const.mul (hFT.comp (by fun_prop))

private theorem stripKernel_bound_of_decay (b : WeilTestFunction) {D : ℝ}
    (hdecay : ∀ w : ℂ, |w.im| ≤ 1 / 2 →
      ‖fourierLaplace b w‖ ≤ D / (1 + w.re ^ 2))
    {β : ℝ} (hβ : |β| ≤ 1 / 2) (u : ℝ) :
    ‖stripKernel b β u‖ ≤ (D / (2 * Real.pi)) / (1 + u ^ 2) := by
  have h := hdecay
    ((u : ℂ) + Complex.I * (β : ℂ)) (by simpa using hβ)
  rw [stripKernel, norm_mul, D5.S3.Weil.ZetaBridge.ClassicExplicitFormula.paperFT_eq_fourierLaplace]
  have hc : ‖(1 / (2 * Real.pi) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  rw [hc]
  have hn : (1 / (2 * Real.pi)) * ‖fourierLaplace b
      ((u : ℂ) + Complex.I * (β : ℂ))‖ ≤
      (1 / (2 * Real.pi)) * (D / (1 + u ^ 2)) := by
    exact mul_le_mul_of_nonneg_left (by simpa using h) (by positivity)
  convert hn using 1 <;> ring

private theorem stripKernel_bound (b : WeilTestFunction) {β : ℝ}
    (hβ : |β| ≤ 1 / 2) (u : ℝ) : ‖stripKernel b β u‖ ≤
      (closedStripJetBudget b (1 / 2) / (2 * Real.pi)) / (1 + u ^ 2) :=
  stripKernel_bound_of_decay b (closedStripJetBudget_spec b (1 / 2) (by norm_num)).2 hβ u

private theorem integrable_stripKernel (b : WeilTestFunction) {β : ℝ}
    (hβ : |β| ≤ 1 / 2) : Integrable (stripKernel b β) := by
  obtain ⟨D, _hD, hdecay⟩ := fourierLaplace_decay_closedStrip b (1 / 2) (by norm_num)
  apply (integrable_inv_one_add_sq.const_mul (D / (2 * Real.pi))).mono'
    (continuous_stripKernel b β).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun u => by
    simpa [div_eq_mul_inv] using stripKernel_bound_of_decay b hdecay hβ u

private theorem tilted_paperFT (b : WeilTestFunction) (β u : ℝ) :
    Zeta23.paperFT (fun x : ℝ => b x * Complex.exp (-(β : ℂ) * (x : ℂ))) u =
      Zeta23.paperFT b ((u : ℂ) + Complex.I * (β : ℂ)) := by
  unfold Zeta23.paperFT
  apply integral_congr_ae
  filter_upwards with x
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  ring_nf
  simp [Complex.I_sq, sub_eq_add_neg]

private theorem stripKernel_inversion (b : WeilTestFunction) {β : ℝ}
    (hβ : |β| ≤ 1 / 2) (x : ℝ) :
    (∫ u : ℝ, stripKernel b β u *
      Complex.exp (-Complex.I * (u : ℂ) * (x : ℂ))) =
      b x * Complex.exp (-(β : ℂ) * (x : ℂ)) := by
  let h : ℝ → ℂ := fun y => b y * Complex.exp (-(β : ℂ) * (y : ℂ))
  have hh : Continuous h := b.continuous.mul (by fun_prop)
  have hhi : Integrable h := hh.integrable_of_hasCompactSupport b.hasCompactSupport.mul_right
  have hhSmooth : ContDiff ℝ 2 h := by
    dsimp only [h]
    have hreal : ContDiff ℝ 2 (fun y : ℝ => (y : ℂ)) := Complex.ofRealCLM.contDiff
    have hlin : ContDiff ℝ 2 (fun y : ℝ => -(β : ℂ) * (y : ℂ)) :=
      contDiff_const.mul hreal
    exact (b.contDiff.of_le (by simp)).mul hlin.cexp
  have hFourier : Integrable (𝓕 h) :=
    Zeta23.EF.integrable_fourier_of_contDiff_two hhSmooth b.hasCompactSupport.mul_right
  have hinv := Zeta23.EF.paper_inversion hh hhi hFourier x
  change _ = h x
  rw [hinv, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with u
  dsimp only [h]
  rw [tilted_paperFT, stripKernel]
  ring

private theorem convolution_inversion
    {f K χ : ℝ → ℂ} (hf : Integrable f) (hK : Integrable K)
    (hinv : ∀ x : ℝ, ∫ u : ℝ, K u * Complex.exp (-Complex.I * (u : ℂ) * (x : ℂ)) = χ x)
    (t : ℝ) :
    (∫ s : ℝ, K (t - s) * Zeta23.paperFT f s) =
      ∫ x : ℝ, f x * Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) * χ x := by
  have hKt : Integrable (fun s : ℝ => K (t - s)) := hK.comp_sub_left t
  have hprod := hKt.norm.mul_prod hf.norm
  have hjoint : Integrable (fun p : ℝ × ℝ =>
      K (t - p.1) * (f p.2 * Complex.exp (Complex.I * (p.1 : ℂ) * (p.2 : ℂ))))
      (volume.prod volume) := by
    apply hprod.mono' (hKt.aestronglyMeasurable.comp_fst.mul
      (hf.aestronglyMeasurable.comp_snd.mul (by fun_prop)))
    filter_upwards with p
    simp [norm_mul, Zeta23.norm_cexp_I_mul]
  have houter : (∫ s : ℝ, K (t - s) * Zeta23.paperFT f s) =
      ∫ s : ℝ, ∫ x : ℝ,
        K (t - s) * (f x * Complex.exp (Complex.I * (s : ℂ) * (x : ℂ))) := by
    apply integral_congr_ae
    filter_upwards with s
    exact (integral_const_mul _ _).symm
  rw [houter, integral_integral_swap hjoint]
  apply integral_congr_ae
  filter_upwards with x
  have hshift :
      (∫ y : ℝ, K (t - y) * Complex.exp (Complex.I * (y : ℂ) * (x : ℂ))) =
        Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) * χ x := by
    rw [← hinv x, ← integral_const_mul,
      ← integral_sub_left_eq_self (fun u : ℝ =>
        Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) *
          (K u * Complex.exp (-Complex.I * (u : ℂ) * (x : ℂ)))) volume t]
    apply integral_congr_ae
    filter_upwards with y
    rw [mul_left_comm, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  calc
    _ = f x * ∫ y : ℝ, K (t - y) *
          Complex.exp (Complex.I * (y : ℂ) * (x : ℂ)) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with y
      ring
    _ = _ := by rw [hshift]; ring

/-- Finite-support L2 profiles have pointwise convolution reproduction at every
complex strip point. The Fubini and inversion hypotheses are derived. -/
theorem support_convolution_reproduction
    (b : WeilTestFunction) {a : ℝ} (hb : ∀ x ∈ Ioc (-a) a, b x = 1)
    {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂(volume : Measure ℝ), x ∉ Ioc (-a) a → f x = 0)
    {β : ℝ} (hβ : |β| ≤ 1 / 2) (t : ℝ) :
    (∫ s : ℝ, stripKernel b β (t - s) * Zeta23.paperFT f s) =
      Zeta23.paperFT f ((t : ℂ) + Complex.I * (β : ℂ)) := by
  rw [convolution_inversion (integrable_of_memLp_Ioc hf hs)
    (integrable_stripKernel b hβ) (stripKernel_inversion b hβ)]
  unfold Zeta23.paperFT
  apply integral_congr_ae
  filter_upwards [hs] with x hx
  by_cases h : x ∈ Ioc (-a) a
  · rw [hb x h, one_mul, mul_assoc, ← Complex.exp_add]
    congr 2
    ring_nf
    simp [Complex.I_sq, sub_eq_add_neg]
  · simp [hx h]

private theorem convolution_norm_sq_le {K F : ℝ → ℂ}
    (hK : Integrable K) (hF : AEStronglyMeasurable F volume)
    (hKF : Integrable (fun s : ℝ => ‖K s‖ * ‖F s‖ ^ 2)) :
    ‖∫ s : ℝ, K s * F s‖ ^ 2 ≤
      (∫ s : ℝ, ‖K s‖) * ∫ s : ℝ, ‖K s‖ * ‖F s‖ ^ 2 := by
  let u : ℝ → ℝ := fun s => Real.sqrt ‖K s‖
  let v : ℝ → ℝ := fun s => Real.sqrt ‖K s‖ * ‖F s‖
  have hu_meas : AEStronglyMeasurable u volume :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hK.aestronglyMeasurable.norm
  have hv_meas : AEStronglyMeasurable v volume := hu_meas.mul hF.norm
  have hu_sq : (fun s => u s ^ 2) = (fun s => ‖K s‖) := by
    funext s
    exact Real.sq_sqrt (norm_nonneg _)
  have hv_sq : (fun s => v s ^ 2) = (fun s => ‖K s‖ * ‖F s‖ ^ 2) := by
    funext s
    dsimp only [v]
    rw [mul_pow, Real.sq_sqrt (norm_nonneg _)]
  have hu : MemLp u 2 volume := (memLp_two_iff_integrable_sq hu_meas).mpr
    (hu_sq.symm ▸ hK.norm)
  have hv : MemLp v 2 volume := (memLp_two_iff_integrable_sq hv_meas).mpr
    (hv_sq.symm ▸ hKF)
  have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume) (f := u) (g := v)
    Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall (fun s => Real.sqrt_nonneg ‖K s‖))
    (Filter.Eventually.of_forall (fun s => mul_nonneg
      (Real.sqrt_nonneg ‖K s‖) (norm_nonneg (F s)))) (by simpa using hu) (by simpa using hv)
  have huv : (fun s => u s * v s) = (fun s => ‖K s‖ * ‖F s‖) := by
    funext s
    dsimp only [u, v]
    rw [← mul_assoc, Real.mul_self_sqrt (norm_nonneg _)]
  have hcs' : (∫ s : ℝ, ‖K s‖ * ‖F s‖) ≤
      Real.sqrt (∫ s : ℝ, ‖K s‖) *
      Real.sqrt (∫ s : ℝ, ‖K s‖ * ‖F s‖ ^ 2) := by
    simpa only [huv, Real.rpow_two, hu_sq, hv_sq, one_div,
      Real.sqrt_eq_rpow] using hcs
  have hnorm : ‖∫ s : ℝ, K s * F s‖ ≤
      Real.sqrt (∫ s : ℝ, ‖K s‖) *
      Real.sqrt (∫ s : ℝ, ‖K s‖ * ‖F s‖ ^ 2) := by
    have hnorm0 : ‖∫ s : ℝ, K s * F s‖ ≤ ∫ s : ℝ, ‖K s‖ * ‖F s‖ := by
      simpa only [norm_mul] using norm_integral_le_integral_norm (fun s : ℝ => K s * F s)
    exact hnorm0.trans hcs'
  calc
    _ ≤ (Real.sqrt (∫ s : ℝ, ‖K s‖) *
        Real.sqrt (∫ s : ℝ, ‖K s‖ * ‖F s‖ ^ 2)) ^ 2 := by
      gcongr
    _ = _ := by
      rw [mul_pow, Real.sq_sqrt (integral_nonneg (fun s => norm_nonneg _)),
        Real.sq_sqrt (integral_nonneg (fun s => by positivity))]

private theorem supported_strip_estimate
    (b : WeilTestFunction) {a : ℝ} (hb : ∀ x ∈ Ioc (-a) a, b x = 1)
    {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂(volume : Measure ℝ), x ∉ Ioc (-a) a → f x = 0)
    (hlog : Integrable (fun s : ℝ => Real.log (|s| + 3) *
      ‖Zeta23.paperFT f s‖ ^ 2))
    (z : ℂ) (hz : |z.im| ≤ 1 / 2) :
    ‖Zeta23.paperFT f z‖ ^ 2 ≤
      (Real.pi * (closedStripJetBudget b (1 / 2) / (2 * Real.pi)) ^ 2) *
        ∫ s : ℝ, ‖Zeta23.paperFT f s‖ ^ 2 / (1 + (z.re - s) ^ 2) := by
  let C : ℝ := closedStripJetBudget b (1 / 2) / (2 * Real.pi)
  have hC : 0 ≤ C := div_nonneg (closedStripJetBudget_spec b (1 / 2) (by norm_num)).1
    (by positivity)
  have hfi : Integrable f := integrable_of_memLp_Ioc hf hs
  have hF : Continuous (fun s : ℝ => Zeta23.paperFT f s) := by
    simp only [Zeta23.paperFT_ofReal_eq_fourier]
    have hc : Continuous (𝓕 f) := VectorFourier.fourierIntegral_continuous
      Real.continuous_fourierChar (innerSL ℝ).continuous₂ hfi
    exact hc.comp (by fun_prop)
  have hq : Integrable (fun s : ℝ => ‖Zeta23.paperFT f s‖ ^ 2) := by
    apply hlog.mono' (hF.norm.pow 2).aestronglyMeasurable
    filter_upwards with s
    change ‖‖Zeta23.paperFT f s‖ ^ 2‖ ≤ _
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have hL : 1 ≤ Real.log (|s| + 3) := by
      rw [Real.le_log_iff_exp_le (by positivity)]
      linarith [Real.exp_one_lt_d9, abs_nonneg s]
    nlinarith [sq_nonneg ‖Zeta23.paperFT f s‖]
  have hweight : Integrable (fun s : ℝ =>
      ‖Zeta23.paperFT f s‖ ^ 2 / (1 + (z.re - s) ^ 2)) := by
    have hmeas : Continuous (fun s : ℝ =>
        ‖Zeta23.paperFT f s‖ ^ 2 / (1 + (z.re - s) ^ 2)) :=
      (hF.norm.pow 2).div (by fun_prop) (fun s => by positivity)
    apply hq.mono' hmeas.aestronglyMeasurable
    filter_upwards with s
    rw [Real.norm_of_nonneg (by positivity)]
    exact div_le_self (sq_nonneg _) (by nlinarith [sq_nonneg (z.re - s)])
  have hK : Integrable (fun s : ℝ => stripKernel b z.im (z.re - s)) :=
    (integrable_stripKernel b hz).comp_sub_left z.re
  have hmajor : Integrable (fun s : ℝ => C / (1 + (z.re - s) ^ 2)) := by
    simpa only [div_eq_mul_inv] using
      (integrable_inv_one_add_sq.comp_sub_left z.re).const_mul C
  have hKF : Integrable (fun s : ℝ =>
      ‖stripKernel b z.im (z.re - s)‖ * ‖Zeta23.paperFT f s‖ ^ 2) := by
    apply (hweight.const_mul C).mono' (by
      exact (continuous_stripKernel b z.im |>.comp (by fun_prop)).norm.aestronglyMeasurable.mul
        (hF.norm.pow 2).aestronglyMeasurable)
    filter_upwards with s
    rw [Real.norm_of_nonneg (by positivity)]
    calc
      _ ≤ (C / (1 + (z.re - s) ^ 2)) * ‖Zeta23.paperFT f s‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (stripKernel_bound b hz _) (sq_nonneg _)
      _ = _ := by ring
  have hKint : (∫ s : ℝ, ‖stripKernel b z.im (z.re - s)‖) ≤ C * Real.pi := by
    calc
      _ ≤ ∫ s : ℝ, C / (1 + (z.re - s) ^ 2) :=
        integral_mono hK.norm hmajor (fun s => stripKernel_bound b hz _)
      _ = C * Real.pi := by
        simp only [div_eq_mul_inv, integral_const_mul]
        have hi := integral_sub_left_eq_self (fun s : ℝ => (1 + s ^ 2)⁻¹) volume z.re
        rw [hi, integral_univ_inv_one_add_sq]
  have hKFint : (∫ s : ℝ,
      ‖stripKernel b z.im (z.re - s)‖ * ‖Zeta23.paperFT f s‖ ^ 2) ≤
      C * ∫ s : ℝ, ‖Zeta23.paperFT f s‖ ^ 2 / (1 + (z.re - s) ^ 2) := by
    rw [← integral_const_mul]
    apply integral_mono hKF (hweight.const_mul C)
    intro s
    calc
      _ ≤ (C / (1 + (z.re - s) ^ 2)) * ‖Zeta23.paperFT f s‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (stripKernel_bound b hz _) (sq_nonneg _)
      _ = _ := by ring
  have hrepro := support_convolution_reproduction b hb hf hs hz z.re
  have hzeta : (z.re : ℂ) + Complex.I * (z.im : ℂ) = z := by
    apply Complex.ext <;> simp
  rw [hzeta] at hrepro
  rw [← hrepro]
  calc
    _ ≤ (∫ s : ℝ, ‖stripKernel b z.im (z.re - s)‖) *
        ∫ s : ℝ, ‖stripKernel b z.im (z.re - s)‖ * ‖Zeta23.paperFT f s‖ ^ 2 :=
      convolution_norm_sq_le hK hF.aestronglyMeasurable hKF
    _ ≤ (C * Real.pi) *
        (C * ∫ s : ℝ, ‖Zeta23.paperFT f s‖ ^ 2 / (1 + (z.re - s) ^ 2)) :=
      mul_le_mul hKint hKFint (integral_nonneg (fun s => by positivity)) (by positivity)
    _ = _ := by dsimp only [C]; ring

private def samplingBump (a : ℝ) (ha : 0 < a) : ContDiffBump (0 : ℝ) where
  rIn := a
  rOut := a + 1
  rIn_pos := ha
  rIn_lt_rOut := by linarith

private def samplingCutoff (a : ℝ) (ha : 0 < a) : WeilTestFunction where
  toFun x := ((samplingBump a ha) x : ℂ)
  contDiff' := Complex.ofRealCLM.contDiff.comp (samplingBump a ha).contDiff
  hasCompactSupport' := (samplingBump a ha).hasCompactSupport.comp_left Complex.ofReal_zero
  even' x := by exact_mod_cast (samplingBump a ha).neg x

private theorem samplingCutoff_one (a : ℝ) (ha : 0 < a) (x : ℝ)
    (hx : x ∈ Ioc (-a) a) : samplingCutoff a ha x = 1 := by
  change ((samplingBump a ha) x : ℂ) = 1
  have h : x ∈ Metric.closedBall (0 : ℝ) (samplingBump a ha).rIn := by
    simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
    exact abs_le.mpr ⟨hx.1.le, hx.2⟩
  exact_mod_cast (samplingBump a ha).one_of_mem_closedBall h
/-- Exact finite local-count kernel bound, reusing the frozen WindowZero supplier. -/
private theorem original_zero_kernel_finite_le
    (Z : Zeta23.ZeroConfig) {A : ℝ} (hA : 1 ≤ A)
    (hlocal : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A * Real.log (|t| + 3))
    (s : ℝ) (E : Finset Z.carrier) :
    ∑ ρ ∈ E, (Z.mult ρ : ℝ) / (1 + (s - (Zeta23.gammaOf ρ).re) ^ 2) ≤
      8 * A * Zeta23.WeilEF.totalWeight * Real.log (|s| + 3) := by
  classical
  have hLC := Zeta23.Tail.LocalCount.ofWindowCount Z hA hlocal
  have hbase := D5.S3.Weil.ZeroInfinitude.WindowZero.shifted_inv_sq_finite_le
    (γ := fun ρ : Z.carrier => (ρ : ℂ).im)
    (m := fun ρ : Z.carrier => Z.mult ρ) (A₀ := A) (T := s) hLC E
  have hL : 1 ≤ Real.log (|s| + 3) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have he := Real.exp_one_lt_d9
    linarith [abs_nonneg s]
  have hlog_int (n : ℤ) : 1 ≤ Real.log (|(n : ℝ)| + 3) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have he := Real.exp_one_lt_d9
    linarith [abs_nonneg (n : ℝ)]
  have hW0 : ∀ (B : Finset ℤ),
      (∑ n ∈ B, 1 / (1 + (n : ℝ) ^ 2)) ≤ Zeta23.WeilEF.totalWeight := by
    intro B
    refine le_trans (Finset.sum_le_sum (fun n hn => ?_))
      (Zeta23.WeilEF.summable_weight.sum_le_tsum _ (fun n _ => ?_))
    · exact div_le_div_of_nonneg_right (hlog_int n) (by positivity)
    · exact div_nonneg (Real.log_nonneg (by linarith [abs_nonneg (n : ℝ)])) (by positivity)
  have hsum :
      (∑ n ∈ E.image (fun ρ : Z.carrier => Zeta23.WeilEF.key
        ((ρ : ℂ).im - s)),
        1 / (1 + (n : ℝ) ^ 2)) ≤ Zeta23.WeilEF.totalWeight :=
    hW0 _
  have hbase' :
      ∑ ρ ∈ E, (Z.mult ρ : ℝ) /
          (1 + ((ρ : ℂ).im - s) ^ 2) ≤
        4 * A * (Real.log (|s| + 3) * Zeta23.WeilEF.totalWeight +
          Zeta23.WeilEF.totalWeight) := by
    calc
      _ ≤ 4 * A * (Real.log (|s| + 3) *
          (∑ n ∈ E.image (fun ρ : Z.carrier => Zeta23.WeilEF.key
            ((ρ : ℂ).im - s)), 1 / (1 + (n : ℝ) ^ 2)) +
            Zeta23.WeilEF.totalWeight) := hbase
      _ ≤ _ := by gcongr
  calc
    ∑ ρ ∈ E, (Z.mult ρ : ℝ) / (1 + (s - (Zeta23.gammaOf ρ).re) ^ 2) =
        ∑ ρ ∈ E, (Z.mult ρ : ℝ) /
          (1 + ((ρ : ℂ).im - s) ^ 2) := by
            apply Finset.sum_congr rfl
            intro ρ hρ
            simp only [Zeta23.WeilEF.gammaOf_re]
            congr 2
            ring
    _ ≤ 4 * A * (Real.log (|s| + 3) * Zeta23.WeilEF.totalWeight +
          Zeta23.WeilEF.totalWeight) := hbase'
    _ ≤ 8 * A * Zeta23.WeilEF.totalWeight * Real.log (|s| + 3) := by
      have hW : 0 ≤ Zeta23.WeilEF.totalWeight := by
        exact tsum_nonneg (fun n => div_nonneg
          (Real.log_nonneg (by linarith [abs_nonneg (n : ℝ)])) (by positivity))
      have hterm : Zeta23.WeilEF.totalWeight ≤
          Real.log (|s| + 3) * Zeta23.WeilEF.totalWeight := by
        calc
          Zeta23.WeilEF.totalWeight = 1 * Zeta23.WeilEF.totalWeight := by ring
          _ ≤ Real.log (|s| + 3) * Zeta23.WeilEF.totalWeight :=
            mul_le_mul_of_nonneg_right hL hW
      have hA0 : 0 ≤ A := by linarith
      calc
        4 * A * (Real.log (|s| + 3) * Zeta23.WeilEF.totalWeight +
            Zeta23.WeilEF.totalWeight) ≤
            4 * A * (Real.log (|s| + 3) * Zeta23.WeilEF.totalWeight +
              Real.log (|s| + 3) * Zeta23.WeilEF.totalWeight) := by
                exact mul_le_mul_of_nonneg_left
                  (add_le_add_right hterm
                    (Real.log (|s| + 3) * Zeta23.WeilEF.totalWeight)) (by positivity)
        _ = 8 * A * Zeta23.WeilEF.totalWeight * Real.log (|s| + 3) := by ring

/--
The actual two-family weighted sampling consumer.  The strip estimate and the
integrability of its real-line kernels are explicit supplier obligations; the
zero-side conclusion itself uses the original carrier and multiplicities.
-/
private theorem weighted_zero_sampling_two_families
    (Z : Zeta23.ZeroConfig) {A B : ℝ} (hA : 1 ≤ A) (hB : 0 ≤ B)
    (hlocal : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A * Real.log (|t| + 3))
    {F : ℂ → ℂ} {q : ℝ → ℝ}
    (hq_log : Integrable (fun s : ℝ => Real.log (|s| + 3) * q s))
    (hq_nonneg : ∀ᵐ s ∂(volume : Measure ℝ), 0 ≤ q s)
    (hkernel : ∀ t : ℝ, Integrable (fun s : ℝ => q s /
      (1 + (t - s) ^ 2)))
    (hstrip : ∀ z : ℂ, |z.im| ≤ 1 / 2 →
      ‖F z‖ ^ 2 ≤ B * ∫ s : ℝ, q s / (1 + (z.re - s) ^ 2)) :
    (Summable (fun ρ : Z.carrier =>
        (Z.mult ρ : ℝ) * ‖F (Zeta23.gammaOf ρ)‖ ^ 2) ∧
      (∑' ρ : Z.carrier, (Z.mult ρ : ℝ) * ‖F (Zeta23.gammaOf ρ)‖ ^ 2) ≤
        8 * B * A * Zeta23.WeilEF.totalWeight *
          ∫ s : ℝ, Real.log (|s| + 3) * q s) ∧
    (Summable (fun ρ : Z.carrier =>
        (Z.mult ρ : ℝ) * ‖F (conj (Zeta23.gammaOf ρ))‖ ^ 2) ∧
      (∑' ρ : Z.carrier, (Z.mult ρ : ℝ) *
        ‖F (conj (Zeta23.gammaOf ρ))‖ ^ 2) ≤
        8 * B * A * Zeta23.WeilEF.totalWeight *
          ∫ s : ℝ, Real.log (|s| + 3) * q s) := by
  classical
  have hqlog0 : 0 ≤ᵐ[volume] fun s : ℝ => Real.log (|s| + 3) * q s := by
    filter_upwards [hq_nonneg] with s hs
    exact mul_nonneg (Real.log_nonneg (by linarith [abs_nonneg s])) hs
  have hE : 0 ≤ ∫ s : ℝ, Real.log (|s| + 3) * q s :=
    integral_nonneg_of_ae hqlog0
  have hfinite (z : Z.carrier → ℂ) (E : Finset Z.carrier)
      (hz : ∀ ρ ∈ E, |(z ρ).im| ≤ 1 / 2)
      (hKbound : ∀ s : ℝ, ∀ E : Finset Z.carrier,
        ∑ ρ ∈ E, (Z.mult ρ : ℝ) /
          (1 + (s - (z ρ).re) ^ 2) ≤
            8 * A * Zeta23.WeilEF.totalWeight * Real.log (|s| + 3))
      :
      ∑ ρ ∈ E, (Z.mult ρ : ℝ) * ‖F (z ρ)‖ ^ 2 ≤
        8 * B * A * Zeta23.WeilEF.totalWeight *
          ∫ s : ℝ, Real.log (|s| + 3) * q s := by
    have hterm (ρ : Z.carrier) (hρ : ρ ∈ E) :
        (Z.mult ρ : ℝ) * ‖F (z ρ)‖ ^ 2 ≤
          (Z.mult ρ : ℝ) *
            (B * ∫ s : ℝ, q s / (1 + ((z ρ).re - s) ^ 2)) := by
      exact mul_le_mul_of_nonneg_left (hstrip (z ρ) (hz ρ hρ)) (by positivity)
    calc
      ∑ ρ ∈ E, (Z.mult ρ : ℝ) * ‖F (z ρ)‖ ^ 2 ≤
          ∑ ρ ∈ E, (Z.mult ρ : ℝ) *
            (B * ∫ s : ℝ, q s / (1 + ((z ρ).re - s) ^ 2)) :=
        Finset.sum_le_sum (fun ρ hρ => hterm ρ hρ)
      _ = ∑ ρ ∈ E, ∫ s : ℝ,
          B * ((Z.mult ρ : ℝ) *
            (q s / (1 + ((z ρ).re - s) ^ 2))) := by
        apply Finset.sum_congr rfl
        intro ρ hρ
        rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul]
        apply integral_congr_ae
        filter_upwards with s
        ring
      _ = B * ∫ s : ℝ, q s *
          (∑ ρ ∈ E, (Z.mult ρ : ℝ) /
            (1 + ((z ρ).re - s) ^ 2)) := by
        rw [← MeasureTheory.integral_finsetSum]
        · rw [← MeasureTheory.integral_const_mul]
          apply integral_congr_ae
          filter_upwards with s
          simp_rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro ρ hρ
          ring
        · intro ρ hρ
          have hi := hkernel (z ρ).re
          have hscaled := hi.const_mul (B * (Z.mult ρ : ℝ))
          refine hscaled.congr ?_
          filter_upwards with s
          ring
      _ ≤ B * ∫ s : ℝ, Real.log (|s| + 3) * q s *
          (8 * A * Zeta23.WeilEF.totalWeight) := by
        have hleft : Integrable (fun s : ℝ => q s *
            (∑ ρ ∈ E, (Z.mult ρ : ℝ) /
              (1 + ((z ρ).re - s) ^ 2))) := by
          have hsum : Integrable (fun s : ℝ =>
              ∑ ρ ∈ E, (Z.mult ρ : ℝ) *
                (q s / (1 + ((z ρ).re - s) ^ 2))) := by
            apply MeasureTheory.integrable_finsetSum E
            intro ρ hρ
            exact (hkernel (z ρ).re).const_mul (Z.mult ρ : ℝ)
          refine hsum.congr ?_
          filter_upwards with s
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro ρ hρ
          ring
        have hright : Integrable (fun s : ℝ => Real.log (|s| + 3) * q s *
            (8 * A * Zeta23.WeilEF.totalWeight)) :=
          hq_log.mul_const (8 * A * Zeta23.WeilEF.totalWeight)
        refine mul_le_mul_of_nonneg_left
          (MeasureTheory.integral_mono_ae hleft hright ?_) (by positivity)
        filter_upwards [hq_nonneg] with s hs
        calc
          q s * (∑ ρ ∈ E, (Z.mult ρ : ℝ) /
                (1 + ((z ρ).re - s) ^ 2)) =
                q s * (∑ ρ ∈ E, (Z.mult ρ : ℝ) /
                  (1 + (s - (z ρ).re) ^ 2)) := by
                    congr 2
                    apply funext
                    intro ρ
                    congr 2
                    ring
          _ ≤ q s * (8 * A * Zeta23.WeilEF.totalWeight *
                Real.log (|s| + 3)) := by
            exact mul_le_mul_of_nonneg_left (hKbound s E) (by positivity)
          _ = Real.log (|s| + 3) * q s *
                (8 * A * Zeta23.WeilEF.totalWeight) := by ring
      _ = 8 * B * A * Zeta23.WeilEF.totalWeight *
          ∫ s : ℝ, Real.log (|s| + 3) * q s := by
        rw [MeasureTheory.integral_mul_const]
        ring
  have hγ (ρ : Z.carrier) : |(Zeta23.gammaOf ρ).im| ≤ 1 / 2 := by
    exact Zeta23.WeilEF.abs_gammaOf_im_le (Z.strip (ρ : ℂ) ρ.2)
  have hcγ (ρ : Z.carrier) :
      |(conj (Zeta23.gammaOf ρ)).im| ≤ 1 / 2 := by
    simpa [abs_neg] using hγ ρ
  have hnonnegγ (ρ : Z.carrier) : 0 ≤
      (Z.mult ρ : ℝ) * ‖F (Zeta23.gammaOf ρ)‖ ^ 2 := by positivity
  have hnonnegcγ (ρ : Z.carrier) : 0 ≤
      (Z.mult ρ : ℝ) * ‖F (conj (Zeta23.gammaOf ρ))‖ ^ 2 := by positivity
  let zγ : Z.carrier → ℂ := fun ρ => Zeta23.gammaOf ρ
  let zcγ : Z.carrier → ℂ := fun ρ => conj (Zeta23.gammaOf ρ)
  have hKγ (s : ℝ) (E : Finset Z.carrier) :
      ∑ ρ ∈ E, (Z.mult ρ : ℝ) /
        (1 + (s - (zγ ρ).re) ^ 2) ≤
          8 * A * Zeta23.WeilEF.totalWeight * Real.log (|s| + 3) := by
    simpa [zγ] using original_zero_kernel_finite_le Z hA hlocal s E
  have hKcγ (s : ℝ) (E : Finset Z.carrier) :
      ∑ ρ ∈ E, (Z.mult ρ : ℝ) /
        (1 + (s - (zcγ ρ).re) ^ 2) ≤
          8 * A * Zeta23.WeilEF.totalWeight * Real.log (|s| + 3) := by
    simpa [zcγ, Zeta23.WeilEF.gammaOf_re] using original_zero_kernel_finite_le Z hA hlocal s E
  have hsγ := summable_of_sum_le hnonnegγ
    (fun E => hfinite zγ E (fun ρ hρ => hγ ρ) hKγ)
  have hscγ := summable_of_sum_le hnonnegcγ
    (fun E => hfinite zcγ E (fun ρ hρ => hcγ ρ) hKcγ)
  refine ⟨⟨?_, hsγ.tsum_le_of_sum_le
      (fun E => hfinite zγ E (fun ρ hρ => hγ ρ) hKγ)⟩,
    ⟨?_, hscγ.tsum_le_of_sum_le
      (fun E => hfinite zcγ E (fun ρ hρ => hcγ ρ) hKcγ)⟩⟩
  · exact hsγ
  · exact hscγ


/-- A support-dependent constant is fixed before the zero configuration, local
count constant, and supported complex L2 profile are chosen. -/
theorem weighted_zero_sampling_Ioc (a : ℝ) (ha : 0 < a) :
    ∃ C_a : ℝ, 0 ≤ C_a ∧ ∀ (Z : Zeta23.ZeroConfig) (A : ℝ), 1 ≤ A →
      (∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A * Real.log (|t| + 3)) →
      ∀ f : ℝ → ℂ, MemLp f 2 volume →
      (∀ᵐ x ∂(volume : Measure ℝ), x ∉ Ioc (-a) a → f x = 0) →
      Integrable (fun s : ℝ => Real.log (|s| + 3) *
        Complex.normSq (Zeta23.paperFT f s)) →
      Integrable f ∧
      (Summable (fun ρ : Z.carrier =>
          (Z.mult ρ : ℝ) * Complex.normSq (Zeta23.paperFT f (Zeta23.gammaOf ρ))) ∧
        (∑' ρ : Z.carrier, (Z.mult ρ : ℝ) *
          Complex.normSq (Zeta23.paperFT f (Zeta23.gammaOf ρ))) ≤
          C_a * A * Zeta23.WeilEF.totalWeight *
            ∫ s : ℝ, Real.log (|s| + 3) * Complex.normSq (Zeta23.paperFT f s)) ∧
      (Summable (fun ρ : Z.carrier => (Z.mult ρ : ℝ) *
          Complex.normSq (Zeta23.paperFT f (conj (Zeta23.gammaOf ρ)))) ∧
        (∑' ρ : Z.carrier, (Z.mult ρ : ℝ) *
          Complex.normSq (Zeta23.paperFT f (conj (Zeta23.gammaOf ρ)))) ≤
          C_a * A * Zeta23.WeilEF.totalWeight *
            ∫ s : ℝ, Real.log (|s| + 3) * Complex.normSq (Zeta23.paperFT f s)) := by
  let b := samplingCutoff a ha
  let B : ℝ := Real.pi * (closedStripJetBudget b (1 / 2) / (2 * Real.pi)) ^ 2
  refine ⟨8 * B, by dsimp only [B]; positivity, ?_⟩
  intro Z A hA hlocal f hf hs hlog
  have hfi : Integrable f := integrable_of_memLp_Ioc hf hs
  have hlog' : Integrable (fun s : ℝ => Real.log (|s| + 3) *
      ‖Zeta23.paperFT f s‖ ^ 2) := by
    simpa only [Complex.normSq_eq_norm_sq] using hlog
  have hF : Continuous (fun s : ℝ => Zeta23.paperFT f s) := by
    simp only [Zeta23.paperFT_ofReal_eq_fourier]
    have hc : Continuous (𝓕 f) := VectorFourier.fourierIntegral_continuous
      Real.continuous_fourierChar (innerSL ℝ).continuous₂ hfi
    exact hc.comp (by fun_prop)
  have hkernel (t : ℝ) : Integrable (fun s : ℝ =>
      ‖Zeta23.paperFT f s‖ ^ 2 / (1 + (t - s) ^ 2)) := by
    have hmeas : Continuous (fun s : ℝ =>
        ‖Zeta23.paperFT f s‖ ^ 2 / (1 + (t - s) ^ 2)) :=
      (hF.norm.pow 2).div (by fun_prop) (fun s => by positivity)
    apply hlog'.mono' hmeas.aestronglyMeasurable
    filter_upwards with s
    rw [Real.norm_of_nonneg (by positivity)]
    have hL : 1 ≤ Real.log (|s| + 3) := by
      rw [Real.le_log_iff_exp_le (by positivity)]
      linarith [Real.exp_one_lt_d9, abs_nonneg s]
    calc
      _ ≤ ‖Zeta23.paperFT f s‖ ^ 2 := div_le_self (sq_nonneg _)
        (by nlinarith [sq_nonneg (t - s)])
      _ ≤ Real.log (|s| + 3) * ‖Zeta23.paperFT f s‖ ^ 2 := by
        nlinarith [sq_nonneg ‖Zeta23.paperFT f s‖]
  have hstrip := supported_strip_estimate b (samplingCutoff_one a ha) hf hs hlog'
  have hout := weighted_zero_sampling_two_families Z hA (show 0 ≤ B by dsimp only [B]; positivity)
    hlocal hlog' (Filter.Eventually.of_forall (fun s => sq_nonneg ‖Zeta23.paperFT f s‖))
    hkernel hstrip
  refine ⟨hfi, ?_⟩
  simpa only [Complex.normSq_eq_norm_sq, mul_assoc] using hout

#print axioms support_convolution_reproduction
#print axioms weighted_zero_sampling_Ioc

end Zeta23.WeilEF.WeightedZeroSampling
