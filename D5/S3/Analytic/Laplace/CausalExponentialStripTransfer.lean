/- GID: D5/S3/Analytic/Laplace/CausalExponentialStripTransfer
   generality: G
   mirror-B: D5/B/S3/Analytic/Laplace/CausalExponentialStripTransfer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Causal exponential smoothing transfers L² membership across a left strip. -/

import D5.S3.Analytic.Laplace.ExponentialMultiplierFourier
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Left-strip transfer by causal exponential smoothing and Fourier inversion. -/

namespace D5.S3.Analytic.Laplace.CausalExponentialStripTransfer

open Complex (I)
open ContinuousLinearMap Filter MeasureTheory Set
open scoped Convolution FourierTransform Topology

open D5.S3.Analytic.Laplace.ExponentialMultiplierContour

noncomputable section

private def density (c a : ℝ) : ℝ → ℝ :=
  (Ici 0).indicator (fun s => c * Real.exp (-a * s))

/-- A causal exponential with amplitude `c` and rate `a`. -/
def kernel (c a : ℝ) (s : ℝ) : ℂ :=
  (density c a s : ℂ)

/-- Its multiplier in the normalized Fourier variable. -/
def multiplier (c a ξ : ℝ) : ℂ :=
  (c : ℂ) / ((a : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I)

def smoothing (c : ℝ) (g : ℝ → ℂ) : ℝ → ℂ :=
  kernel c c ⋆[mul ℂ ℂ] g

def tilt (d : ℝ) (g : ℝ → ℂ) (t : ℝ) : ℂ :=
  (Real.exp (-d * t) : ℂ) * g t

def sectionAt (F : ℂ → ℂ) (a ξ : ℝ) : ℂ :=
  F ((a : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I)

private theorem density_nonneg {c : ℝ} (hc : 0 ≤ c) (a s : ℝ) :
    0 ≤ density c a s := by
  by_cases hs : s ∈ Ici (0 : ℝ)
  · rw [density, indicator_of_mem hs]
    exact mul_nonneg hc (Real.exp_nonneg _)
  · simpa only [density, indicator_of_notMem hs] using (le_rfl : (0 : ℝ) ≤ 0)

private theorem norm_kernel {c : ℝ} (hc : 0 ≤ c) (a s : ℝ) :
    ‖kernel c a s‖ = density c a s := by
  rw [kernel, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (density_nonneg hc a s)]

private theorem norm_kernel_le {c a : ℝ} (hc : 0 ≤ c) (ha : 0 ≤ a) (s : ℝ) :
    ‖kernel c a s‖ ≤ c := by
  rw [norm_kernel hc]
  by_cases hs : s ∈ Ici (0 : ℝ)
  · rw [density, indicator_of_mem hs]
    exact mul_le_of_le_one_right hc
      (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha) hs))
  · simpa only [density, indicator_of_notMem hs] using hc

private theorem integrable_density (c : ℝ) {a : ℝ} (ha : 0 < a) :
    Integrable (density c a) := by
  unfold density
  apply IntegrableOn.integrable_indicator _ measurableSet_Ici
  apply (integrableOn_Ici_iff_integrableOn_Ioi).mpr
  exact (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr ha) 0).const_mul c

private theorem integrable_kernel (c : ℝ) {a : ℝ} (ha : 0 < a) :
    Integrable (kernel c a) :=
  (integrable_density c ha).ofReal

private theorem measurable_kernel (c a : ℝ) : Measurable (kernel c a) := by
  have h : Measurable (fun s : ℝ => c * Real.exp (-a * s)) := by fun_prop
  exact Complex.continuous_ofReal.measurable.comp (h.indicator measurableSet_Ici)

private theorem continuousAt_kernel (c a : ℝ) {s : ℝ} (hs : s ≠ 0) :
    ContinuousAt (kernel c a) s := by
  rcases lt_or_gt_of_ne hs with h | h
  · refine (continuousAt_const (y := (0 : ℂ))).congr ?_
    filter_upwards [eventually_lt_nhds h] with u hu
    simp [kernel, density, not_le.mpr hu]
  · have hcont : Continuous (fun u : ℝ => (↑(c * Real.exp (-a * u)) : ℂ)) := by
      apply Complex.continuous_ofReal.comp
      fun_prop
    refine hcont.continuousAt.congr ?_
    filter_upwards [eventually_gt_nhds h] with u hu
    simp [kernel, density, hu.le]

/-- The Fourier multiplier of the causal exponential, including the old-line tilt. -/
theorem fourier_kernel (c : ℝ) {a : ℝ} (ha : 0 < a) (ξ : ℝ) :
    𝓕 (kernel c a) ξ = multiplier c a ξ := by
  let b : ℂ := (a : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I
  have hb : (-b).re < 0 := by simpa [b] using ha
  rw [Real.fourier_eq']
  calc
    _ = ∫ s : ℝ, (Ici (0 : ℝ)).indicator (fun u : ℝ => (c : ℂ) * Complex.exp (-b * u)) s := by
      apply integral_congr_ae
      filter_upwards with s
      simp only [Real.inner_apply, smul_eq_mul]
      by_cases hs : s ∈ Ici (0 : ℝ)
      · simp only [kernel, density, indicator_of_mem hs]
        rw [Complex.ofReal_mul c (Real.exp (-a * s)), Complex.ofReal_exp]
        have hphase :
            ((-2 * Real.pi * (s * ξ) : ℝ) : ℂ) * I + ((-a * s : ℝ) : ℂ) =
              -b * (s : ℂ) := by
          dsimp [b]
          push_cast
          ring
        calc
          _ = (c : ℂ) * (Complex.exp (((-2 * Real.pi * (s * ξ) : ℝ) : ℂ) * I) *
              Complex.exp ((-a * s : ℝ) : ℂ)) := by ring
          _ = _ := by rw [← Complex.exp_add, hphase]
      · simp [kernel, density, hs]
    _ = (c : ℂ) * ∫ s : ℝ in Ioi 0, Complex.exp (-b * s) := by
      rw [integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi, integral_const_mul]
    _ = _ := by
      rw [integral_exp_mul_complex_Ioi (a := -b) hb 0]
      simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, neg_div_neg_eq,
        mul_one_div, multiplier, b]

/-- The integrand in the old-line convolution is absolutely integrable at every point. -/
theorem integrable_oldLine_integrand {c a : ℝ} (hc : 0 ≤ c) (ha : 0 < a)
    {g₀ : ℝ → ℂ} (hg₀ : Integrable g₀) (t : ℝ) :
    Integrable (fun s => kernel c a s * g₀ (t - s)) := by
  have hshift := hg₀.comp_sub_left t
  refine (hshift.norm.const_mul c).mono'
    ((measurable_kernel c a).aestronglyMeasurable.mul hshift.aestronglyMeasurable) ?_
  filter_upwards with s
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_kernel_le hc ha.le _) (norm_nonneg _)

private theorem continuous_oldLine {c a : ℝ} (hc : 0 ≤ c) (ha : 0 < a)
    {g₀ : ℝ → ℂ} (hg₀ : Integrable g₀) :
    Continuous (kernel c a ⋆[mul ℂ ℂ] g₀) := by
  have heq : kernel c a ⋆[mul ℂ ℂ] g₀ = fun t => ∫ s, kernel c a (t - s) * g₀ s :=
    funext fun t => convolution_mul_swap (x := t)
  rw [heq]
  refine continuous_iff_continuousAt.2 fun t => ?_
  apply continuousAt_of_dominated
    (F := fun x s => kernel c a (x - s) * g₀ s) (bound := fun s => c * ‖g₀ s‖)
  · refine Eventually.of_forall fun x => ?_
    simpa only [sub_sub_cancel] using
      ((integrable_oldLine_integrand hc ha hg₀ x).comp_sub_left x).aestronglyMeasurable
  · refine Eventually.of_forall fun x => ?_
    filter_upwards with s
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (norm_kernel_le hc ha.le _) (norm_nonneg _)
  · exact hg₀.norm.const_mul c
  · filter_upwards [(volume : Measure ℝ).ae_ne t] with s hs
    have hsub : ContinuousAt (fun x : ℝ => x - s) t := by fun_prop
    have hk := continuousAt_kernel c a (s := t - s) (sub_ne_zero.mpr hs.symm)
    exact (hk.comp' (f := fun x : ℝ => x - s) hsub).mul continuousAt_const

/-- Ordinary inversion identifies the continuous old-line convolution at every point. -/
theorem oldLineSmoothing_eq_fourierInv {c a : ℝ} (hc : 0 ≤ c) (ha : 0 < a)
    {g₀ : ℝ → ℂ} (hg₀ : Integrable g₀)
    (hfreq : Integrable (fun ξ => 𝓕 g₀ ξ * multiplier c a ξ)) :
    kernel c a ⋆[mul ℂ ℂ] g₀ = 𝓕⁻ (fun ξ => 𝓕 g₀ ξ * multiplier c a ξ) := by
  have hk := integrable_kernel c ha
  have hfourier : 𝓕 (kernel c a ⋆[mul ℂ ℂ] g₀) = fun ξ => 𝓕 g₀ ξ * multiplier c a ξ := by
    funext ξ
    rw [Real.fourier_mul_convolution_eq hk hg₀, fourier_kernel c ha, mul_comm]
  have hfreq' : Integrable (𝓕 (kernel c a ⋆[mul ℂ ℂ] g₀)) := by
    rw [hfourier]
    exact hfreq
  have hinv := (continuous_oldLine hc ha hg₀).fourierInv_fourier_eq
    (hk.integrable_convolution (mul ℂ ℂ) hg₀) hfreq'
  rw [hfourier] at hinv
  exact hinv.symm

private theorem integral_density_tail {c : ℝ} (hc : 0 < c) {δ : ℝ} (hδ : 0 ≤ δ) :
    (∫ s : ℝ, (Ici δ).indicator (density c c) s) = Real.exp (-c * δ) := by
  rw [integral_indicator measurableSet_Ici]
  calc
    _ = ∫ s : ℝ in Ici δ, c * Real.exp (-c * s) := by
      apply setIntegral_congr_fun measurableSet_Ici
      intro s hs
      rw [density, indicator_of_mem (show s ∈ Ici (0 : ℝ) from hδ.trans hs)]
    _ = _ := by
      rw [integral_Ici_eq_integral_Ioi, integral_const_mul,
        integral_exp_mul_Ioi (neg_lt_zero.mpr hc) δ]
      field_simp [hc.ne']

private theorem integral_density {c : ℝ} (hc : 0 < c) :
    (∫ s : ℝ, density c c s) = 1 := by
  have heq : (Ici (0 : ℝ)).indicator (density c c) = density c c := by
    funext s
    by_cases hs : s ∈ Ici (0 : ℝ) <;> simp [density, hs]
  simpa only [heq, mul_zero, Real.exp_zero] using integral_density_tail hc (δ := 0) le_rfl

private theorem integral_kernel {c : ℝ} (hc : 0 < c) :
    (∫ s : ℝ, kernel c c s) = 1 := by
  change (∫ s : ℝ, (density c c s : ℂ)) = 1
  rw [integral_complex_ofReal, integral_density hc, Complex.ofReal_one]

/-- A pointwise prefix bound suffices for absolute integrability of the local smoothing. -/
theorem integrable_smoothing_integrand {c t M : ℝ} (hc : 0 < c)
    {g : ℝ → ℂ} (hg : Measurable g) (hM : ∀ x ≤ t, ‖g x‖ ≤ M) :
    Integrable (fun s => kernel c c s * g (t - s)) := by
  have hm : Measurable (fun s : ℝ => kernel c c s * g (t - s)) :=
    (measurable_kernel c c).mul (hg.comp (measurable_id.const_sub t))
  refine ((integrable_density c hc).mul_const M).mono' hm.aestronglyMeasurable ?_
  filter_upwards with s
  rw [norm_mul, norm_kernel hc.le]
  by_cases hs : s ∈ Ici (0 : ℝ)
  · exact mul_le_mul_of_nonneg_left (hM _ (sub_le_self _ hs)) (density_nonneg hc.le c s)
  · simp [density, hs]

/-- The causal exponential smoothing converges at any continuity point with a bounded past. -/
theorem smoothing_tendsto_atTop {g : ℝ → ℂ} (hg : Measurable g)
    {t M : ℝ} (ht : ContinuousAt g t) (hM : ∀ x ≤ t, ‖g x‖ ≤ M) :
    Tendsto (fun c : ℝ => smoothing c g t) atTop (𝓝 (g t)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hnear⟩ := Metric.continuousAt_iff.mp ht (ε / 2) (by positivity)
  have harg : Tendsto (fun c : ℝ => -c * δ) atTop atBot := by
    convert (tendsto_id : Tendsto (fun c : ℝ => c) atTop atTop).const_mul_atTop_of_neg
      (neg_lt_zero.mpr hδ) using 1
    funext c
    simp only [id_eq]
    ring
  have htail_lim : Tendsto (fun c : ℝ => (2 * M) * Real.exp (-c * δ)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, mul_zero] using
      (Real.tendsto_exp_atBot.comp harg).const_mul (2 * M)
  filter_upwards [eventually_gt_atTop (0 : ℝ), (tendsto_order.1 htail_lim).2 _ (half_pos hε)]
    with c hc htail_small
  let tail : ℝ → ℝ := (Ici δ).indicator (density c c)
  have hd := integrable_density c hc
  have htail : Integrable tail := hd.integrableOn.integrable_indicator measurableSet_Ici
  have ht₀ := integrable_smoothing_integrand hc hg hM
  have hk := integrable_kernel c hc
  have herr : Integrable (fun s => kernel c c s * (g (t - s) - g t)) := by
    simp only [mul_sub]
    exact ht₀.sub (hk.mul_const (g t))
  have herr_eq :
      (∫ s : ℝ, kernel c c s * (g (t - s) - g t)) = smoothing c g t - g t := by
    simp only [mul_sub, integral_sub ht₀ (hk.mul_const (g t)), integral_mul_const,
      integral_kernel hc, one_mul, smoothing, convolution_def, ContinuousLinearMap.mul_apply']
  have hbound (s : ℝ) :
      ‖kernel c c s * (g (t - s) - g t)‖ ≤ (ε / 2) * density c c s + (2 * M) * tail s := by
    rw [norm_mul, norm_kernel hc.le]
    by_cases hs : s ∈ Ici (0 : ℝ)
    · have hs₀ : 0 ≤ s := hs
      have hd₀ := density_nonneg hc.le c s
      by_cases hsδ : s < δ
      · have hdist : dist (t - s) t < δ := by
          rw [dist_eq_norm, show t - s - t = -s by ring, Real.norm_eq_abs, abs_neg,
            abs_of_nonneg hs₀]
          exact hsδ
        have hsmall : ‖g (t - s) - g t‖ < ε / 2 := by
          simpa only [dist_eq_norm] using hnear hdist
        have hnot : s ∉ Ici δ := not_le.mpr hsδ
        dsimp only [tail]
        rw [indicator_of_notMem hnot, mul_zero, add_zero, mul_comm (ε / 2)]
        exact mul_le_mul_of_nonneg_left hsmall.le hd₀
      · have hmem : s ∈ Ici δ := le_of_not_gt hsδ
        have hlarge : ‖g (t - s) - g t‖ ≤ 2 * M := by
          calc
            _ ≤ ‖g (t - s)‖ + ‖g t‖ := norm_sub_le _ _
            _ ≤ M + M := add_le_add (hM _ (sub_le_self _ hs₀)) (hM _ le_rfl)
            _ = _ := by ring
        dsimp only [tail]
        rw [indicator_of_mem hmem, mul_comm (2 * M)]
        exact (mul_le_mul_of_nonneg_left hlarge hd₀).trans
          (le_add_of_nonneg_left (mul_nonneg (half_pos hε).le hd₀))
    · have hnot : s ∉ Ici δ := fun h => hs (hδ.le.trans h)
      simp [tail, density, hs, hnot]
  rw [dist_eq_norm, ← herr_eq]
  calc
    _ ≤ ∫ s : ℝ, ‖kernel c c s * (g (t - s) - g t)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ s : ℝ, (ε / 2) * density c c s + (2 * M) * tail s :=
      integral_mono herr.norm ((hd.const_mul _).add (htail.const_mul _)) hbound
    _ = ε / 2 + (2 * M) * Real.exp (-c * δ) := by
      rw [integral_add (hd.const_mul _) (htail.const_mul _), integral_const_mul, integral_const_mul,
        integral_density hc, mul_one]
      rw [show (∫ s : ℝ, tail s) = Real.exp (-c * δ) from integral_density_tail hc hδ.le]
    _ < ε := by linarith

private theorem oldLineSmoothing_eq_tilt (c d : ℝ) (g : ℝ → ℂ) (t : ℝ) :
    (kernel c (c + d) ⋆[mul ℂ ℂ] tilt d g) t = tilt d (smoothing c g) t := by
  simp only [tilt, smoothing, convolution_def, ContinuousLinearMap.mul_apply', ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with s
  by_cases hs : s ∈ Ici (0 : ℝ)
  · simp only [kernel, density, indicator_of_mem hs]
    have hphase : -(c + d) * s + -d * (t - s) = -d * t + -c * s := by ring
    have hscalar :
        ((c * Real.exp (-(c + d) * s) : ℝ) : ℂ) * (Real.exp (-d * (t - s)) : ℂ) =
          (Real.exp (-d * t) : ℂ) * ((c * Real.exp (-c * s) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
      congr 1
      calc
        _ = c * (Real.exp (-(c + d) * s) * Real.exp (-d * (t - s))) := by ring
        _ = c * (Real.exp (-d * t) * Real.exp (-c * s)) := by
          rw [← Real.exp_add, ← Real.exp_add, hphase]
        _ = _ := by ring
    simpa only [mul_assoc] using congrArg (fun z : ℂ => z * g (t - s)) hscalar
  · simp [kernel, density, hs]

private theorem smoothed_eq_phase (σ c t a ξ : ℝ) (F : ℂ → ℂ) :
    smoothed σ c t F ((a : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I) =
      (Real.exp ((a - σ) * t) : ℂ) *
        (Complex.exp (((2 * (Real.pi * (ξ * t)) : ℝ) : ℂ) * I) *
          (sectionAt F a ξ * multiplier c (c + (a - σ)) ξ)) := by
  have hphase :
      ((a : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I - σ) * (t : ℂ) =
        (((a - σ) * t : ℝ) : ℂ) + ((2 * (Real.pi * (ξ * t)) : ℝ) : ℂ) * I := by
    push_cast
    ring
  have hden :
      (c : ℂ) + ((a : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I) - σ =
        ((c + (a - σ) : ℝ) : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I := by
    push_cast
    ring
  unfold smoothed sectionAt multiplier
  rw [hphase, hden, Complex.exp_add, ← Complex.ofReal_exp, mul_assoc, mul_assoc]

private theorem integrable_section_mul {σ c a : ℝ} {F : ℂ → ℂ}
    (h : Integrable (fun y : ℝ => smoothed σ c 0 F ((a : ℂ) + y * I))) :
    Integrable (fun ξ => sectionAt F a ξ * multiplier c (c + (a - σ)) ξ) := by
  have hπ : 0 < 2 * Real.pi := by positivity
  have hs : Integrable (fun ξ : ℝ =>
      smoothed σ c 0 F ((a : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I)) :=
    h.comp_mul_left' hπ.ne'
  apply hs.congr
  filter_upwards with ξ
  rw [smoothed_eq_phase]
  simp

private theorem exp_mul_inverse_eq_vertical_integral (σ c t a : ℝ) (F : ℂ → ℂ) :
    (Real.exp ((a - σ) * t) : ℂ) *
      (𝓕⁻ (fun ξ => sectionAt F a ξ * multiplier c (c + (a - σ)) ξ)) t =
        (2 * Real.pi)⁻¹ • ∫ y : ℝ, smoothed σ c t F ((a : ℂ) + y * I) := by
  have hπ : 0 < 2 * Real.pi := by positivity
  rw [Real.fourierInv_eq', ← integral_const_mul, ← abs_of_pos (inv_pos.mpr hπ),
    ← Measure.integral_comp_mul_left]
  apply integral_congr_ae
  filter_upwards with ξ
  simpa only [Real.inner_apply, smul_eq_mul, mul_assoc] using (smoothed_eq_phase σ c t a ξ F).symm

/-- Inversion on the old line and the checked contour shift identify the local
smoothing with the target inverse. The checked inverse estimate bounds its L² norm. -/
theorem smoothing_transfer {σ σ₀ c C p : ℝ} (hσσ₀ : σ < σ₀)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 0 < p) {F : ℂ → ℂ} {g : ℝ → ℂ}
    (hF : ∀ z : ℂ, z.re ∈ Icc σ σ₀ → DifferentiableAt ℂ F z)
    (hdecay : ∀ a ∈ Icc σ σ₀, ∀ y : ℝ,
      ‖F ((a : ℂ) + y * I)‖ ≤ C * (1 + |y|) ^ (-p))
    (hg₀ : Integrable (tilt (σ₀ - σ) g))
    (hfourier : 𝓕 (tilt (σ₀ - σ) g) = sectionAt F σ₀)
    (htarget : MemLp (sectionAt F σ) 2) :
    smoothing c g = 𝓕⁻ (fun ξ => sectionAt F σ ξ * targetMultiplier c ξ) ∧
      MemLp (smoothing c g) 2 ∧ eLpNorm (smoothing c g) 2 ≤ eLpNorm (sectionAt F σ) 2 := by
  have hsections := (smoothed_vertical_shift hσσ₀ hc hC hp 0 hF hdecay).1
  have holdFreq := integrable_section_mul (hsections σ₀ ⟨hσσ₀.le, le_rfl⟩)
  have htargetFreq : Integrable (fun ξ => sectionAt F σ ξ * targetMultiplier c ξ) := by
    simpa only [sub_self, add_zero, multiplier, targetMultiplier] using
      integrable_section_mul (hsections σ ⟨le_rfl, hσσ₀.le⟩)
  have ha : 0 < c + (σ₀ - σ) := by linarith
  have hold := oldLineSmoothing_eq_fourierInv (c := c) hc.le ha hg₀ (by
    rw [hfourier]
    exact holdFreq)
  rw [hfourier] at hold
  have heq : smoothing c g = 𝓕⁻ (fun ξ => sectionAt F σ ξ * targetMultiplier c ξ) := by
    funext t
    have htilt :
        (Real.exp (-(σ₀ - σ) * t) : ℂ) * smoothing c g t =
          (𝓕⁻ (fun ξ => sectionAt F σ₀ ξ * multiplier c (c + (σ₀ - σ)) ξ)) t :=
      (oldLineSmoothing_eq_tilt c (σ₀ - σ) g t).symm.trans (congrFun hold t)
    calc
      _ = (Real.exp ((σ₀ - σ) * t) : ℂ) *
          ((Real.exp (-(σ₀ - σ) * t) : ℂ) * smoothing c g t) := by
        rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add,
          show (σ₀ - σ) * t + -(σ₀ - σ) * t = 0 by ring, Real.exp_zero, Complex.ofReal_one,
          one_mul]
      _ = (2 * Real.pi)⁻¹ • ∫ y : ℝ, smoothed σ c t F ((σ₀ : ℂ) + y * I) := by
        rw [htilt, exp_mul_inverse_eq_vertical_integral]
      _ = (2 * Real.pi)⁻¹ • ∫ y : ℝ, smoothed σ c t F ((σ : ℂ) + y * I) := by
        rw [(smoothed_vertical_shift hσσ₀ hc hC hp t hF hdecay).2.2.2]
      _ = _ := (targetInverse_eq_vertical_integral σ c t F).symm
  refine ⟨heq, ?_⟩
  rw [heq]
  exact targetInverse_memLp hc htarget htargetFreq

/-- A known exponentially tilted Fourier section transfers L² membership to the
left-hand line for a causal, locally bounded function continuous almost everywhere. -/
theorem memLp_of_strip_transfer {σ σ₀ C p : ℝ} (hσσ₀ : σ < σ₀)
    (hC : 0 ≤ C) (hp : 0 < p) {F : ℂ → ℂ} {g : ℝ → ℂ}
    (hF : ∀ z : ℂ, z.re ∈ Icc σ σ₀ → DifferentiableAt ℂ F z)
    (hdecay : ∀ a ∈ Icc σ σ₀, ∀ y : ℝ,
      ‖F ((a : ℂ) + y * I)‖ ≤ C * (1 + |y|) ^ (-p))
    (hg : Measurable g) (hcont : ∀ᵐ t ∂(volume : Measure ℝ), ContinuousAt g t)
    (hzero : ∀ t < 0, g t = 0)
    (hbounded : ∀ T : ℝ, ∃ M : ℝ, ∀ t ∈ Icc 0 T, ‖g t‖ ≤ M)
    (hg₀ : Integrable (tilt (σ₀ - σ) g))
    (hfourier : 𝓕 (tilt (σ₀ - σ) g) = sectionAt F σ₀)
    (htarget : MemLp (sectionAt F σ) 2) :
    MemLp g 2 := by
  let rates : ℕ → ℝ := fun n => (n : ℝ) + 1
  have hrates : Tendsto rates atTop atTop :=
    tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
  have hrates_pos (n : ℕ) : 0 < rates n := by
    dsimp [rates]
    positivity
  have huniform (n : ℕ) : MemLp (smoothing (rates n) g) 2 ∧
      eLpNorm (smoothing (rates n) g) 2 ≤ eLpNorm (sectionAt F σ) 2 :=
    (smoothing_transfer hσσ₀ (hrates_pos n) hC hp hF hdecay
      hg₀ hfourier htarget).2
  have hlimit : ∀ᵐ t ∂(volume : Measure ℝ),
      Tendsto (fun n => smoothing (rates n) g t) atTop (𝓝 (g t)) := by
    filter_upwards [hcont] with t ht
    obtain ⟨M, hM⟩ := hbounded t
    have hpast : ∀ x ≤ t, ‖g x‖ ≤ max M 0 := by
      intro x hx
      by_cases hx₀ : x < 0
      · rw [hzero x hx₀, norm_zero]
        exact le_max_right _ _
      · exact (hM x ⟨le_of_not_gt hx₀, hx⟩).trans (le_max_left _ _)
    exact (smoothing_tendsto_atTop hg ht hpast).comp hrates
  have hbound : eLpNorm g 2 ≤ eLpNorm (sectionAt F σ) 2 :=
    Lp.eLpNorm_le_of_ae_tendsto
      (u := (atTop : Filter ℕ)) (f := fun n => smoothing (rates n) g)
      (p := 2) (Eventually.of_forall fun n => (huniform n).2)
      (fun n => (huniform n).1.aestronglyMeasurable) hg.aestronglyMeasurable hlimit
  exact hbound.trans_lt htarget.eLpNorm_lt_top

end

end D5.S3.Analytic.Laplace.CausalExponentialStripTransfer
