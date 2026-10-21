/- GID: D5/S3/Weil/ZetaGamma/FormCore/Mollifier
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaGamma/FormCore/Mollifier
   mirror-E: none(waiver:analytic-Gamma-form-core)
   anchors: []
   utility: none
   digest: Bump convolution converges in the actual Gamma graph size. -/


import D5.S3.Weil.PrimePoleTerms
import D5.S3.Weil.TestFunctions.ConvolutionSquarePositivity
import D5.S3.Weil.ZetaBridge.ClassicExplicitFormula
import D5.S3.Weil.ZetaCore.ExplicitFormulaBridge
import D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition
import D5.S3.Weil.ZetaGamma.FormCore.DirectionalEnergy
import D5.S3.Weil.ZetaGamma.FormCore.ExteriorBudget
import D5.S3.Weil.ZetaGamma.FormCore.LineFourier
import D5.S3.Weil.ZetaGamma.GammaMu
import D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

noncomputable section
open MeasureTheory Set Filter
open MeasureTheory.Measure
open D5.S3.Weil.Convention
open D5.S3.Weil.FourierLaplace
open D5.S3.Weil.PrimePoleTerms
open D5.S3.Weil.TestFunctions
open D5.S3.Weil.TestFunctions.ConvolutionSquarePositivity
open D5.S3.Weil.ZetaBridge.ClassicExplicitFormula
open scoped ComplexConjugate FourierTransform ENNReal Topology ContDiff Classical
open scoped SchwartzMap NNReal Convolution Pointwise

namespace D5.S3.Weil.ZetaGamma.FormCore

open MeasureTheory Set Filter
open D5.S3.Weil.ZetaGamma.FormCore.LineFourier
open scoped ENNReal Topology FourierTransform Convolution Pointwise

def coreL2Mass (G : ℝ → ℂ) : ℝ≥0∞ := ∫⁻ x : ℝ, ‖G x‖ₑ ^ 2

private def coreMollify (φ : ContDiffBump (0 : ℝ)) (G : ℝ → ℂ) : ℝ → ℂ :=
  convolution (φ.normed volume) G (ContinuousLinearMap.lsmul ℝ ℝ) volume

private def coreComplexKernel (φ : ContDiffBump (0 : ℝ)) (x : ℝ) : ℂ :=
  (φ.normed volume x : ℂ)

private theorem coreComplexKernel_integrable (φ : ContDiffBump (0 : ℝ)) :
    Integrable (coreComplexKernel φ) :=
  Complex.ofRealCLM.integrable_comp φ.integrable_normed

private theorem coreMollify_eq_complex_convolution
    (φ : ContDiffBump (0 : ℝ)) (G : ℝ → ℂ) :
    coreMollify φ G =
      convolution (coreComplexKernel φ) G (ContinuousLinearMap.mul ℂ ℂ) volume := by
  funext x
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    simp only [coreComplexKernel, ContinuousLinearMap.lsmul_apply,
      ContinuousLinearMap.mul_apply', Complex.real_smul]

private theorem coreMollify_integrable
    (φ : ContDiffBump (0 : ℝ)) (G : ℝ → ℂ) (hG : Integrable G) :
    Integrable (coreMollify φ G) :=
  φ.integrable_normed.integrable_convolution (ContinuousLinearMap.lsmul ℝ ℝ) hG

private theorem coreMollify_contDiff
    (φ : ContDiffBump (0 : ℝ)) (G : ℝ → ℂ) (hG2 : MemLp G 2 volume) :
    ContDiff ℝ ∞ (coreMollify φ G) :=
  φ.hasCompactSupport_normed.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    φ.contDiff_normed (hG2.locallyIntegrable (by norm_num))

private theorem coreMollify_hasCompactSupport
    (φ : ContDiffBump (0 : ℝ)) (G : ℝ → ℂ) (hGc : HasCompactSupport G) :
    HasCompactSupport (coreMollify φ G) :=
  φ.hasCompactSupport_normed.convolution (ContinuousLinearMap.lsmul ℝ ℝ) hGc

private theorem coreMollify_memLp
    (φ : ContDiffBump (0 : ℝ)) (G : ℝ → ℂ)
    (hG2 : MemLp G 2 volume) (hGc : HasCompactSupport G) :
    MemLp (coreMollify φ G) 2 volume :=
  (coreMollify_contDiff φ G hG2).continuous.memLp_of_hasCompactSupport
    (coreMollify_hasCompactSupport φ G hGc)

private theorem core_integrable_of_memLp_compact
    (G : ℝ → ℂ) (hG2 : MemLp G 2 volume) (hGc : HasCompactSupport G) :
    Integrable G :=
  (integrableOn_iff_integrable_of_support_subset (subset_tsupport G)).mp
    ((hG2.locallyIntegrable (by norm_num)).integrableOn_isCompact hGc)

private theorem coreMollify_tsupport_subset
    (φ : ContDiffBump (0 : ℝ)) (G : ℝ → ℂ) (l r : ℝ)
    (hGsupport : tsupport G ⊆ Icc l r) :
    tsupport (coreMollify φ G) ⊆ Icc (l - φ.rOut) (r + φ.rOut) := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  obtain ⟨u, hu, v, hv, rfl⟩ :=
    support_convolution_subset (ContinuousLinearMap.lsmul ℝ ℝ) hx
  rw [φ.support_normed_eq] at hu
  have huabs : |u| < φ.rOut := by
    simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using hu
  have hvI := hGsupport (subset_tsupport G hv)
  exact ⟨by linarith [(abs_lt.mp huabs).1, hvI.1],
    by linarith [(abs_lt.mp huabs).2, hvI.2]⟩

private theorem coreMollify_tsupport_inside
    (φ : ContDiffBump (0 : ℝ)) (G : ℝ → ℂ) (a η : ℝ)
    (hmargin : φ.rOut < η) (hGsupport : tsupport G ⊆ Icc (-a + η) (a - η)) :
    tsupport (coreMollify φ G) ⊆ Ioo (-a) a := by
  intro x hx
  have h := coreMollify_tsupport_subset φ G (-a + η) (a - η) hGsupport hx
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

private theorem coreComplexKernel_fourier_norm_le_one
    (φ : ContDiffBump (0 : ℝ)) (ξ : ℝ) : ‖𝓕 (coreComplexKernel φ) ξ‖ ≤ 1 := by
  calc
    _ ≤ ∫ x : ℝ, ‖coreComplexKernel φ x‖ :=
      VectorFourier.norm_fourierIntegral_le_integral_norm
        Real.fourierChar volume (innerₗ ℝ) (coreComplexKernel φ) ξ
    _ = ∫ x : ℝ, φ.normed volume x := by
      congr 1
      funext x
      exact Complex.norm_of_nonneg (φ.nonneg_normed x)
    _ = 1 := φ.integral_normed

private theorem coreComplexKernel_fourier_gap_sq_le_four
    (φ : ContDiffBump (0 : ℝ)) (ξ : ℝ) :
    ‖𝓕 (coreComplexKernel φ) ξ - 1‖ₑ ^ 2 ≤ 4 := by
  have hn : ‖𝓕 (coreComplexKernel φ) ξ - 1‖ ≤ 2 := by
    calc
      _ ≤ ‖𝓕 (coreComplexKernel φ) ξ‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ 2 := by
        calc
          _ ≤ 1 + ‖(1 : ℂ)‖ :=
            add_le_add (coreComplexKernel_fourier_norm_le_one φ ξ) (le_refl _)
          _ = 2 := by norm_num
  have he : ‖𝓕 (coreComplexKernel φ) ξ - 1‖ₑ ≤ (2 : ℝ≥0∞) := by
    simpa only [ofReal_norm, ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal hn
  calc
    _ ≤ (2 : ℝ≥0∞) ^ 2 := pow_le_pow_left' he 2
    _ = 4 := by norm_num

private theorem coreComplexKernel_fourier_tendsto_one
    {ι : Type*} {l : Filter ι} (φ : ι → ContDiffBump (0 : ℝ))
    (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0)) (ξ : ℝ) :
    Tendsto (fun i => 𝓕 (coreComplexKernel (φ i)) ξ) l (𝓝 1) := by
  let character : ℝ → ℂ := fun x => (Real.fourierChar (x * ξ) : ℂ)
  have hchar : Continuous character := by
    dsimp only [character]
    fun_prop
  have heq (i : ι) :
      ((φ i).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] character) 0 =
        𝓕 (coreComplexKernel (φ i)) ξ := by
    simp only [convolution_def, Real.fourier_eq, Real.inner_apply]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      simp [character, coreComplexKernel, Circle.smul_def, smul_eq_mul,
        Complex.real_smul, mul_comm]
  have hconv :=
    ContDiffBump.convolution_tendsto_right_of_continuous (μ := volume) hφ hchar 0
  have hzero : character 0 = (1 : ℂ) := by
    simp [character, Real.fourierChar_apply]
  rw [hzero] at hconv
  apply Tendsto.congr' (Filter.Eventually.of_forall heq) hconv

private theorem coreFourierMultiplier_lintegral_tendsto_zero
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (φ : ι → ContDiffBump (0 : ℝ))
    (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0))
    (B : ℝ → ℝ≥0∞) (hB : Measurable B)
    (hBfin : (∫⁻ z : ℝ, B z) < (⊤ : ℝ≥0∞)) :
    Tendsto (fun i => ∫⁻ z : ℝ,
      ‖angularFourier (coreComplexKernel (φ i)) z - 1‖ₑ ^ 2 * B z) l (𝓝 0) := by
  have hm (i : ι) : Measurable (fun z : ℝ =>
      ‖angularFourier (coreComplexKernel (φ i)) z - 1‖ₑ ^ 2 * B z) := by
    have hc : Continuous (angularFourier (coreComplexKernel (φ i))) :=
      (continuous_raw_fourier (coreComplexKernel_integrable (φ i))).comp
        (continuous_id.div_const (2 * Real.pi))
    exact ((hc.sub continuous_const).measurable.enorm.pow_const 2).mul hB
  have hbound (i : ι) (z : ℝ) :
      ‖angularFourier (coreComplexKernel (φ i)) z - 1‖ₑ ^ 2 * B z ≤ 4 * B z := by
    gcongr
    exact coreComplexKernel_fourier_gap_sq_le_four (φ i) (z / (2 * Real.pi))
  have hfin : (∫⁻ z : ℝ, 4 * B z) ≠ (⊤ : ℝ≥0∞) := by
    rw [lintegral_const_mul' _ _ (by norm_num)]
    exact (ENNReal.mul_lt_top (by norm_num) hBfin).ne
  have hlim : ∀ᵐ z : ℝ, Tendsto (fun i =>
      ‖angularFourier (coreComplexKernel (φ i)) z - 1‖ₑ ^ 2 * B z) l (𝓝 0) := by
    filter_upwards [ae_lt_top hB hBfin.ne] with z hz
    have ht : Tendsto (fun i =>
        ‖angularFourier (coreComplexKernel (φ i)) z - 1‖ₑ ^ 2) l (𝓝 0) := by
      have htc := (coreComplexKernel_fourier_tendsto_one φ hφ
        (z / (2 * Real.pi))).sub
        (tendsto_const_nhds : Tendsto (fun _ : ι => (1 : ℂ)) l (𝓝 1))
      have htc' : Tendsto (fun i =>
          𝓕 (coreComplexKernel (φ i)) (z / (2 * Real.pi)) - 1) l
          (𝓝 (0 : ℂ)) := by
        simpa only [sub_self] using htc
      have hteRaw : Tendsto (fun i =>
          ‖𝓕 (coreComplexKernel (φ i)) (z / (2 * Real.pi)) - 1‖ₑ) l
          (𝓝 (0 : ℝ≥0∞)) := by
        simpa only [Function.comp_def, enorm_zero] using
          ((continuous_enorm : Continuous (fun w : ℂ => ‖w‖ₑ)).tendsto 0).comp htc'
      have hte : Tendsto (fun i =>
          ‖angularFourier (coreComplexKernel (φ i)) z - 1‖ₑ) l
          (𝓝 (0 : ℝ≥0∞)) := by
        simpa only [angularFourier] using hteRaw
      simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
        (ENNReal.Tendsto.pow (n := 2) hte)
    simpa only [zero_mul] using
      (ENNReal.Tendsto.mul_const ht (Or.inr hz.ne) :
        Tendsto (fun i =>
          ‖angularFourier (coreComplexKernel (φ i)) z - 1‖ₑ ^ 2 * B z) l
          (𝓝 ((0 : ℝ≥0∞) * B z)))
  simpa only [lintegral_zero] using
    tendsto_lintegral_filter_of_dominated_convergence (fun z => 4 * B z)
      (Eventually.of_forall hm)
      (Eventually.of_forall fun i => Eventually.of_forall (hbound i)) hfin hlim

private theorem coreMollify_angular_fourier_error
    (φ : ContDiffBump (0 : ℝ)) (G : ℝ → ℂ) (hG1 : Integrable G) (z : ℝ) :
    angularFourier (fun x => coreMollify φ G x - G x) z =
      (angularFourier (coreComplexKernel φ) z - 1) * angularFourier G z := by
  unfold angularFourier
  rw [raw_fourier_sub (coreMollify_integrable φ G hG1) hG1,
    coreMollify_eq_complex_convolution,
    Real.fourier_mul_convolution_eq (coreComplexKernel_integrable φ) hG1]
  ring

private theorem core_actual_spectral_weight_measurable :
    Measurable (fun z : ℝ => ENNReal.ofReal (actualIncrement z)) := by
  have hm : Measurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal (actualDensity p.2) *
        ENNReal.ofReal (cyclicGap (p.1 / (2 * Real.pi)) p.2)) := by
    unfold actualDensity
      D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.archimedeanJumpDensity cyclicGap
    fun_prop
  have heq (z : ℝ) : (∫⁻ s : ℝ in Ioi 0,
      ENNReal.ofReal (actualDensity s) *
        ENNReal.ofReal (cyclicGap (z / (2 * Real.pi)) s)) =
      ENNReal.ofReal (actualIncrement z) := by
    rw [actual_line_spectralWeight]
    congr 2
    field_simp [Real.pi_ne_zero]
  simpa only [heq] using
    (hm.lintegral_prod_right' (ν := volume.restrict (Ioi (0 : ℝ))))

private theorem core_actual_energy_eq_angular
    (G : ℝ → ℂ) (hG : Measurable G) (hG1 : Integrable G) (hG2 : MemLp G 2 volume) :
    directionalEnergy actualGammaExitMeasure G =
      ENNReal.ofReal (1 / (2 * Real.pi)) *
        ∫⁻ z : ℝ, ENNReal.ofReal (actualIncrement z) * ‖angularFourier G z‖ₑ ^ 2 := by
  have hscale : Measurable (fun s : ℝ => ∫⁻ x : ℝ, ‖G x - G (x - s)‖ₑ ^ 2) := by
    have hm : Measurable (fun p : ℝ × ℝ => ‖G p.2 - G (p.2 - p.1)‖ₑ ^ 2) := by
      fun_prop
    exact hm.lintegral_prod_right'
  have hρ : Measurable (fun s => ENNReal.ofReal (actualDensity s)) := by
    unfold actualDensity
      D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.archimedeanJumpDensity
    fun_prop
  have hgap (s : ℝ) : (∫⁻ x : ℝ, ‖G x - G (x - s)‖ₑ ^ 2) =
      ENNReal.ofReal (lineGapMass G s) := by
    have hg2 : MemLp (fun x : ℝ => G x - G (x - s)) 2 volume :=
      hG2.sub (hG2.comp_measurePreserving (measurePreserving_sub_right volume s))
    have hsq := hg2.integrable_norm_pow (p := 2) (by norm_num)
    rw [lineGapMass, ofReal_integral_eq_lintegral_ofReal hsq
      (Eventually.of_forall fun x => sq_nonneg _)]
    apply lintegral_congr_ae
    exact Eventually.of_forall fun x => by
      simpa only [ofReal_norm] using
        (ENNReal.ofReal_pow (norm_nonneg (G x - G (x - s))) 2).symm
  calc
    _ = ∫⁻ s : ℝ in Ioi 0, ENNReal.ofReal (actualDensity s) *
        (∫⁻ x : ℝ, ‖G x - G (x - s)‖ₑ ^ 2) := by
      unfold directionalEnergy actualGammaExitMeasure
      exact lintegral_withDensity_eq_lintegral_mul _ hρ hscale
    _ = ∫⁻ s : ℝ in Ioi 0,
        ENNReal.ofReal (actualDensity s) * ENNReal.ofReal (lineGapMass G s) := by
      apply lintegral_congr_ae
      exact Eventually.of_forall fun s => by dsimp only; rw [hgap]
    _ = _ := actual_gamma_whole_line_energy_eq_angular_integral hG1 hG2

private theorem coreMollify_mass_and_actual_energy_tendsto_zero
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (φ : ι → ContDiffBump (0 : ℝ))
    (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0))
    (G : ℝ → ℂ) (hG : Measurable G) (hG2 : MemLp G 2 volume)
    (hGc : HasCompactSupport G)
    (hGE : directionalEnergy actualGammaExitMeasure G < (⊤ : ℝ≥0∞)) :
    Tendsto (fun i => coreL2Mass (fun x => coreMollify (φ i) G x - G x) +
      directionalEnergy actualGammaExitMeasure (fun x => coreMollify (φ i) G x - G x))
      l (𝓝 0) := by
  let c : ℝ≥0∞ := ENNReal.ofReal (1 / (2 * Real.pi))
  have hc0 : c ≠ 0 := by dsimp only [c]; positivity
  have hcfin : c ≠ (⊤ : ℝ≥0∞) := ENNReal.ofReal_ne_top
  have hG1 : Integrable G := core_integrable_of_memLp_compact G hG2 hGc
  have hGhat : Measurable (angularFourier G) :=
    ((continuous_raw_fourier hG1).comp (continuous_id.div_const (2 * Real.pi))).measurable
  have hmassfin : (∫⁻ z : ℝ, ‖angularFourier G z‖ₑ ^ 2) < (⊤ : ℝ≥0∞) := by
    apply ENNReal.lt_top_of_mul_ne_top_right (a := c)
      (b := ∫⁻ z : ℝ, ‖angularFourier G z‖ₑ ^ 2) _ hc0
    change ENNReal.ofReal (1 / (2 * Real.pi)) *
      (∫⁻ z : ℝ, ‖angularFourier G z‖ₑ ^ 2) ≠ (⊤ : ℝ≥0∞)
    rw [← angular_extended_plancherel hG1 hG2,
      squared_mass_eq_eLpNorm _ hG2.aestronglyMeasurable]
    exact (ENNReal.pow_lt_top hG2.eLpNorm_lt_top).ne
  have henergyfin : (∫⁻ z : ℝ,
      ENNReal.ofReal (actualIncrement z) * ‖angularFourier G z‖ₑ ^ 2) < (⊤ : ℝ≥0∞) := by
    apply ENNReal.lt_top_of_mul_ne_top_right (a := c) _ hc0
    change ENNReal.ofReal (1 / (2 * Real.pi)) *
      (∫⁻ z : ℝ, ENNReal.ofReal (actualIncrement z) * ‖angularFourier G z‖ₑ ^ 2)
        ≠ (⊤ : ℝ≥0∞)
    rw [← core_actual_energy_eq_angular G hG hG1 hG2]
    exact hGE.ne
  have hM := coreFourierMultiplier_lintegral_tendsto_zero φ hφ
    (fun z => ‖angularFourier G z‖ₑ ^ 2) (hGhat.enorm.pow_const 2) hmassfin
  have hE := coreFourierMultiplier_lintegral_tendsto_zero φ hφ
    (fun z => ENNReal.ofReal (actualIncrement z) * ‖angularFourier G z‖ₑ ^ 2)
    (core_actual_spectral_weight_measurable.mul (hGhat.enorm.pow_const 2)) henergyfin
  have hscaled := ENNReal.Tendsto.const_mul (hM.add hE) (Or.inr hcfin)
  have heq (i : ι) : coreL2Mass (fun x => coreMollify (φ i) G x - G x) +
      directionalEnergy actualGammaExitMeasure (fun x => coreMollify (φ i) G x - G x) =
      c * ((∫⁻ z : ℝ,
        ‖angularFourier (coreComplexKernel (φ i)) z - 1‖ₑ ^ 2 *
          ‖angularFourier G z‖ₑ ^ 2) +
        ∫⁻ z : ℝ, ‖angularFourier (coreComplexKernel (φ i)) z - 1‖ₑ ^ 2 *
          (ENNReal.ofReal (actualIncrement z) * ‖angularFourier G z‖ₑ ^ 2)) := by
    have hf1 := (coreMollify_integrable (φ i) G hG1).sub hG1
    have hf2 := (coreMollify_memLp (φ i) G hG2 hGc).sub hG2
    have hfm := (coreMollify_contDiff (φ i) G hG2).continuous.measurable.sub hG
    change (∫⁻ x : ℝ, ‖(coreMollify (φ i) G - G) x‖ₑ ^ 2) +
      directionalEnergy actualGammaExitMeasure (coreMollify (φ i) G - G) = _
    rw [angular_extended_plancherel hf1 hf2,
      core_actual_energy_eq_angular _ hfm hf1 hf2]
    change c * _ + c * _ = c * _
    rw [← mul_add]
    apply congrArg (fun t : ℝ≥0∞ => c * t)
    apply congrArg₂ (fun u v : ℝ≥0∞ => u + v)
    · apply lintegral_congr_ae
      exact Eventually.of_forall fun z => by
        dsimp only
        change ‖angularFourier
          (fun x => coreMollify (φ i) G x - G x) z‖ₑ ^ 2 = _
        rw [coreMollify_angular_fourier_error (φ i) G hG1 z, enorm_mul, mul_pow]
    · apply lintegral_congr_ae
      exact Eventually.of_forall fun z => by
        dsimp only
        change ENNReal.ofReal (actualIncrement z) *
          ‖angularFourier (fun x => coreMollify (φ i) G x - G x) z‖ₑ ^ 2 = _
        rw [coreMollify_angular_fourier_error (φ i) G hG1 z, enorm_mul, mul_pow]
        ring
  simpa only [heq, zero_add, mul_zero] using hscaled

private theorem coreMollify_eventually_tsupport_inside
    {ι : Type*} {l : Filter ι} (φ : ι → ContDiffBump (0 : ℝ))
    (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0))
    (G : ℝ → ℂ) (a η : ℝ) (hη : 0 < η)
    (hGsupport : tsupport G ⊆ Icc (-a + η) (a - η)) :
    ∀ᶠ i in l, tsupport (coreMollify (φ i) G) ⊆ Ioo (-a) a := by
  filter_upwards [hφ.eventually (gt_mem_nhds hη)] with i hi
  exact coreMollify_tsupport_inside (φ i) G a η hi hGsupport

private def coreBumpSequence (n : ℕ) : ContDiffBump (0 : ℝ) where
  rIn := (1 / ((n : ℝ) + 1)) / 2
  rOut := 1 / ((n : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have hp : 0 < (1 / ((n : ℝ) + 1)) := by positivity
    linarith

private theorem coreBumpSequence_rOut_tendsto_zero :
    Tendsto (fun n : ℕ => (coreBumpSequence n).rOut) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

theorem exists_smooth_actual_gamma_approximation_of_inward_support
    (G : ℝ → ℂ) (hG : Measurable G) (hG2 : MemLp G 2 volume)
    (hGc : HasCompactSupport G)
    (hGE : directionalEnergy actualGammaExitMeasure G < (⊤ : ℝ≥0∞))
    (a η : ℝ) (hη : 0 < η) (hGsupport : tsupport G ⊆ Icc (-a + η) (a - η))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ H : ℝ → ℂ, ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧
      tsupport H ⊆ Ioo (-a) a ∧
      coreL2Mass (fun x => H x - G x) +
        directionalEnergy actualGammaExitMeasure (fun x => H x - G x) <
          ENNReal.ofReal ε := by
  have hconv := coreMollify_mass_and_actual_energy_tendsto_zero
    coreBumpSequence coreBumpSequence_rOut_tendsto_zero G hG hG2 hGc hGE
  have hs := coreMollify_eventually_tsupport_inside
    coreBumpSequence coreBumpSequence_rOut_tendsto_zero G a η hη hGsupport
  have he : ∀ᶠ n : ℕ in atTop,
      coreL2Mass (fun x => coreMollify (coreBumpSequence n) G x - G x) +
        directionalEnergy actualGammaExitMeasure
          (fun x => coreMollify (coreBumpSequence n) G x - G x) < ENNReal.ofReal ε :=
    hconv.eventually (gt_mem_nhds (by positivity : (0 : ℝ≥0∞) < ENNReal.ofReal ε))
  obtain ⟨n, hn, he⟩ := (hs.and he).exists
  exact ⟨coreMollify (coreBumpSequence n) G,
    coreMollify_contDiff _ G hG2, coreMollify_hasCompactSupport _ G hGc, hn, he⟩

end D5.S3.Weil.ZetaGamma.FormCore
