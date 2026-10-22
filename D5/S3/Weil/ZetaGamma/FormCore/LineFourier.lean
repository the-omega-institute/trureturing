/- GID: D5/S3/Weil/ZetaGamma/FormCore/LineFourier
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaGamma/FormCore/LineFourier
   mirror-E: none(waiver:analytic-Gamma-form-core)
   anchors: []
   utility: none
   digest: Raw whole-line Fourier bridge and actual-Gamma spectral energy. -/


import D5.S3.Weil.PrimePoleTerms
import D5.S3.Weil.TestFunctions.ConvolutionSquarePositivity
import D5.S3.Weil.ZetaBridge.ClassicExplicitFormula
import D5.S3.Weil.ZetaCore.ExplicitFormulaBridge
import D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition
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

namespace D5.S3.Weil.ZetaGamma.FormCore.LineFourier

theorem continuous_raw_fourier {f : ℝ → ℂ} (hf : Integrable f) :
    Continuous (𝓕 f) := by
  exact VectorFourier.fourierIntegral_continuous
    Real.continuous_fourierChar continuous_inner hf

private theorem raw_fourier_test {f : ℝ → ℂ} (hf : Integrable f)
    (ψ : SchwartzMap ℝ ℂ) :
    (∫ ξ : ℝ, ψ ξ • 𝓕 f ξ) = ∫ x : ℝ, 𝓕 ψ x • f x := by
  simpa [SchwartzMap.fourier_coe, Real.fourier_eq, VectorFourier.fourierIntegral,
    Real.inner_apply, smul_eq_mul, mul_comm] using!
    VectorFourier.integral_bilin_fourierIntegral_eq_flip
      (f := f) (g := (ψ : ℝ → ℂ)) (.mul ℂ ℂ) (L := innerₗ ℝ)
      (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
      Real.continuous_fourierChar continuous_inner hf (ψ.integrable (μ := volume))

private theorem raw_fourier_ae_eq_L2 {f : ℝ → ℂ}
    (hf₁ : Integrable f) (hf₂ : MemLp f 2) :
    (𝓕 f : ℝ → ℂ) =ᵐ[volume]
      (𝓕 (hf₂.toLp f) : Lp ℂ 2 volume) := by
  let F : Lp ℂ 2 volume := 𝓕 (hf₂.toLp f)
  apply ae_eq_of_integral_contDiff_smul_eq
    (continuous_raw_fourier hf₁).locallyIntegrable
    ((Lp.memLp F).locallyIntegrable (by norm_num))
  intro g hg hgc
  have hg₁ : HasCompactSupport (Complex.ofRealCLM ∘ g) := hgc.comp_left rfl
  have hg₂ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Complex.ofRealCLM ∘ g) :=
    Complex.ofRealCLM.contDiff.comp hg
  let ψ : SchwartzMap ℝ ℂ := hg₁.toSchwartzMap hg₂
  have hdist := congrArg (fun T : TemperedDistribution ℝ ℂ => T ψ)
    (Lp.fourier_toTemperedDistribution_eq (hf₂.toLp f))
  simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply] at hdist
  calc
    (∫ ξ : ℝ, g ξ • 𝓕 f ξ) = ∫ ξ : ℝ, ψ ξ • 𝓕 f ξ := by
      simp [ψ, Function.comp_apply]
    _ = ∫ x : ℝ, 𝓕 ψ x • f x := raw_fourier_test hf₁ ψ
    _ = ∫ x : ℝ, 𝓕 ψ x • (hf₂.toLp f) x := by
      apply integral_congr_ae
      filter_upwards [hf₂.coeFn_toLp] with x hx
      rw [hx]
    _ = ∫ ξ : ℝ, ψ ξ • F ξ := hdist
    _ = ∫ ξ : ℝ, g ξ • F ξ := by
      simp [ψ, Function.comp_apply]

private theorem raw_fourier_eLpNorm_eq {f : ℝ → ℂ}
    (hf₁ : Integrable f) (hf₂ : MemLp f 2) :
    eLpNorm (𝓕 f) 2 volume = eLpNorm f 2 volume := by
  calc
    _ = eLpNorm (𝓕 (hf₂.toLp f) : Lp ℂ 2 volume) 2 volume :=
      eLpNorm_congr_ae (raw_fourier_ae_eq_L2 hf₁ hf₂)
    _ = ‖𝓕 (hf₂.toLp f)‖ₑ := (Lp.enorm_def _).symm
    _ = ‖hf₂.toLp f‖ₑ := (Lp.fourierTransformₗᵢ ℝ ℂ).enorm_map _
    _ = _ := Lp.enorm_toLp hf₂

theorem squared_mass_eq_eLpNorm (f : ℝ → ℂ)
    (hf : AEStronglyMeasurable f volume) :
    (∫⁻ x : ℝ, ‖f x‖ₑ ^ 2) = eLpNorm f 2 volume ^ 2 := by
  simpa using (eLpNorm_nnreal_pow_eq_lintegral
    (f := f) (μ := volume) (p := (2 : ℝ≥0)) (by norm_num) hf).symm

private theorem raw_fourier_extended_plancherel {f : ℝ → ℂ}
    (hf₁ : Integrable f) (hf₂ : MemLp f 2) :
    (∫⁻ ξ : ℝ, ‖𝓕 f ξ‖ₑ ^ 2) = ∫⁻ x : ℝ, ‖f x‖ₑ ^ 2 := by
  rw [squared_mass_eq_eLpNorm (𝓕 f)
      ((continuous_raw_fourier hf₁).aestronglyMeasurable),
    squared_mass_eq_eLpNorm f hf₂.aestronglyMeasurable,
    raw_fourier_eLpNorm_eq hf₁ hf₂]

private theorem lintegral_dilate (H : ℝ → ℝ≥0∞) {c : ℝ} (hc : c ≠ 0) :
    (∫⁻ ξ : ℝ, H (c * ξ)) =
      ENNReal.ofReal |c⁻¹| * ∫⁻ t : ℝ, H t := by
  calc
    _ = ∫⁻ t : ℝ, H t ∂Measure.map (c * ·) volume :=
      ((Homeomorph.mulLeft₀ c hc).toMeasurableEquiv.measurableEmbedding.lintegral_map H).symm
    _ = _ := by
      rw [Real.map_volume_mul_left hc, lintegral_smul_measure]
      rfl

def angularFourier (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  𝓕 f (t / (2 * Real.pi))

private theorem angularFourier_eq_integral (f : ℝ → ℂ) (t : ℝ) :
    angularFourier f t =
      ∫ x : ℝ, Complex.exp ((-(t * x) : ℝ) * Complex.I) * f x := by
  unfold angularFourier
  rw [Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards with x
  have h : -2 * Real.pi * x * (t / (2 * Real.pi)) = -(t * x) := by
    field_simp [Real.pi_ne_zero]
    <;> ring
  rw [h, smul_eq_mul]

theorem angular_extended_plancherel {f : ℝ → ℂ}
    (hf₁ : Integrable f) (hf₂ : MemLp f 2) :
    (∫⁻ x : ℝ, ‖f x‖ₑ ^ 2) =
      ENNReal.ofReal (1 / (2 * Real.pi)) *
        ∫⁻ t : ℝ, ‖angularFourier f t‖ₑ ^ 2 := by
  have hc : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hpoint (ξ : ℝ) : angularFourier f ((2 * Real.pi) * ξ) = 𝓕 f ξ := by
    rw [angularFourier_eq_integral, Real.fourier_real_eq_integral_exp_smul]
    apply integral_congr_ae
    filter_upwards with x
    have harg : -2 * Real.pi * x * ξ = -(((2 * Real.pi) * ξ) * x) := by ring
    rw [harg, smul_eq_mul]
  calc
    _ = ∫⁻ ξ : ℝ, ‖𝓕 f ξ‖ₑ ^ 2 :=
      (raw_fourier_extended_plancherel hf₁ hf₂).symm
    _ = ∫⁻ ξ : ℝ, ‖angularFourier f ((2 * Real.pi) * ξ)‖ₑ ^ 2 := by
      simp_rw [hpoint]
    _ = _ := by
      simpa only [abs_of_pos (inv_pos.mpr (by positivity : 0 < 2 * Real.pi)),
        one_div] using
        lintegral_dilate (fun t : ℝ => ‖angularFourier f t‖ₑ ^ 2) hc

private theorem raw_fourier_translation (f : ℝ → ℂ) (s ξ : ℝ) :
    𝓕 (fun x : ℝ => f (x - s)) ξ =
      (Real.fourierChar (-(s * ξ)) : ℂ) * 𝓕 f ξ := by
  simpa [Real.fourier_eq, VectorFourier.fourierIntegral,
    Function.comp_def, sub_eq_add_neg, Real.inner_apply,
    Circle.smul_def, smul_eq_mul, mul_comm] using
    congrFun (VectorFourier.fourierIntegral_comp_add_right
      Real.fourierChar volume (innerₗ ℝ) f (-s)) ξ

theorem raw_fourier_sub {f g : ℝ → ℂ}
    (hf : Integrable f) (hg : Integrable g) (ξ : ℝ) :
    𝓕 (fun x => f x - g x) ξ = 𝓕 f ξ - 𝓕 g ξ := by
  simp only [Real.fourier_eq, smul_sub]
  exact integral_sub ((Real.fourierIntegral_convergent_iff ξ).2 hf)
    ((Real.fourierIntegral_convergent_iff ξ).2 hg)

def lineGapMass (f : ℝ → ℂ) (s : ℝ) : ℝ :=
  ∫ x : ℝ, ‖f x - f (x - s)‖ ^ 2

private theorem linePhase_gap_norm_sq (ξ s : ℝ) :
    ‖(1 : ℂ) - (Real.fourierChar (-(s * ξ)) : ℂ)‖ ^ 2 =
      2 * (1 - Real.cos ((2 * Real.pi * ξ) * s)) := by
  have hre : (Real.fourierChar (-(s * ξ)) : ℂ).re =
      Real.cos ((2 * Real.pi * ξ) * s) := by
    rw [Real.fourierChar_apply, Complex.exp_ofReal_mul_I_re]
    have harg : 2 * Real.pi * -(s * ξ) = -((2 * Real.pi * ξ) * s) := by ring
    rw [harg, Real.cos_neg]
  rw [Complex.sq_norm, Complex.normSq_sub, Complex.normSq_one, Circle.normSq_coe]
  simp only [one_mul, Complex.conj_re]
  rw [hre]
  ring

private theorem lineGapMass_eq_lintegral {f : ℝ → ℂ}
    (hf₁ : Integrable f) (hf₂ : MemLp f 2 volume) (s : ℝ) :
    ENNReal.ofReal (lineGapMass f s) =
      ∫⁻ ξ : ℝ,
        ENNReal.ofReal (2 * (1 - Real.cos ((2 * Real.pi * ξ) * s))) *
          ‖𝓕 f ξ‖ₑ ^ 2 := by
  have hshift₁ : Integrable (fun x : ℝ => f (x - s)) volume := by
    simpa only [Function.comp_def] using
      (measurePreserving_sub_right (volume : Measure ℝ) s).integrable_comp_of_integrable hf₁
  have hshift₂ : MemLp (fun x : ℝ => f (x - s)) 2 volume := by
    simpa only [Function.comp_def] using
      hf₂.comp_measurePreserving (measurePreserving_sub_right (volume : Measure ℝ) s)
  have hgap₁ : Integrable (fun x : ℝ => f x - f (x - s)) volume :=
    hf₁.sub hshift₁
  have hgap₂ : MemLp (fun x : ℝ => f x - f (x - s)) 2 volume :=
    hf₂.sub hshift₂
  have hgap_sq : Integrable (fun x : ℝ => ‖f x - f (x - s)‖ ^ 2) volume :=
    hgap₂.integrable_norm_pow (p := 2) (by norm_num)
  have htransform (ξ : ℝ) :
      𝓕 (fun x : ℝ => f x - f (x - s)) ξ =
        ((1 : ℂ) - (Real.fourierChar (-(s * ξ)) : ℂ)) * 𝓕 f ξ := by
    rw [raw_fourier_sub hf₁ hshift₁ ξ, raw_fourier_translation]
    ring
  have hphase (ξ : ℝ) :
      ‖(1 : ℂ) - (Real.fourierChar (-(s * ξ)) : ℂ)‖ₑ ^ 2 =
        ENNReal.ofReal (2 * (1 - Real.cos ((2 * Real.pi * ξ) * s))) := by
    calc
      _ = ENNReal.ofReal
          (‖(1 : ℂ) - (Real.fourierChar (-(s * ξ)) : ℂ)‖ ^ 2) := by
        rw [ENNReal.ofReal_pow (norm_nonneg _) 2, ofReal_norm]
      _ = _ := congrArg ENNReal.ofReal (linePhase_gap_norm_sq ξ s)
  calc
    ENNReal.ofReal (lineGapMass f s) =
        ∫⁻ x : ℝ, ENNReal.ofReal (‖f x - f (x - s)‖ ^ 2) := by
      unfold lineGapMass
      exact ofReal_integral_eq_lintegral_ofReal hgap_sq
        (Filter.Eventually.of_forall fun x => sq_nonneg _)
    _ = ∫⁻ x : ℝ, ‖f x - f (x - s)‖ₑ ^ 2 := by
      apply lintegral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        dsimp only
        rw [ENNReal.ofReal_pow (norm_nonneg _) 2, ofReal_norm]
    _ = ∫⁻ ξ : ℝ, ‖𝓕 (fun x : ℝ => f x - f (x - s)) ξ‖ₑ ^ 2 :=
      (raw_fourier_extended_plancherel hgap₁ hgap₂).symm
    _ = _ := by
      apply lintegral_congr_ae
      exact Filter.Eventually.of_forall fun ξ => by
        dsimp only
        rw [htransform ξ, enorm_mul, mul_pow, hphase ξ]

end D5.S3.Weil.ZetaGamma.FormCore.LineFourier

namespace D5.S3.Weil.ZetaGamma.FormCore.LineFourier

abbrev actualDensity : ℝ → ℝ :=
  D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.archimedeanJumpDensity

def actualIncrement (z : ℝ) : ℝ :=
  (Complex.digamma ((1 / 4 : ℂ) + Complex.I * ((z / 2 : ℝ) : ℂ))).re -
    (Complex.digamma (1 / 4)).re

def cyclicGap (ξ s : ℝ) : ℝ :=
  2 * (1 - Real.cos ((2 * Real.pi * ξ) * s))

private theorem extended_line_energy_eq_frequency_integral
    (k : ℝ → ℝ) (hk : Measurable k) {f : ℝ → ℂ}
    (hf₁ : Integrable f) (hf₂ : MemLp f 2) :
    (∫⁻ s : ℝ in Ioi 0,
      ENNReal.ofReal (k s) * ENNReal.ofReal (lineGapMass f s)) =
      ∫⁻ ξ : ℝ,
        (∫⁻ s : ℝ in Ioi 0,
          ENNReal.ofReal (k s) * ENNReal.ofReal (cyclicGap ξ s)) *
        ‖𝓕 f ξ‖ₑ ^ 2 := by
  have hgap : Measurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal (cyclicGap p.2 p.1)) := by
    unfold cyclicGap
    fun_prop
  have hmeas : Measurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal (k p.1) *
        (ENNReal.ofReal (cyclicGap p.2 p.1) * ‖𝓕 f p.2‖ₑ ^ 2)) :=
    (ENNReal.measurable_ofReal.comp (hk.comp measurable_fst)).mul
      (hgap.mul (((continuous_raw_fourier hf₁).measurable.comp
        measurable_snd).enorm.pow_const 2))
  calc
    _ = ∫⁻ s : ℝ in Ioi 0, ∫⁻ ξ : ℝ,
        ENNReal.ofReal (k s) *
          (ENNReal.ofReal (cyclicGap ξ s) * ‖𝓕 f ξ‖ₑ ^ 2) := by
      apply lintegral_congr_ae
      exact Filter.Eventually.of_forall fun s => by
        dsimp only
        rw [lineGapMass_eq_lintegral hf₁ hf₂ s]
        exact (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
    _ = ∫⁻ ξ : ℝ, ∫⁻ s : ℝ in Ioi 0,
        ENNReal.ofReal (k s) *
          (ENNReal.ofReal (cyclicGap ξ s) * ‖𝓕 f ξ‖ₑ ^ 2) :=
      lintegral_lintegral_swap hmeas.aemeasurable
    _ = _ := by
      apply lintegral_congr_ae
      exact Filter.Eventually.of_forall fun ξ => by
        simp_rw [← mul_assoc]
        exact lintegral_mul_const' _ _ (by finiteness)

theorem actual_line_spectralWeight (ξ : ℝ) :
    (∫⁻ s : ℝ in Ioi 0,
      ENNReal.ofReal (actualDensity s) * ENNReal.ofReal (cyclicGap ξ s)) =
      ENNReal.ofReal (actualIncrement (2 * Real.pi * ξ)) := by
  let z : ℝ := 2 * Real.pi * ξ
  have hInt : IntegrableOn
      (fun s : ℝ => 2 * actualDensity s * (1 - Real.cos (z * s))) (Ioi 0) :=
    D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.levy_kernel_integrableOn z
  have hnn : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
      0 ≤ 2 * actualDensity s * (1 - Real.cos (z * s)) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
    exact mul_nonneg (mul_nonneg (by norm_num)
      (D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.jump_density_nonnegative hs))
      (sub_nonneg.mpr (Real.cos_le_one _))
  calc
    _ = ∫⁻ s : ℝ in Ioi 0,
        ENNReal.ofReal (2 * actualDensity s * (1 - Real.cos (z * s))) := by
      apply lintegral_congr_ae
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
      rw [← ENNReal.ofReal_mul
        (D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.jump_density_nonnegative hs)]
      congr 1
      dsimp only [cyclicGap, z]
      ring
    _ = ENNReal.ofReal
        (∫ s : ℝ in Ioi 0, 2 * actualDensity s * (1 - Real.cos (z * s))) :=
      (ofReal_integral_eq_lintegral_ofReal hInt hnn).symm
    _ = _ := congrArg ENNReal.ofReal
      (D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.levy_integral_eq_digamma_increment z)

theorem actual_gamma_whole_line_energy_eq_angular_integral
    {f : ℝ → ℂ} (hf₁ : Integrable f) (hf₂ : MemLp f 2) :
    (∫⁻ s : ℝ in Ioi 0,
      ENNReal.ofReal (actualDensity s) * ENNReal.ofReal (lineGapMass f s)) =
      ENNReal.ofReal (1 / (2 * Real.pi)) *
        ∫⁻ z : ℝ, ENNReal.ofReal (actualIncrement z) *
          ‖angularFourier f z‖ₑ ^ 2 := by
  have hk : Measurable actualDensity := by
    unfold actualDensity
      D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.archimedeanJumpDensity
    fun_prop
  have hc : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hpoint (ξ : ℝ) : angularFourier f ((2 * Real.pi) * ξ) = 𝓕 f ξ := by
    unfold angularFourier
    congr 1
    field_simp [Real.pi_ne_zero]
  calc
    _ = ∫⁻ ξ : ℝ, ENNReal.ofReal (actualIncrement (2 * Real.pi * ξ)) *
        ‖𝓕 f ξ‖ₑ ^ 2 := by
      rw [extended_line_energy_eq_frequency_integral actualDensity hk hf₁ hf₂]
      simp_rw [actual_line_spectralWeight]
    _ = ∫⁻ ξ : ℝ, ENNReal.ofReal (actualIncrement ((2 * Real.pi) * ξ)) *
        ‖angularFourier f ((2 * Real.pi) * ξ)‖ₑ ^ 2 := by
      simp_rw [hpoint]
    _ = _ := by
      simpa only [abs_of_pos (inv_pos.mpr (by positivity : 0 < 2 * Real.pi)),
        one_div] using
        lintegral_dilate (fun z : ℝ => ENNReal.ofReal (actualIncrement z) *
          ‖angularFourier f z‖ₑ ^ 2) hc

end D5.S3.Weil.ZetaGamma.FormCore.LineFourier
