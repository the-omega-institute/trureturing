/- GID: D5/S3/Weil/ZetaGamma/FormCore/CutoffConvergence
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaGamma/FormCore/CutoffConvergence
   mirror-E: none(waiver:analytic-Gamma-form-core)
   anchors: []
   utility: none
   digest: Actual cutoff energy convergence and measurable representatives. -/


import D5.S3.Weil.PrimePoleTerms
import D5.S3.Weil.TestFunctions.ConvolutionSquarePositivity
import D5.S3.Weil.ZetaBridge.ClassicExplicitFormula
import D5.S3.Weil.ZetaCore.ExplicitFormulaBridge
import D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition
import D5.S3.Weil.ZetaGamma.FormCore.CornerTransport
import D5.S3.Weil.ZetaGamma.FormCore.DirectionalEnergy
import D5.S3.Weil.ZetaGamma.FormCore.ExteriorBudget
import D5.S3.Weil.ZetaGamma.FormCore.SmoothCutoff
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
open D5.S3.Weil.ZetaGamma.FormCore.Corner
open scoped ENNReal Topology

private theorem actual_gamma_radialMaskEnergy_eq_ofReal
    (b : ℝ → ℝ) (hb : Measurable b) (y : ℝ)
    (hi : IntegrableOn (cutoffRadialGap b y) (Ioi (0 : ℝ))) :
    radialMaskEnergy actualGammaExitMeasure b y =
      ENNReal.ofReal (∫ r in Ioi (0 : ℝ), cutoffRadialGap b y r) := by
  have hρ : Measurable (fun r => ENNReal.ofReal (actualDensity r)) :=
    actual_density_measurable.ennreal_ofReal
  have hpair : Measurable (fun r : ℝ => ENNReal.ofReal
      ((b (y + r) - b y) ^ 2 + (b (y - r) - b y) ^ 2)) := by
    fun_prop
  have hnn : ∀ᵐ r ∂volume.restrict (Ioi (0 : ℝ)),
      0 ≤ cutoffRadialGap b y r := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    exact cutoffRadialGap_nonneg b y hr
  calc
    radialMaskEnergy actualGammaExitMeasure b y =
        ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (actualDensity r) *
          ENNReal.ofReal ((b (y + r) - b y) ^ 2 + (b (y - r) - b y) ^ 2) := by
      unfold radialMaskEnergy actualGammaExitMeasure
      exact lintegral_withDensity_eq_lintegral_mul _ hρ hpair
    _ = ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (cutoffRadialGap b y r) := by
      apply lintegral_congr_ae
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
      rw [cutoffRadialGap, ENNReal.ofReal_mul (actual_density_pos hr).le]
    _ = ENNReal.ofReal (∫ r in Ioi (0 : ℝ), cutoffRadialGap b y r) :=
      (ofReal_integral_eq_lintegral_ofReal hi hnn).symm

private theorem actual_gamma_radialMaskEnergy_bound_and_tendsto :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a y : ℝ, y ∈ Ioo (-a) a →
      (∀ ε : ℝ, 0 < ε →
        radialMaskEnergy actualGammaExitMeasure (actualCutoffMask a ε) y ≤
          ENNReal.ofReal C +
            2 * exteriorPotential actualGammaExitMeasure (Ioo (-a) a) y) ∧
      Tendsto (fun ε =>
        radialMaskEnergy actualGammaExitMeasure (actualCutoffMask a ε) y)
        (𝓝[Ioi (0 : ℝ)] 0) (𝓝 0) := by
  obtain ⟨C, hC, _hsmooth, hcut⟩ := actual_smooth_cutoff_commutator
  refine ⟨C, hC, ?_⟩
  intro a y hy
  have hleft : 0 < a + y := by linarith [hy.1]
  have hright : 0 < a - y := sub_pos.mpr hy.2
  have hV : 0 ≤ actualExteriorPotential a y := by
    unfold actualExteriorPotential
    exact add_nonneg (actualDensity_tail_nonneg hright)
      (actualDensity_tail_nonneg hleft)
  have hradial := (hcut a y hy).1
  refine ⟨?_, ?_⟩
  · intro ε hε
    have hi := (hradial.1 ε hε).1
    calc
      radialMaskEnergy actualGammaExitMeasure (actualCutoffMask a ε) y =
          ENNReal.ofReal (∫ r in Ioi (0 : ℝ),
            cutoffRadialGap (actualCutoffMask a ε) y r) :=
        actual_gamma_radialMaskEnergy_eq_ofReal _ (actualCutoffMask_measurable a ε) y hi
      _ ≤ ENNReal.ofReal (C + 2 * actualExteriorPotential a y) :=
        ENNReal.ofReal_le_ofReal (hradial.1 ε hε).2
      _ = ENNReal.ofReal C + (2 : ℝ≥0∞) *
          exteriorPotential actualGammaExitMeasure (Ioo (-a) a) y := by
        rw [ENNReal.ofReal_add hC (mul_nonneg (by norm_num) hV),
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
          actual_gamma_exteriorPotential_eq_ofReal hy]
        norm_num
  · have hoff : Tendsto (fun ε => ENNReal.ofReal
        (∫ r in Ioi (0 : ℝ), cutoffRadialGap (actualCutoffMask a ε) y r))
        (𝓝[Ioi (0 : ℝ)] 0) (𝓝 (0 : ℝ≥0∞)) := by
      simpa only [Function.comp_def, ENNReal.ofReal_zero] using
        (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hradial.2
    apply hoff.congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (actual_gamma_radialMaskEnergy_eq_ofReal _
      (actualCutoffMask_measurable a ε) y (hradial.1 ε hε).1).symm

private theorem actual_gamma_cutoff_radial_outer_tendsto_zero
    (a : ℝ) (F : ℝ → ℂ) (hF : Measurable F) (hF₂ : MemLp F 2)
    (hzero : ∀ x ∉ Ioo (-a) a, F x = 0)
    (henergy : directionalEnergy actualGammaExitMeasure F < (⊤ : ℝ≥0∞)) :
    Tendsto (fun ε => ∫⁻ y : ℝ, ‖F y‖ₑ ^ 2 *
      radialMaskEnergy actualGammaExitMeasure (actualCutoffMask a ε) y)
      (𝓝[Ioi (0 : ℝ)] 0) (𝓝 0) := by
  obtain ⟨C, _hC, hcut⟩ := actual_gamma_radialMaskEnergy_bound_and_tendsto
  let G : ℝ → ℝ → ℝ≥0∞ := fun ε y => ‖F y‖ₑ ^ 2 *
    radialMaskEnergy actualGammaExitMeasure (actualCutoffMask a ε) y
  let D : ℝ → ℝ≥0∞ := fun y =>
    ENNReal.ofReal C * ‖F y‖ₑ ^ 2 +
      2 * (‖F y‖ₑ ^ 2 * exteriorPotential actualGammaExitMeasure (Ioo (-a) a) y)
  have hmassR : Integrable (fun y => ‖F y‖ ^ 2) :=
    hF₂.integrable_norm_pow (p := 2) (by norm_num)
  have hmass_eq : (∫⁻ y : ℝ, ‖F y‖ₑ ^ 2) =
      ENNReal.ofReal (∫ y : ℝ, ‖F y‖ ^ 2) := by
    rw [ofReal_integral_eq_lintegral_ofReal hmassR
      (Eventually.of_forall fun y => sq_nonneg ‖F y‖)]
    apply lintegral_congr_ae
    exact Eventually.of_forall fun y => by
      dsimp only
      rw [ENNReal.ofReal_pow (norm_nonneg _) 2, ofReal_norm]
  have hmass : (∫⁻ y : ℝ, ‖F y‖ₑ ^ 2) < (⊤ : ℝ≥0∞) := by
    rw [hmass_eq]
    exact ENNReal.ofReal_lt_top
  have hfinite : (∫⁻ y : ℝ, D y) ≠ (⊤ : ℝ≥0∞) :=
    (cutoff_outer_majorant_finite actualGammaExitMeasure (Ioo (-a) a)
      measurableSet_Ioo F hF hzero hmass henergy C).ne
  have hmeas : ∀ᶠ ε in 𝓝[Ioi (0 : ℝ)] 0, Measurable (G ε) :=
    Eventually.of_forall fun ε =>
      (hF.enorm.pow_const 2).mul
        (radialMaskEnergy_measurable actualGammaExitMeasure _
          (actualCutoffMask_measurable a ε))
  have hdom : ∀ᶠ ε in 𝓝[Ioi (0 : ℝ)] 0,
      ∀ᵐ y ∂volume, G ε y ≤ D y := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact Eventually.of_forall fun y => by
      by_cases hy : y ∈ Ioo (-a) a
      · calc
          G ε y ≤ ‖F y‖ₑ ^ 2 * (ENNReal.ofReal C +
              2 * exteriorPotential actualGammaExitMeasure (Ioo (-a) a) y) :=
            mul_le_mul' le_rfl ((hcut a y hy).1 ε hε)
          _ = D y := by
            dsimp only [D]
            rw [mul_add]
            ac_rfl
      · simp [G, D, hzero y hy]
  have hlim : ∀ᵐ y ∂volume,
      Tendsto (fun ε => G ε y) (𝓝[Ioi (0 : ℝ)] 0) (𝓝 (0 : ℝ≥0∞)) := by
    exact Eventually.of_forall fun y => by
      by_cases hy : y ∈ Ioo (-a) a
      · simpa only [G, mul_zero] using
          (ENNReal.Tendsto.const_mul (a := ‖F y‖ₑ ^ 2) (hcut a y hy).2
            (Or.inr (by finiteness : ‖F y‖ₑ ^ 2 ≠ (⊤ : ℝ≥0∞))))
      · simpa [G, hzero y hy] using
          (tendsto_const_nhds : Tendsto (fun _ε : ℝ => (0 : ℝ≥0∞))
            (𝓝[Ioi (0 : ℝ)] 0) (𝓝 0))
  simpa only [G, lintegral_zero] using
    tendsto_lintegral_filter_of_dominated_convergence
      (μ := (volume : Measure ℝ)) (f := fun _ => (0 : ℝ≥0∞))
      D hmeas hdom hfinite hlim

end D5.S3.Weil.ZetaGamma.FormCore

namespace D5.S3.Weil.ZetaGamma.FormCore

open MeasureTheory Set Filter
open D5.S3.Weil.ZetaGamma.FormCore.Corner
open scoped ENNReal Topology

theorem actual_gamma_cutoff_error_energy_tendsto_zero
    (a : ℝ) (F : ℝ → ℂ) (hF : Measurable F) (hF₂ : MemLp F 2)
    (hzero : ∀ x ∉ Ioo (-a) a, F x = 0)
    (henergy : directionalEnergy actualGammaExitMeasure F < (⊤ : ℝ≥0∞)) :
    Tendsto (fun ε => directionalEnergy actualGammaExitMeasure
      (fun x => (actualCutoffMask a ε x : ℂ) * F x))
      (𝓝[Ioi (0 : ℝ)] 0) (𝓝 (0 : ℝ≥0∞)) := by
  have hfirst := cutoffFirstEnergy_tendsto_zero actualGammaExitMeasure F hF henergy
    (actualCutoffMask a) (actualCutoffMask_measurable a)
    (fun ε _hε x => actualCutoffMask_range a ε x)
    (actualCutoffMask_tendsto_zero a)
  have hsecond := actual_gamma_cutoff_radial_outer_tendsto_zero
    a F hF hF₂ hzero henergy
  have hsum : Tendsto (fun ε => cutoffFirstEnergy actualGammaExitMeasure
      (actualCutoffMask a ε) F + ∫⁻ y : ℝ, ‖F y‖ₑ ^ 2 *
        radialMaskEnergy actualGammaExitMeasure (actualCutoffMask a ε) y)
      (𝓝[Ioi (0 : ℝ)] 0) (𝓝 (0 : ℝ≥0∞)) := by
    simpa only [zero_add] using hfirst.add hsecond
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le) (fun ε => directionalEnergy_cutoff_le
      actualGammaExitMeasure (actualCutoffMask a ε)
      (actualCutoffMask_measurable a ε) F hF)

end D5.S3.Weil.ZetaGamma.FormCore

namespace D5.S3.Weil.ZetaGamma.FormCore

open MeasureTheory Set Filter
open scoped ENNReal Classical

theorem directionalEnergy_congr_ae (nu : Measure ℝ)
    {F G : ℝ → ℂ} (h : F =ᵐ[volume] G) :
    directionalEnergy nu F = directionalEnergy nu G := by
  unfold directionalEnergy
  apply lintegral_congr_ae
  exact Eventually.of_forall fun s => by
    have hs : (fun x : ℝ => F (x - s)) =ᵐ[volume]
        (fun x : ℝ => G (x - s)) :=
      (measurePreserving_sub_right (volume : Measure ℝ) s).quasiMeasurePreserving.ae_eq h
    apply lintegral_congr_ae
    filter_upwards [h, hs] with x hx hxs
    rw [hx, hxs]

theorem exists_measurable_zero_supported_energy_representative
    (nu : Measure ℝ) (Omega : Set ℝ) (hOmega : MeasurableSet Omega)
    (F : ℝ → ℂ) (hF : AEMeasurable F)
    (hzero : ∀ᵐ x : ℝ, x ∉ Omega → F x = 0) :
    ∃ G : ℝ → ℂ, Measurable G ∧ (∀ x ∉ Omega, G x = 0) ∧
      F =ᵐ[volume] G ∧
      (∫⁻ x : ℝ, ‖F x‖ₑ ^ 2) = (∫⁻ x : ℝ, ‖G x‖ₑ ^ 2) ∧
      directionalEnergy nu F = directionalEnergy nu G := by
  let G : ℝ → ℂ := Omega.indicator (hF.mk F)
  have hG : Measurable G := hF.measurable_mk.indicator hOmega
  have hGzero : ∀ x ∉ Omega, G x = 0 := by
    intro x hx
    exact indicator_of_notMem hx _
  have hFG : F =ᵐ[volume] G := by
    filter_upwards [hF.ae_eq_mk, hzero] with x hx hz
    by_cases hmem : x ∈ Omega
    · simpa only [G, indicator_of_mem hmem] using hx
    · simp only [G, indicator_of_notMem hmem, hz hmem]
  refine ⟨G, hG, hGzero, hFG, ?_, directionalEnergy_congr_ae nu hFG⟩
  apply lintegral_congr_ae
  filter_upwards [hFG] with x hx
  rw [hx]

end D5.S3.Weil.ZetaGamma.FormCore
