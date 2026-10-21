/- GID: D5/S3/Weil/ZetaGamma/FormCore/InteriorApproximation
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaGamma/FormCore/InteriorApproximation
   mirror-E: none(waiver:analytic-Gamma-form-core)
   anchors: []
   utility: none
   digest: Original-Ioc inward approximation in mass and actual energy. -/


import D5.S3.Weil.PrimePoleTerms
import D5.S3.Weil.TestFunctions.ConvolutionSquarePositivity
import D5.S3.Weil.ZetaBridge.ClassicExplicitFormula
import D5.S3.Weil.ZetaCore.ExplicitFormulaBridge
import D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition
import D5.S3.Weil.ZetaGamma.FormCore.CutoffConvergence
import D5.S3.Weil.ZetaGamma.FormCore.CutoffSupport
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

private theorem directionalEnergy_neg (nu : Measure ℝ) (F : ℝ → ℂ) :
    directionalEnergy nu (fun x => -F x) = directionalEnergy nu F := by
  unfold directionalEnergy
  apply lintegral_congr_ae
  exact Eventually.of_forall fun s => by
    apply lintegral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp only
      rw [show -F x - -F (x - s) = -(F x - F (x - s)) by abel, enorm_neg]

theorem actual_gamma_interior_cutoff_form_approximation
    (a : ℝ) (F : ℝ → ℂ) (hF : Measurable F) (hF₂ : MemLp F 2)
    (hzero : ∀ x ∉ Ioo (-a) a, F x = 0)
    (henergy : directionalEnergy actualGammaExitMeasure F < (⊤ : ℝ≥0∞)) :
    (∀ ε > 0, HasCompactSupport (fun x => (actualCutoffEta a ε x : ℂ) * F x) ∧
      tsupport (fun x => (actualCutoffEta a ε x : ℂ) * F x) ⊆ Ioo (-a) a) ∧
    Tendsto (fun ε =>
      (∫⁻ x : ℝ, ‖(actualCutoffEta a ε x : ℂ) * F x - F x‖ₑ ^ 2) +
        directionalEnergy actualGammaExitMeasure
          (fun x => (actualCutoffEta a ε x : ℂ) * F x - F x))
      (𝓝[Ioi (0 : ℝ)] 0) (𝓝 (0 : ℝ≥0∞)) := by
  have hmass : (∫⁻ x : ℝ, ‖F x‖ₑ ^ 2) < (⊤ : ℝ≥0∞) := by
    have hm := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num) hF₂
    simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_two] using hm
  have hm := actualCutoffEta_mul_sub_mass_tendsto_zero a F hF hmass hzero
  have he := actual_gamma_cutoff_error_energy_tendsto_zero a F hF hF₂ hzero henergy
  have he' : Tendsto (fun ε => directionalEnergy actualGammaExitMeasure
      (fun x => (actualCutoffEta a ε x : ℂ) * F x - F x))
      (𝓝[Ioi (0 : ℝ)] 0) (𝓝 (0 : ℝ≥0∞)) := by
    apply he.congr'
    exact Eventually.of_forall fun ε => by
      have hpoint : (fun x => (actualCutoffEta a ε x : ℂ) * F x - F x) =
          (fun x => -((actualCutoffMask a ε x : ℂ) * F x)) := by
        funext x
        rw [actualCutoffEta_mul_eq_sub_mask a ε F hzero x]
        abel
      dsimp only
      rw [hpoint, directionalEnergy_neg]
  refine ⟨?_, ?_⟩
  · intro ε hε
    refine ⟨actualCutoffEta_mul_hasCompactSupport hε F, ?_⟩
    intro x hx
    have hx' := actualCutoffEta_mul_tsupport_subset_Icc hε F hx
    constructor <;> linarith [hx'.1, hx'.2]
  · simpa only [zero_add] using hm.add he'

end D5.S3.Weil.ZetaGamma.FormCore

namespace D5.S3.Weil.ZetaGamma.FormCore

open MeasureTheory Set Filter
open D5.S3.Weil.ZetaGamma.FormCore.Corner
open scoped ENNReal Topology

private theorem actual_ioc_zeroExtension_ae_zero_outside
    (a : ℝ) (u : ℝ → ℂ) :
    ∀ᵐ x : ℝ, x ∉ Ioo (-a) a →
      D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.zeroExtension (2 * a) (-a) u x = 0 := by
  have hend : -a + 2 * a = a := by ring
  filter_upwards [(volume : Measure ℝ).ae_ne a] with x hxa
  intro hx
  have hnot : x ∉ Ioc (-a) a := by
    intro hxi
    exact hx ⟨hxi.1, lt_of_le_of_ne hxi.2 hxa⟩
  simp only [D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.zeroExtension, hend,
    indicator_of_notMem hnot]

private theorem actual_ioc_zeroExtension_mass_eq (a : ℝ) (u : ℝ → ℂ) :
    (∫⁻ x : ℝ,
      ‖D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.zeroExtension (2 * a) (-a) u x‖ₑ ^ 2) =
        ∫⁻ x in Ioc (-a) a, ‖u x‖ₑ ^ 2 := by
  have hend : -a + 2 * a = a := by ring
  calc
    _ = ∫⁻ x : ℝ, (Ioc (-a) a).indicator (fun y => ‖u y‖ₑ ^ 2) x := by
      apply lintegral_congr_ae
      exact Eventually.of_forall fun x => by
        by_cases hx : x ∈ Ioc (-a) a <;>
          simp [D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.zeroExtension, hend, hx]
    _ = _ := lintegral_indicator measurableSet_Ioc _

theorem actual_ioc_exists_measurable_zero_supported_energy_representative
    (a : ℝ) (u : ℝ → ℂ)
    (hu : MemLp u 2 (volume.restrict (Ioc (-a) a))) :
    ∃ G : ℝ → ℂ, Measurable G ∧ MemLp G 2 ∧
      (∀ x ∉ Ioo (-a) a, G x = 0) ∧
      D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.zeroExtension (2 * a) (-a) u =ᵐ[volume] G ∧
      ((∫⁻ x : ℝ,
          ‖D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.zeroExtension (2 * a) (-a) u x‖ₑ ^ 2) =
        ∫⁻ x : ℝ, ‖G x‖ₑ ^ 2) ∧
      ((∫⁻ x in Ioc (-a) a, ‖u x‖ₑ ^ 2) = ∫⁻ x : ℝ, ‖G x‖ₑ ^ 2) ∧
      directionalEnergy actualGammaExitMeasure
        (D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.zeroExtension (2 * a) (-a) u) =
          directionalEnergy actualGammaExitMeasure G := by
  have hend : -a + 2 * a = a := by ring
  have hF₂ : MemLp
      (D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.zeroExtension (2 * a) (-a) u) 2 := by
    simpa only [D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.zeroExtension, hend] using
      (memLp_indicator_iff_restrict (μ := volume)
        measurableSet_Ioc.nullMeasurableSet).mpr hu
  obtain ⟨G, hG, hGzero, hFG, hmass, henergy⟩ :=
    exists_measurable_zero_supported_energy_representative
      actualGammaExitMeasure (Ioo (-a) a) measurableSet_Ioo
      (D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.zeroExtension (2 * a) (-a) u)
      hF₂.aestronglyMeasurable.aemeasurable (actual_ioc_zeroExtension_ae_zero_outside a u)
  refine ⟨G, hG, (memLp_congr_ae hFG).mp hF₂, hGzero, hFG, hmass, ?_, henergy⟩
  exact (actual_ioc_zeroExtension_mass_eq a u).symm.trans hmass

private theorem actual_ioc_cutoff_error_energy_tendsto_zero
    (a : ℝ) (u : ℝ → ℂ)
    (hu : MemLp u 2 (volume.restrict (Ioc (-a) a)))
    (henergy : directionalEnergy actualGammaExitMeasure
      (D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.zeroExtension (2 * a) (-a) u) < (⊤ : ℝ≥0∞)) :
    Tendsto (fun ε => directionalEnergy actualGammaExitMeasure
      (fun x => (actualCutoffMask a ε x : ℂ) *
        D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.zeroExtension (2 * a) (-a) u x))
      (𝓝[Ioi (0 : ℝ)] 0) (𝓝 (0 : ℝ≥0∞)) := by
  obtain ⟨G, hG, hG₂, hGzero, hFG, _hmass, _hmassIoc, henergyEq⟩ :=
    actual_ioc_exists_measurable_zero_supported_energy_representative a u hu
  have hGenergy : directionalEnergy actualGammaExitMeasure G < (⊤ : ℝ≥0∞) := by
    rw [← henergyEq]
    exact henergy
  have hlim := actual_gamma_cutoff_error_energy_tendsto_zero a G hG hG₂ hGzero hGenergy
  apply hlim.congr'
  exact Eventually.of_forall fun ε => by
    have hcut :
        (fun x => (actualCutoffMask a ε x : ℂ) *
          D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.zeroExtension (2 * a) (-a) u x) =ᵐ[volume]
            (fun x => (actualCutoffMask a ε x : ℂ) * G x) := by
      filter_upwards [hFG] with x hx
      rw [hx]
    exact (directionalEnergy_congr_ae actualGammaExitMeasure hcut).symm

end D5.S3.Weil.ZetaGamma.FormCore

namespace D5.S3.Weil.ZetaGamma.FormCore

open MeasureTheory Set Filter
open D5.S3.Weil.ZetaGamma.FormCore.Corner
open scoped ENNReal Topology

private theorem actual_ioc_interior_cutoff_form_approximation
    (a : ℝ) (u : ℝ → ℂ)
    (hu : MemLp u 2 (volume.restrict (Ioc (-a) a)))
    (henergy : directionalEnergy actualGammaExitMeasure
      (D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.zeroExtension (2 * a) (-a) u) < (⊤ : ℝ≥0∞)) :
    let F := D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.zeroExtension (2 * a) (-a) u
    (∀ ε > 0, HasCompactSupport (fun x => (actualCutoffEta a ε x : ℂ) * F x) ∧
      tsupport (fun x => (actualCutoffEta a ε x : ℂ) * F x) ⊆ Ioo (-a) a) ∧
    Tendsto (fun ε =>
      (∫⁻ x : ℝ, ‖(actualCutoffEta a ε x : ℂ) * F x - F x‖ₑ ^ 2) +
        directionalEnergy actualGammaExitMeasure
          (fun x => (actualCutoffEta a ε x : ℂ) * F x - F x))
      (𝓝[Ioi (0 : ℝ)] 0) (𝓝 (0 : ℝ≥0∞)) := by
  dsimp only
  let F := D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.zeroExtension (2 * a) (-a) u
  obtain ⟨G, hG, hG₂, hGzero, hFG, _hmass, _hmassIoc, henergyEq⟩ :=
    actual_ioc_exists_measurable_zero_supported_energy_representative a u hu
  have hGenergy : directionalEnergy actualGammaExitMeasure G < (⊤ : ℝ≥0∞) := by
    rw [← henergyEq]
    exact henergy
  have hlim := (actual_gamma_interior_cutoff_form_approximation
    a G hG hG₂ hGzero hGenergy).2
  refine ⟨?_, ?_⟩
  · intro ε hε
    refine ⟨actualCutoffEta_mul_hasCompactSupport hε F, ?_⟩
    intro x hx
    have hx' := actualCutoffEta_mul_tsupport_subset_Icc hε F hx
    constructor <;> linarith [hx'.1, hx'.2]
  · apply hlim.congr'
    exact Eventually.of_forall fun ε => by
      have herr : (fun x => (actualCutoffEta a ε x : ℂ) * F x - F x) =ᵐ[volume]
          (fun x => (actualCutoffEta a ε x : ℂ) * G x - G x) := by
        filter_upwards [hFG] with x hx
        dsimp only [F]
        rw [hx]
      have hm : (∫⁻ x : ℝ, ‖(actualCutoffEta a ε x : ℂ) * F x - F x‖ₑ ^ 2) =
          ∫⁻ x : ℝ, ‖(actualCutoffEta a ε x : ℂ) * G x - G x‖ₑ ^ 2 := by
        apply lintegral_congr_ae
        filter_upwards [herr] with x hx
        rw [hx]
      have he := directionalEnergy_congr_ae actualGammaExitMeasure herr
      dsimp only
      exact (congrArg₂ (fun x y : ℝ≥0∞ => x + y) hm he).symm

end D5.S3.Weil.ZetaGamma.FormCore
