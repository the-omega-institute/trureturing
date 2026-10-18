/- GID: D5/S3/Weil/ZetaGamma/FormCore/FrequencyDomain
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaGamma/FormCore/FrequencyDomain
   mirror-E: none(waiver:analytic-Gamma-form-core)
   anchors: []
   utility: none
   digest: Original-Ioc actual-Gamma frequency domain. -/

/- SOURCE_ONLY_UNCOMPILED. Repackaged from exact accepted input e122c325.
The prior receipt does not certify these module boundaries, imports or exports.
Canonical original-Ioc carriers and full actual-Gamma energy are retained. -/

import D5.S3.Weil.PrimePoleTerms
import D5.S3.Weil.TestFunctions.ConvolutionSquarePositivity
import D5.S3.Weil.ZetaBridge.ClassicExplicitFormula
import D5.S3.Weil.ZetaCore.ExplicitFormulaBridge
import D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition
import D5.S3.Weil.ZetaGamma.FormCore.DomainPassage
import D5.S3.Weil.ZetaGamma.FormCore.PeriodicSpectralEnergy
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

namespace D5.S3.Weil.ZetaGamma.FormCore.DomainPassage

open MeasureTheory Set
open scoped ENNReal

private theorem actual_gamma_zero_domain_iff_periodic_frequency_sum_finite
    (a : ℝ) (ha : 0 < a) (u : ℝ → ℂ)
    (hu : MemLp u 2 (volume.restrict (Ioc (-a) a))) :
    letI : Fact (0 < 2 * a) := ⟨by linarith⟩
    IntegrableOn (zeroEnergyDensity (2 * a) (-a) u) (Ioi 0) ↔
      (∑' n : ℤ,
        (∫⁻ s : ℝ in Ioi 0, ENNReal.ofReal (density s) *
          ENNReal.ofReal
            (D5.S3.Weil.ZetaGamma.FormCore.PeriodicSpectralEnergy.phaseGap
              (d := 2 * a) n s)) *
        ENNReal.ofReal
          (‖D5.S3.Weil.ZetaGamma.FormCore.PeriodicSpectralEnergy.physicalCoeff
            (AddCircle.liftIoc (2 * a) (-a) u) n‖ ^ 2)) < ∞ := by
  letI : Fact (0 < 2 * a) := ⟨by linarith⟩
  have hend : -a + 2 * a = a := by ring
  have huCommon : MemLp u 2
      (D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.windowMeasure (2 * a) (-a)) := by
    simpa only [D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.windowMeasure, hend] using hu
  have hdensity : Measurable density := by
    unfold density
      D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.archimedeanJumpDensity
    fun_prop
  have hmeas : AEStronglyMeasurable
      (periodicEnergyDensity (2 * a) (-a) u) (volume.restrict (Ioi (0 : ℝ))) := by
    have h := hdensity.aestronglyMeasurable.mul
      (D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.periodicTranslationEnergy_aestronglyMeasurable
        (2 * a) (-a) u huCommon)
    exact h.restrict
  have hnonneg : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
      0 ≤ periodicEnergyDensity (2 * a) (-a) u s := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
    exact mul_nonneg (density_nonneg hs)
      (integral_nonneg fun x => Complex.normSq_nonneg _)
  have hMass (s : ℝ) :
      D5.S3.Weil.ZetaGamma.FormCore.PeriodicSpectralEnergy.windowGapMass
        (d := 2 * a) (-a) u s =
      D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.periodicTranslationEnergy
        (2 * a) (-a) u s := by
    simp only [D5.S3.Weil.ZetaGamma.FormCore.PeriodicSpectralEnergy.windowGapMass,
      D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.periodicTranslationEnergy,
      D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.periodicExtension,
      D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.windowMeasure,
      Complex.normSq_eq_norm_sq]
  have hEnergy :=
    D5.S3.Weil.ZetaGamma.FormCore.PeriodicSpectralEnergy.extended_window_energy_eq_tsum
      density hdensity (-a) u huCommon
  have hLinear :
      (∫⁻ s : ℝ in Ioi 0,
        ENNReal.ofReal (periodicEnergyDensity (2 * a) (-a) u s)) =
      ∫⁻ s : ℝ in Ioi 0,
        ENNReal.ofReal (density s) *
          ENNReal.ofReal
            (D5.S3.Weil.ZetaGamma.FormCore.PeriodicSpectralEnergy.windowGapMass
              (d := 2 * a) (-a) u s) := by
    apply lintegral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
    rw [hMass]
    exact ENNReal.ofReal_mul (density_nonneg hs)
  rw [(actual_centered_gamma_full_domain_equivalence a ha u hu).1]
  rw [← hEnergy, ← hLinear]
  exact ⟨fun h => (hasFiniteIntegral_iff_ofReal hnonneg).mp h.2,
    fun h => ⟨hmeas, (hasFiniteIntegral_iff_ofReal hnonneg).mpr h⟩⟩

end D5.S3.Weil.ZetaGamma.FormCore.DomainPassage

namespace D5.S3.Weil.ZetaGamma.FormCore.DomainPassage

open MeasureTheory Set
open scoped ENNReal

theorem actual_gamma_zero_domain_iff_digamma_weighted_sum_finite
    (a : ℝ) (ha : 0 < a) (u : ℝ → ℂ)
    (hu : MemLp u 2 (volume.restrict (Ioc (-a) a))) :
    letI : Fact (0 < 2 * a) := ⟨by linarith⟩
    IntegrableOn (zeroEnergyDensity (2 * a) (-a) u) (Ioi 0) ↔
      (∑' n : ℤ,
        ENNReal.ofReal
          (D5.S3.Weil.ZetaGamma.FormCore.PeriodicSpectralEnergy.gammaIncrement
            (D5.S3.Weil.ZetaGamma.FormCore.PeriodicSpectralEnergy.angularFrequency
              (d := 2 * a) n)) *
        ENNReal.ofReal
          (‖D5.S3.Weil.ZetaGamma.FormCore.PeriodicSpectralEnergy.physicalCoeff
            (AddCircle.liftIoc (2 * a) (-a) u) n‖ ^ 2)) < ∞ := by
  letI : Fact (0 < 2 * a) := ⟨by linarith⟩
  have hweight (n : ℤ) :
      (∫⁻ s : ℝ in Ioi 0,
        ENNReal.ofReal (density s) *
          ENNReal.ofReal
            (D5.S3.Weil.ZetaGamma.FormCore.PeriodicSpectralEnergy.phaseGap
              (d := 2 * a) n s)) =
        ENNReal.ofReal
          (D5.S3.Weil.ZetaGamma.FormCore.PeriodicSpectralEnergy.gammaIncrement
            (D5.S3.Weil.ZetaGamma.FormCore.PeriodicSpectralEnergy.angularFrequency
              (d := 2 * a) n)) := by
    simpa only [density,
      D5.S3.Weil.ZetaGamma.FormCore.PeriodicSpectralEnergy.gammaDensity] using
      D5.S3.Weil.ZetaGamma.FormCore.PeriodicSpectralEnergy.actual_gamma_spectralWeight
        (d := 2 * a) n
  simpa only [hweight] using
    actual_gamma_zero_domain_iff_periodic_frequency_sum_finite a ha u hu

end D5.S3.Weil.ZetaGamma.FormCore.DomainPassage
