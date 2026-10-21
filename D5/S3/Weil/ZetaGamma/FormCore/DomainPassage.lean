/- GID: D5/S3/Weil/ZetaGamma/FormCore/DomainPassage
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaGamma/FormCore/DomainPassage
   mirror-E: none(waiver:analytic-Gamma-form-core)
   anchors: []
   utility: none
   digest: Nonnegative full-domain passage without infinite subtraction. -/


import D5.S3.Weil.PrimePoleTerms
import D5.S3.Weil.TestFunctions.ConvolutionSquarePositivity
import D5.S3.Weil.ZetaBridge.ClassicExplicitFormula
import D5.S3.Weil.ZetaCore.ExplicitFormulaBridge
import D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition
import D5.S3.Weil.ZetaGamma.FormCore.CommonCutoff
import D5.S3.Weil.ZetaGamma.FormCore.CornerTransport
import D5.S3.Weil.ZetaGamma.FormCore.LatticeBoundary
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

open D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport

abbrev density :=
  D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.archimedeanJumpDensity

def intervalMeasure (d t : ℝ) : Measure ℝ :=
  volume.restrict (Ioc t (t + d))

def zeroEnergyDensity (d t : ℝ) (u : ℝ → ℂ) (s : ℝ) : ℝ :=
  density s * ∫ x : ℝ, Complex.normSq
    (zeroExtension d t u x - zeroExtension d t u (x - s))

def periodicEnergyDensity (d t : ℝ) [Fact (0 < d)]
    (u : ℝ → ℂ) (s : ℝ) : ℝ :=
  density s * ∫ x : ℝ, Complex.normSq
    (u x - periodicExtension d t u (x - s)) ∂intervalMeasure d t

def cutoffKernel (ε s : ℝ) : ℝ :=
  if ε < |s| then density |s| else 0

def cutoffBoundaryPair (d t ε : ℝ) (u : ℝ → ℂ) : ℝ :=
  (∫ p : ℝ × ℝ, conj (u p.1) *
    ((∑' m : ℤ, if m = 0 then 0 else
      cutoffKernel ε (p.1 - p.2 + m • d)) : ℂ) * u p.2
    ∂(intervalMeasure d t).prod (intervalMeasure d t)).re

private def cutoff (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

private theorem cutoff_pos (n : ℕ) : 0 < cutoff n := by
  unfold cutoff
  positivity

private theorem cutoff_tendsto : Tendsto cutoff atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

theorem density_nonneg {s : ℝ} (hs : 0 < s) : 0 ≤ density s := by
  change 0 ≤ Real.exp (-s / 2) / (1 - Real.exp (-2 * s))
  exact div_nonneg (Real.exp_pos _).le
    (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith)))

private theorem actual_nonnegative_energy_domain_passage
    (d t : ℝ) [Fact (0 < d)] (u : ℝ → ℂ)
    (hcut0 : ∀ ε : ℝ, 0 < ε →
      IntegrableOn (zeroEnergyDensity d t u) (Ioi ε))
    (hcutP : ∀ ε : ℝ, 0 < ε →
      IntegrableOn (periodicEnergyDensity d t u) (Ioi ε))
    (hfinite : ∀ ε : ℝ, 0 < ε →
      (∫ s in Ioi ε, zeroEnergyDensity d t u s) =
        (∫ s in Ioi ε, periodicEnergyDensity d t u s) +
          cutoffBoundaryPair d t ε u)
    (hboundary : Tendsto (fun n => cutoffBoundaryPair d t (cutoff n) u)
      atTop (𝓝 (cutoffBoundaryPair d t 0 u))) :
    (IntegrableOn (zeroEnergyDensity d t u) (Ioi 0) ↔
      IntegrableOn (periodicEnergyDensity d t u) (Ioi 0)) ∧
    (IntegrableOn (periodicEnergyDensity d t u) (Ioi 0) →
      (∫ s in Ioi 0, zeroEnergyDensity d t u s) =
        (∫ s in Ioi 0, periodicEnergyDensity d t u s) +
          cutoffBoundaryPair d t 0 u) := by
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  let F := zeroEnergyDensity d t u
  let G := periodicEnergyDensity d t u
  let b := cutoffBoundaryPair d t 0 u
  have hc : AECover μ atTop (fun n : ℕ => Ioi (cutoff n)) :=
    aecover_Ioi_of_Ioi cutoff_tendsto
  have hrestrict (n : ℕ) : μ.restrict (Ioi (cutoff n)) =
      volume.restrict (Ioi (cutoff n)) := by
    exact Measure.restrict_restrict_of_subset
      (fun _ hs => (cutoff_pos n).trans hs)
  have hFcut (n : ℕ) : IntegrableOn F (Ioi (cutoff n)) μ := by
    change Integrable F (μ.restrict (Ioi (cutoff n)))
    rw [hrestrict]
    exact hcut0 _ (cutoff_pos n)
  have hGcut (n : ℕ) : IntegrableOn G (Ioi (cutoff n)) μ := by
    change Integrable G (μ.restrict (Ioi (cutoff n)))
    rw [hrestrict]
    exact hcutP _ (cutoff_pos n)
  have hFnonneg : ∀ᵐ s ∂μ, 0 ≤ F s := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
    exact mul_nonneg (density_nonneg hs)
      (integral_nonneg fun x => Complex.normSq_nonneg _)
  have hGnonneg : ∀ᵐ s ∂μ, 0 ≤ G s := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
    exact mul_nonneg (density_nonneg hs)
      (integral_nonneg fun x => Complex.normSq_nonneg _)
  have hid (n : ℕ) : (∫ s in Ioi (cutoff n), F s ∂μ) =
      (∫ s in Ioi (cutoff n), G s ∂μ) +
        cutoffBoundaryPair d t (cutoff n) u := by
    simp only [hrestrict]
    exact hfinite _ (cutoff_pos n)
  have hforward (hG : Integrable G μ) :
      Integrable F μ ∧ (∫ s, F s ∂μ) = (∫ s, G s ∂μ) + b := by
    have hlim : Tendsto (fun n => ∫ s in Ioi (cutoff n), F s ∂μ)
        atTop (𝓝 ((∫ s, G s ∂μ) + b)) := by
      simpa only [hid] using
        (hc.integral_tendsto_of_countably_generated hG).add hboundary
    have hF : Integrable F μ :=
      hc.integrable_of_integral_tendsto_of_nonneg_ae
        ((∫ s, G s ∂μ) + b) hFcut hFnonneg hlim
    exact ⟨hF, hc.integral_eq_of_tendsto _ hF hlim⟩
  have hbackward (hF : Integrable F μ) : Integrable G μ := by
    have hid' (n : ℕ) : (∫ s in Ioi (cutoff n), F s ∂μ) -
        cutoffBoundaryPair d t (cutoff n) u =
          (∫ s in Ioi (cutoff n), G s ∂μ) := by
      rw [hid]
      ring
    have hlim : Tendsto (fun n => ∫ s in Ioi (cutoff n), G s ∂μ)
        atTop (𝓝 ((∫ s, F s ∂μ) - b)) := by
      simpa only [hid'] using
        (hc.integral_tendsto_of_countably_generated hF).sub hboundary
    exact hc.integrable_of_integral_tendsto_of_nonneg_ae
      ((∫ s, F s ∂μ) - b) hGcut hGnonneg hlim
  exact ⟨⟨hbackward, fun hG => (hforward hG).1⟩,
    fun hG => (hforward hG).2⟩

end D5.S3.Weil.ZetaGamma.FormCore.DomainPassage

namespace D5.S3.Weil.ZetaGamma.FormCore.DomainPassage

open Filter
open scoped Topology ComplexConjugate

theorem actual_centered_gamma_full_domain_equivalence
    (a : ℝ) (ha : 0 < a) (u : ℝ → ℂ)
    (hu : MemLp u 2 (volume.restrict (Ioc (-a) a))) :
    letI : Fact (0 < 2 * a) := ⟨by linarith⟩
    (IntegrableOn (zeroEnergyDensity (2 * a) (-a) u) (Ioi 0) ↔
      IntegrableOn (periodicEnergyDensity (2 * a) (-a) u) (Ioi 0)) ∧
    (IntegrableOn (periodicEnergyDensity (2 * a) (-a) u) (Ioi 0) →
      (∫ s in Ioi 0, zeroEnergyDensity (2 * a) (-a) u s) =
        (∫ s in Ioi 0, periodicEnergyDensity (2 * a) (-a) u s) +
          cutoffBoundaryPair (2 * a) (-a) 0 u) := by
  letI : Fact (0 < 2 * a) := ⟨by linarith⟩
  have hend : -a + 2 * a = a := by ring
  have hWindow :
      D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.windowMeasure (2 * a) (-a) =
        volume.restrict (Ioc (-a) a) := by
    simp only [D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.windowMeasure, hend]
  have huCommon : MemLp u 2
      (D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.windowMeasure (2 * a) (-a)) := by
    rw [hWindow]
    exact hu
  have hCommon (ε : ℝ) (hε : 0 < ε) :=
    D5.S3.Weil.ZetaGamma.FormCore.CommonCutoff.actual_common_cutoff_integrable_and_identity
      (2 * a) (-a) ε hε u huCommon
  have hcut0 : ∀ ε : ℝ, 0 < ε →
      IntegrableOn (zeroEnergyDensity (2 * a) (-a) u) (Ioi ε) := by
    intro ε hε
    change IntegrableOn
      (fun s => D5.S3.Weil.ZetaGamma.FormCore.CommonCutoff.density s *
        D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.zeroTranslationEnergy (2 * a) (-a) u s)
      (Ioi ε)
    exact (hCommon ε hε).1
  have hcutP : ∀ ε : ℝ, 0 < ε →
      IntegrableOn (periodicEnergyDensity (2 * a) (-a) u) (Ioi ε) := by
    intro ε hε
    change IntegrableOn
      (fun s => D5.S3.Weil.ZetaGamma.FormCore.CommonCutoff.density s *
        D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.periodicTranslationEnergy (2 * a) (-a) u s)
      (Ioi ε)
    exact (hCommon ε hε).2.1

  have hKernel (ε : ℝ) (p : ℝ × ℝ) :
      (∑' m : ℤ, if m = 0 then (0 : ℂ) else
        (cutoffKernel ε (p.1 - p.2 + m • (2 * a)) : ℂ)) =
      (D5.S3.Weil.ZetaGamma.FormCore.CommonCutoff.imageKernel
        (2 * a) ε p.1 p.2 : ℂ) := by
    unfold D5.S3.Weil.ZetaGamma.FormCore.CommonCutoff.imageKernel
    rw [Complex.ofReal_tsum]
    apply tsum_congr
    intro m
    by_cases hm : m = 0 <;>
      simp [hm, cutoffKernel, D5.S3.Weil.ZetaGamma.FormCore.CommonCutoff.cutoffKernel]
  have hBoundary_common (ε : ℝ) :
      cutoffBoundaryPair (2 * a) (-a) ε u =
        (∫ p : ℝ × ℝ, conj (u p.1) *
          (D5.S3.Weil.ZetaGamma.FormCore.CommonCutoff.imageKernel
            (2 * a) ε p.1 p.2 : ℂ) * u p.2
          ∂(D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.windowMeasure (2 * a) (-a)).prod
            (D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.windowMeasure (2 * a) (-a))).re := by
    simp only [cutoffBoundaryPair, hKernel, intervalMeasure,
      D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.windowMeasure]
  have hfinite : ∀ ε : ℝ, 0 < ε →
      (∫ s in Ioi ε, zeroEnergyDensity (2 * a) (-a) u s) =
        (∫ s in Ioi ε, periodicEnergyDensity (2 * a) (-a) u s) +
          cutoffBoundaryPair (2 * a) (-a) ε u := by
    intro ε hε
    rw [hBoundary_common]
    change D5.S3.Weil.ZetaGamma.FormCore.CommonCutoff.zeroCutoffEnergy (2 * a) (-a) ε u =
      D5.S3.Weil.ZetaGamma.FormCore.CommonCutoff.periodicCutoffEnergy (2 * a) (-a) ε u +
        (∫ p : ℝ × ℝ, conj (u p.1) *
          (D5.S3.Weil.ZetaGamma.FormCore.CommonCutoff.imageKernel (2 * a) ε p.1 p.2 : ℂ) *
          u p.2 ∂(D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.windowMeasure (2 * a) (-a)).prod
            (D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.windowMeasure (2 * a) (-a))).re
    exact (hCommon ε hε).2.2.2
  have hBoundary_eq (ε : ℝ) : cutoffBoundaryPair (2 * a) (-a) ε u =
      D5.S3.Weil.ZetaGamma.FormCore.Corner.actualIocBoundaryPair a ε u := by
    have hSum (p : ℝ × ℝ) :
        (∑' m : ℤ, if m = 0 then (0 : ℂ) else
          (cutoffKernel ε (p.1 - p.2 + m • (2 * a)) : ℂ)) =
        ∑' m : ℤ, if m = 0 then (0 : ℂ) else
          if ε < |p.1 - p.2 + m • (2 * a)| then
            (D5.S3.Weil.ZetaGamma.FormCore.Corner.actualDensity
              |p.1 - p.2 + m • (2 * a)| : ℂ) else 0 := by
      apply tsum_congr
      intro m
      by_cases hm : m = 0
      · simp only [hm, if_true]
      · simp only [if_neg hm, cutoffKernel, density,
          D5.S3.Weil.ZetaGamma.FormCore.Corner.actualDensity]
        split_ifs <;> rfl
    simp only [cutoffBoundaryPair, hSum, intervalMeasure,
      D5.S3.Weil.ZetaGamma.FormCore.Corner.actualIocBoundaryPair, hend]
  have hboundary : Tendsto
      (fun n : ℕ => cutoffBoundaryPair (2 * a) (-a) (cutoff n) u)
      atTop (𝓝 (cutoffBoundaryPair (2 * a) (-a) 0 u)) := by
    simpa only [hBoundary_eq, cutoff] using
      D5.S3.Weil.ZetaGamma.FormCore.Corner.actualIocBoundaryPair_nat_tendsto a ha hu
  exact actual_nonnegative_energy_domain_passage (2 * a) (-a) u
    hcut0 hcutP hfinite hboundary

/-- Quantitative boundary control on the original centered carrier. -/
theorem actual_centered_cutoffBoundaryPair_abs_le
    (a ε : ℝ) (ha : 0 < a) {u : ℝ → ℂ}
    (hu : MemLp u 2 (volume.restrict (Ioc (-a) a))) :
    |cutoffBoundaryPair (2 * a) (-a) ε u| ≤
      (2 * D5.S3.Weil.ZetaGamma.FormCore.Corner.gammaCk * Real.pi +
        4 * a * Real.exp (-a) /
          ((1 - Real.exp (-a)) * (1 - Real.exp (-4 * a)))) *
      (∫ x, ‖u x‖ ^ 2 ∂(volume.restrict (Ioc (-a) a))) := by
  have hend : -a + 2 * a = a := by ring
  have hSum (p : ℝ × ℝ) :
      (∑' m : ℤ, if m = 0 then (0 : ℂ) else
        (cutoffKernel ε (p.1 - p.2 + m • (2 * a)) : ℂ)) =
      ∑' m : ℤ, if m = 0 then (0 : ℂ) else
        if ε < |p.1 - p.2 + m • (2 * a)| then
          (D5.S3.Weil.ZetaGamma.FormCore.Corner.actualDensity
            |p.1 - p.2 + m • (2 * a)| : ℂ) else 0 := by
    apply tsum_congr
    intro m
    by_cases hm : m = 0
    · simp only [hm, if_true]
    · simp only [if_neg hm, cutoffKernel, density,
        D5.S3.Weil.ZetaGamma.FormCore.Corner.actualDensity]
      split_ifs <;> rfl
  simpa only [cutoffBoundaryPair, hSum, intervalMeasure,
    D5.S3.Weil.ZetaGamma.FormCore.Corner.actualIocBoundaryPair, hend] using
    D5.S3.Weil.ZetaGamma.FormCore.Corner.actualIocBoundaryPair_abs_le a ε ha hu

/-- Periodic Fourier-tail energy controls actual zero-extension energy. -/
theorem actual_centered_gamma_energy_upper_bound
    (a : ℝ) (ha : 0 < a) (u : ℝ → ℂ)
    (hu : MemLp u 2 (volume.restrict (Ioc (-a) a))) :
    letI : Fact (0 < 2 * a) := ⟨by linarith⟩
    IntegrableOn (periodicEnergyDensity (2 * a) (-a) u) (Ioi 0) →
      (∫ s in Ioi 0, zeroEnergyDensity (2 * a) (-a) u s) ≤
        (∫ s in Ioi 0, periodicEnergyDensity (2 * a) (-a) u s) +
        (2 * D5.S3.Weil.ZetaGamma.FormCore.Corner.gammaCk * Real.pi +
          4 * a * Real.exp (-a) /
            ((1 - Real.exp (-a)) * (1 - Real.exp (-4 * a)))) *
        (∫ x, ‖u x‖ ^ 2 ∂(volume.restrict (Ioc (-a) a))) := by
  letI : Fact (0 < 2 * a) := ⟨by linarith⟩
  intro hperiodic
  rw [(actual_centered_gamma_full_domain_equivalence a ha u hu).2 hperiodic]
  exact add_le_add le_rfl
    ((le_abs_self _).trans (actual_centered_cutoffBoundaryPair_abs_le a 0 ha hu))

end D5.S3.Weil.ZetaGamma.FormCore.DomainPassage
