/- GID: D5/S3/Weil/ZetaGamma/FormCore/EvenCore
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaGamma/FormCore/EvenCore
   mirror-E: none(waiver:analytic-Gamma-form-core)
   anchors: []
   utility: none
   digest: AE-even compact core in the canonical bundled Weil test carrier. -/


import D5.S3.Weil.PrimePoleTerms
import D5.S3.Weil.TestFunctions.ConvolutionSquarePositivity
import D5.S3.Weil.ZetaBridge.ClassicExplicitFormula
import D5.S3.Weil.ZetaCore.ExplicitFormulaBridge
import D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition
import D5.S3.Weil.ZetaGamma.FormCore.DirectionalEnergy
import D5.S3.Weil.ZetaGamma.FormCore.ExteriorBudget
import D5.S3.Weil.ZetaGamma.FormCore.InteriorApproximation
import D5.S3.Weil.ZetaGamma.FormCore.Mollifier
import D5.S3.Weil.ZetaGamma.FormCore.SmoothCore
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
open scoped ENNReal Topology

private def coreReflect (F : ℝ → ℂ) : ℝ → ℂ := fun x => F (-x)

private def coreEvenPart (F : ℝ → ℂ) : ℝ → ℂ :=
  fun x => (1 / 2 : ℂ) * (F x + coreReflect F x)

private theorem coreL2Mass_reflect (F : ℝ → ℂ) :
    coreL2Mass (coreReflect F) = coreL2Mass F := by
  change (∫⁻ x : ℝ, ‖F (-x)‖ₑ ^ 2 ∂volume) =
    ∫⁻ x : ℝ, ‖F x‖ₑ ^ 2 ∂volume
  exact lintegral_neg_eq_self (μ := (volume : Measure ℝ))
    (fun x : ℝ => ‖F x‖ₑ ^ 2)

private theorem coreDirectionalEnergy_reflect (nu : Measure ℝ) (F : ℝ → ℂ) :
    directionalEnergy nu (coreReflect F) = directionalEnergy nu F := by
  unfold directionalEnergy
  apply lintegral_congr_ae
  exact Eventually.of_forall fun s => by
    calc
      (∫⁻ x : ℝ, ‖coreReflect F x - coreReflect F (x - s)‖ₑ ^ 2) =
          ∫⁻ x : ℝ, ‖F ((s - x) - s) - F (s - x)‖ₑ ^ 2 := by
        apply lintegral_congr_ae
        exact Eventually.of_forall fun x => by
          have h₁ : (s - x) - s = -x := by ring
          have h₂ : -(x - s) = s - x := by ring
          simp only [coreReflect, h₁, h₂]
      _ = ∫⁻ x : ℝ, ‖F (x - s) - F x‖ₑ ^ 2 :=
        lintegral_sub_left_eq_self (μ := (volume : Measure ℝ))
          (fun x : ℝ => ‖F (x - s) - F x‖ₑ ^ 2) s
      _ = ∫⁻ x : ℝ, ‖F x - F (x - s)‖ₑ ^ 2 := by
        apply lintegral_congr_ae
        exact Eventually.of_forall fun x => by
          change ‖F (x - s) - F x‖ₑ ^ 2 = ‖F x - F (x - s)‖ₑ ^ 2
          rw [show F (x - s) - F x = -(F x - F (x - s)) by ring, enorm_neg]

private theorem coreGraphSize_reflect (nu : Measure ℝ) (F : ℝ → ℂ) :
    coreGraphSize nu (coreReflect F) = coreGraphSize nu F := by
  simp only [coreGraphSize, coreL2Mass_reflect, coreDirectionalEnergy_reflect]

private theorem coreL2Mass_const_mul (c : ℂ) (F : ℝ → ℂ) :
    coreL2Mass (fun x => c * F x) = ‖c‖ₑ ^ 2 * coreL2Mass F := by
  unfold coreL2Mass
  simp_rw [enorm_mul, mul_pow]
  exact lintegral_const_mul' (μ := (volume : Measure ℝ))
    (‖c‖ₑ ^ 2) (fun x : ℝ => ‖F x‖ₑ ^ 2)
    (ENNReal.pow_ne_top (enorm_ne_top (x := c)))

private theorem coreDirectionalEnergy_const_mul
    (nu : Measure ℝ) (c : ℂ) (F : ℝ → ℂ) :
    directionalEnergy nu (fun x => c * F x) =
      ‖c‖ₑ ^ 2 * directionalEnergy nu F := by
  have hc : ‖c‖ₑ ^ 2 ≠ (⊤ : ℝ≥0∞) :=
    ENNReal.pow_ne_top (enorm_ne_top (x := c))
  unfold directionalEnergy
  simp_rw [← mul_sub, enorm_mul, mul_pow,
    lintegral_const_mul' (μ := (volume : Measure ℝ)) (‖c‖ₑ ^ 2) _ hc]
  exact lintegral_const_mul' (μ := nu) (‖c‖ₑ ^ 2) _ hc

private theorem coreGraphSize_const_mul (nu : Measure ℝ) (c : ℂ) (F : ℝ → ℂ) :
    coreGraphSize nu (fun x => c * F x) = ‖c‖ₑ ^ 2 * coreGraphSize nu F := by
  simp only [coreGraphSize, coreL2Mass_const_mul,
    coreDirectionalEnergy_const_mul, mul_add]

private theorem coreGraphSize_evenPart_le
    (nu : Measure ℝ) (F : ℝ → ℂ) (hF : Measurable F) :
    coreGraphSize nu (coreEvenPart F) ≤ coreGraphSize nu F := by
  have hRF : Measurable (coreReflect F) := hF.comp measurable_neg
  have hnorm : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by
    rw [norm_div]
    norm_num
  have hq : ‖(1 / 2 : ℂ)‖ₑ ^ 2 = ENNReal.ofReal (1 / 4 : ℝ) := by
    calc
      ‖(1 / 2 : ℂ)‖ₑ ^ 2 = ENNReal.ofReal (1 / 2 : ℝ) ^ 2 := by
        rw [← ofReal_norm, hnorm]
      _ = ENNReal.ofReal ((1 / 2 : ℝ) ^ 2) :=
        (ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 2) 2).symm
      _ = ENNReal.ofReal (1 / 4 : ℝ) := congrArg ENNReal.ofReal (by norm_num)
  have hcoeff : ENNReal.ofReal (1 / 4 : ℝ) * 2 +
      ENNReal.ofReal (1 / 4 : ℝ) * 2 = (1 : ℝ≥0∞) := by
    have hreal : (1 / 4 : ℝ) * 2 + (1 / 4 : ℝ) * 2 = 1 := by norm_num
    have hnonneg : (0 : ℝ) ≤ (1 / 4 : ℝ) * 2 := by norm_num
    simpa only [ENNReal.ofReal_add hnonneg hnonneg,
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 4),
      ENNReal.ofReal_ofNat, ENNReal.ofReal_one] using congrArg ENNReal.ofReal hreal
  calc
    coreGraphSize nu (coreEvenPart F) = ENNReal.ofReal (1 / 4 : ℝ) *
        coreGraphSize nu (fun x => F x + coreReflect F x) := by
      change coreGraphSize nu (fun x => (1 / 2 : ℂ) * (F x + coreReflect F x)) = _
      rw [coreGraphSize_const_mul, hq]
    _ ≤ ENNReal.ofReal (1 / 4 : ℝ) *
        (2 * coreGraphSize nu F + 2 * coreGraphSize nu (coreReflect F)) :=
      mul_le_mul_of_nonneg_left (coreGraphSize_add_le nu F (coreReflect F) hF hRF)
        (by positivity)
    _ = (ENNReal.ofReal (1 / 4 : ℝ) * 2 +
        ENNReal.ofReal (1 / 4 : ℝ) * 2) * coreGraphSize nu F := by
      rw [coreGraphSize_reflect]
      ring
    _ = coreGraphSize nu F := by rw [hcoeff, one_mul]

private theorem coreEvenPart_contDiff {H : ℝ → ℂ} (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (coreEvenPart H) := by
  change ContDiff ℝ ∞ (fun x : ℝ => (1 / 2 : ℂ) * (H x + H (-x)))
  exact contDiff_const.mul (hH.add (hH.comp contDiff_neg))

private theorem coreEvenPart_hasCompactSupport {H : ℝ → ℂ}
    (hH : HasCompactSupport H) : HasCompactSupport (coreEvenPart H) := by
  have hneg : HasCompactSupport (coreReflect H) := by
    change HasCompactSupport (H ∘ (Homeomorph.neg ℝ))
    exact hH.comp_homeomorph (Homeomorph.neg ℝ)
  change HasCompactSupport
    ((fun _ : ℝ => (1 / 2 : ℂ)) * (H + coreReflect H))
  exact (hH.add hneg).mul_left (f := fun _ : ℝ => (1 / 2 : ℂ))

private theorem coreEvenPart_even (H : ℝ → ℂ) (x : ℝ) :
    coreEvenPart H (-x) = coreEvenPart H x := by
  simp only [coreEvenPart, coreReflect, neg_neg, add_comm]

private theorem coreEvenPart_tsupport_subset {H : ℝ → ℂ} {a : ℝ}
    (hH : tsupport H ⊆ Ioo (-a) a) :
    tsupport (coreEvenPart H) ⊆ Ioo (-a) a := by
  have hneg : tsupport (coreReflect H) ⊆ Ioo (-a) a := by
    intro x hx
    have hpre : tsupport (coreReflect H) =
        (Homeomorph.neg ℝ) ⁻¹' tsupport H := by
      change tsupport (H ∘ (Homeomorph.neg ℝ)) =
        (Homeomorph.neg ℝ) ⁻¹' tsupport H
      exact tsupport_comp_eq_preimage H (Homeomorph.neg ℝ)
    rw [hpre] at hx
    change -x ∈ tsupport H at hx
    have hnx : -x ∈ Ioo (-a) a := hH hx
    exact ⟨by linarith [hnx.2], by linarith [hnx.1]⟩
  have hsum : tsupport (fun x : ℝ => H x + coreReflect H x) ⊆ Ioo (-a) a :=
    (tsupport_add H (coreReflect H)).trans (union_subset hH hneg)
  change tsupport (fun x : ℝ => (1 / 2 : ℂ) * (H x + coreReflect H x)) ⊆ Ioo (-a) a
  exact (tsupport_mul_subset_right
    (f := fun _ : ℝ => (1 / 2 : ℂ))
    (g := fun x : ℝ => H x + coreReflect H x)).trans hsum

private def coreEvenWeilTest (H : ℝ → ℂ)
    (hHs : ContDiff ℝ ∞ H) (hHc : HasCompactSupport H) :
    D5.S3.Weil.TestFunctions.WeilTestFunction where
  toFun := coreEvenPart H
  contDiff' := coreEvenPart_contDiff hHs
  hasCompactSupport' := coreEvenPart_hasCompactSupport hHc
  even' := coreEvenPart_even H

private theorem coreGraphSize_evenPart_error_le
    (nu : Measure ℝ) (F H : ℝ → ℂ)
    (hF : Measurable F) (hH : Measurable H)
    (heven : ∀ᵐ x : ℝ ∂volume, F (-x) = F x) :
    coreGraphSize nu (fun x => coreEvenPart H x - F x) ≤
      coreGraphSize nu (fun x => H x - F x) := by
  have herr : (fun x => coreEvenPart H x - F x) =ᵐ[volume]
      coreEvenPart (fun x => H x - F x) := by
    filter_upwards [heven] with x hx
    dsimp only [coreEvenPart, coreReflect]
    rw [hx]
    ring
  rw [coreGraphSize_congr_ae nu herr]
  exact coreGraphSize_evenPart_le nu _ (hH.sub hF)

private theorem core_ae_even_transfer
    {F M : ℝ → ℂ} (hFM : F =ᵐ[volume] M)
    (heven : ∀ᵐ x : ℝ ∂volume, F (-x) = F x) :
    ∀ᵐ x : ℝ ∂volume, M (-x) = M x := by
  have hneg : (fun x : ℝ => F (-x)) =ᵐ[volume] (fun x : ℝ => M (-x)) := by
    simpa only [Function.comp_def] using
      (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae_eq_comp hFM
  filter_upwards [hFM, hneg, heven] with x hx hnx hex
  exact hnx.symm.trans (hex.trans hx)

theorem actual_ioc_exists_weil_test_core_approximation
    (a : ℝ) (u : ℝ → ℂ)
    (hu : MemLp u 2 (volume.restrict (Ioc (-a) a)))
    (henergy : directionalEnergy actualGammaExitMeasure
      (D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.zeroExtension (2 * a) (-a) u) < (⊤ : ℝ≥0∞))
    (heven : ∀ᵐ x : ℝ ∂volume,
      D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.zeroExtension (2 * a) (-a) u (-x) =
        D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.zeroExtension (2 * a) (-a) u x)
    (ε : ℝ) (hε : 0 < ε) :
    let F := D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.zeroExtension (2 * a) (-a) u
    ∃ g : D5.S3.Weil.TestFunctions.WeilTestFunction,
      tsupport (g : ℝ → ℂ) ⊆ Ioo (-a) a ∧
      coreL2Mass (fun x => g x - F x) +
        directionalEnergy actualGammaExitMeasure (fun x => g x - F x) <
          ENNReal.ofReal ε := by
  dsimp only
  let F := D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.zeroExtension (2 * a) (-a) u
  obtain ⟨H, hHs, hHc, hHsupport, hHerror⟩ :=
    actual_ioc_exists_smooth_compact_core_approximation a u hu henergy ε hε
  obtain ⟨M, hM, _hM₂, _hMzero, hFM, _hmass, _hmassIoc, _henergyEq⟩ :=
    actual_ioc_exists_measurable_zero_supported_energy_representative a u hu
  have hMeven : ∀ᵐ x : ℝ ∂volume, M (-x) = M x :=
    core_ae_even_transfer hFM heven
  have hHFM : (fun x => H x - F x) =ᵐ[volume] (fun x => H x - M x) := by
    filter_upwards [hFM] with x hx
    dsimp only [F]
    rw [hx]
  have hJFM : (fun x => coreEvenPart H x - F x) =ᵐ[volume]
      (fun x => coreEvenPart H x - M x) := by
    filter_upwards [hFM] with x hx
    dsimp only [F]
    rw [hx]
  refine ⟨coreEvenWeilTest H hHs hHc, coreEvenPart_tsupport_subset hHsupport, ?_⟩
  change coreGraphSize actualGammaExitMeasure (fun x => coreEvenPart H x - F x) <
    ENNReal.ofReal ε
  calc
    _ = coreGraphSize actualGammaExitMeasure (fun x => coreEvenPart H x - M x) :=
      coreGraphSize_congr_ae actualGammaExitMeasure hJFM
    _ ≤ coreGraphSize actualGammaExitMeasure (fun x => H x - M x) :=
      coreGraphSize_evenPart_error_le actualGammaExitMeasure M H hM
        hHs.continuous.measurable hMeven
    _ = coreGraphSize actualGammaExitMeasure (fun x => H x - F x) :=
      (coreGraphSize_congr_ae actualGammaExitMeasure hHFM).symm
    _ < ENNReal.ofReal ε := hHerror

end D5.S3.Weil.ZetaGamma.FormCore
