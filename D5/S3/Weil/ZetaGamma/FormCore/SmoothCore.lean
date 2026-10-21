/- GID: D5/S3/Weil/ZetaGamma/FormCore/SmoothCore
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaGamma/FormCore/SmoothCore
   mirror-E: none(waiver:analytic-Gamma-form-core)
   anchors: []
   utility: none
   digest: Diagonal smooth compact core on the original Ioc domain. -/


import D5.S3.Weil.PrimePoleTerms
import D5.S3.Weil.TestFunctions.ConvolutionSquarePositivity
import D5.S3.Weil.ZetaBridge.ClassicExplicitFormula
import D5.S3.Weil.ZetaCore.ExplicitFormulaBridge
import D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition
import D5.S3.Weil.ZetaGamma.FormCore.CutoffConvergence
import D5.S3.Weil.ZetaGamma.FormCore.CutoffSupport
import D5.S3.Weil.ZetaGamma.FormCore.DirectionalEnergy
import D5.S3.Weil.ZetaGamma.FormCore.ExteriorBudget
import D5.S3.Weil.ZetaGamma.FormCore.InteriorApproximation
import D5.S3.Weil.ZetaGamma.FormCore.LineFourier
import D5.S3.Weil.ZetaGamma.FormCore.Mollifier
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
open D5.S3.Weil.ZetaGamma.FormCore.LineFourier
open scoped ENNReal Topology

def coreGraphSize (nu : Measure ℝ) (F : ℝ → ℂ) : ℝ≥0∞ :=
  coreL2Mass F + directionalEnergy nu F

private theorem coreComplexAdd_enorm_sq_le (z w : ℂ) :
    ‖z + w‖ₑ ^ 2 ≤ 2 * ‖z‖ₑ ^ 2 + 2 * ‖w‖ₑ ^ 2 := by
  have h := ENNReal.ofReal_le_ofReal (complex_norm_add_sq_le z w)
  rw [ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num),
    ENNReal.ofReal_pow (norm_nonneg _) 2,
    ENNReal.ofReal_pow (norm_nonneg _) 2,
    ENNReal.ofReal_pow (norm_nonneg _) 2] at h
  simpa only [ofReal_norm, ENNReal.ofReal_ofNat] using h

private theorem coreL2Mass_add_le
    (F G : ℝ → ℂ) (hF : Measurable F) (hG : Measurable G) :
    coreL2Mass (fun x => F x + G x) ≤ 2 * coreL2Mass F + 2 * coreL2Mass G := by
  calc
    _ ≤ ∫⁻ x : ℝ, 2 * ‖F x‖ₑ ^ 2 + 2 * ‖G x‖ₑ ^ 2 :=
      lintegral_mono fun x => coreComplexAdd_enorm_sq_le (F x) (G x)
    _ = _ := by
      simp only [coreL2Mass]
      calc
        _ = (∫⁻ x : ℝ, 2 * ‖F x‖ₑ ^ 2) +
            ∫⁻ x : ℝ, 2 * ‖G x‖ₑ ^ 2 :=
          lintegral_add_left' ((measurable_const.mul (hF.enorm.pow_const 2)).aemeasurable) _
        _ = _ := by
          rw [lintegral_const_mul' _ _ (by norm_num),
            lintegral_const_mul' _ _ (by norm_num)]

private theorem coreDirectionalEnergy_add_le
    (nu : Measure ℝ) (F G : ℝ → ℂ) (hF : Measurable F) (hG : Measurable G) :
    directionalEnergy nu (fun x => F x + G x) ≤
      2 * directionalEnergy nu F + 2 * directionalEnergy nu G := by
  let DF (s x : ℝ) : ℂ := F x - F (x - s)
  let DG (s x : ℝ) : ℂ := G x - G (x - s)
  have hDF (s : ℝ) : Measurable (DF s) :=
    hF.sub (hF.comp (measurable_id.sub_const s))
  have hDG (s : ℝ) : Measurable (DG s) :=
    hG.sub (hG.comp (measurable_id.sub_const s))
  have hDFmass : Measurable (fun s : ℝ => coreL2Mass (DF s)) := by
    have hm : Measurable (fun p : ℝ × ℝ => ‖DF p.1 p.2‖ₑ ^ 2) := by
      dsimp only [DF]
      fun_prop
    exact hm.lintegral_prod_right'
  have hslice (s : ℝ) :
      (∫⁻ x : ℝ, ‖(F x + G x) - (F (x - s) + G (x - s))‖ₑ ^ 2) ≤
        2 * coreL2Mass (DF s) + 2 * coreL2Mass (DG s) := by
    calc
      _ = coreL2Mass (fun x => DF s x + DG s x) := by
        apply lintegral_congr_ae
        exact Eventually.of_forall fun x => by
          dsimp only [DF, DG]
          rw [show (F x + G x) - (F (x - s) + G (x - s)) =
            (F x - F (x - s)) + (G x - G (x - s)) by ring]
      _ ≤ _ := coreL2Mass_add_le (DF s) (DG s) (hDF s) (hDG s)
  calc
    _ ≤ ∫⁻ s : ℝ, (2 * coreL2Mass (DF s) + 2 * coreL2Mass (DG s)) ∂nu :=
      lintegral_mono hslice
    _ = _ := by
      simp only [directionalEnergy, coreL2Mass]
      calc
        _ = (∫⁻ s : ℝ, 2 * coreL2Mass (DF s) ∂nu) +
            ∫⁻ s : ℝ, 2 * coreL2Mass (DG s) ∂nu :=
          lintegral_add_left' ((measurable_const.mul hDFmass).aemeasurable) _
        _ = _ := by
          rw [lintegral_const_mul' _ _ (by norm_num),
            lintegral_const_mul' _ _ (by norm_num)]
          simp only [coreL2Mass, DF, DG]

theorem coreGraphSize_add_le
    (nu : Measure ℝ) (F G : ℝ → ℂ) (hF : Measurable F) (hG : Measurable G) :
    coreGraphSize nu (fun x => F x + G x) ≤
      2 * coreGraphSize nu F + 2 * coreGraphSize nu G := by
  calc
    _ ≤ (2 * coreL2Mass F + 2 * coreL2Mass G) +
        (2 * directionalEnergy nu F + 2 * directionalEnergy nu G) :=
      add_le_add (coreL2Mass_add_le F G hF hG)
        (coreDirectionalEnergy_add_le nu F G hF hG)
    _ = _ := by unfold coreGraphSize; ring

theorem coreGraphSize_congr_ae
    (nu : Measure ℝ) {F G : ℝ → ℂ} (hFG : F =ᵐ[volume] G) :
    coreGraphSize nu F = coreGraphSize nu G := by
  have hm : coreL2Mass F = coreL2Mass G := by
    apply lintegral_congr_ae
    filter_upwards [hFG] with x hx
    rw [hx]
  exact congrArg₂ (fun u v : ℝ≥0∞ => u + v) hm (directionalEnergy_congr_ae nu hFG)

private theorem core_eighth_budget {ε : ℝ} (hε : 0 < ε) :
    (2 : ℝ≥0∞) * ENNReal.ofReal (ε / 8) +
      2 * ENNReal.ofReal (ε / 8) < ENNReal.ofReal ε := by
  calc
    _ = ENNReal.ofReal (2 * (ε / 8) + 2 * (ε / 8)) := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_mul (by positivity)]
      norm_num
    _ < _ := (ENNReal.ofReal_lt_ofReal_iff hε).mpr (by linarith)

theorem actual_ioc_exists_smooth_compact_core_approximation
    (a : ℝ) (u : ℝ → ℂ)
    (hu : MemLp u 2 (volume.restrict (Ioc (-a) a)))
    (henergy : directionalEnergy actualGammaExitMeasure
      (D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.zeroExtension (2 * a) (-a) u) < (⊤ : ℝ≥0∞))
    (ε : ℝ) (hε : 0 < ε) :
    let F := D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.zeroExtension (2 * a) (-a) u
    ∃ H : ℝ → ℂ, ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧
      tsupport H ⊆ Ioo (-a) a ∧
      coreL2Mass (fun x => H x - F x) +
        directionalEnergy actualGammaExitMeasure (fun x => H x - F x) <
          ENNReal.ofReal ε := by
  dsimp only
  let F := D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.zeroExtension (2 * a) (-a) u
  obtain ⟨M, hM, hM₂, hMzero, hFM, _hmass, _hmassIoc, henergyEq⟩ :=
    actual_ioc_exists_measurable_zero_supported_energy_representative a u hu
  have hME : directionalEnergy actualGammaExitMeasure M < (⊤ : ℝ≥0∞) := by
    rw [← henergyEq]
    exact henergy
  have hMmass : coreL2Mass M < (⊤ : ℝ≥0∞) := by
    rw [coreL2Mass, squared_mass_eq_eLpNorm M hM₂.aestronglyMeasurable]
    exact ENNReal.pow_lt_top hM₂
  have hMsize : coreGraphSize actualGammaExitMeasure M < (⊤ : ℝ≥0∞) :=
    ENNReal.add_lt_top.mpr ⟨hMmass, hME⟩
  have hcutlim : Tendsto (fun δ => coreGraphSize actualGammaExitMeasure
      (fun x => (actualCutoffEta a δ x : ℂ) * M x - M x))
      (𝓝[Ioi (0 : ℝ)] 0) (𝓝 (0 : ℝ≥0∞)) :=
    (actual_gamma_interior_cutoff_form_approximation a M hM hM₂ hMzero hME).2
  have hsmall : ∀ᶠ δ : ℝ in 𝓝[Ioi (0 : ℝ)] 0,
      coreGraphSize actualGammaExitMeasure
        (fun x => (actualCutoffEta a δ x : ℂ) * M x - M x) < ENNReal.ofReal (ε / 8) :=
    hcutlim.eventually (gt_mem_nhds (by positivity : (0 : ℝ≥0∞) < ENNReal.ofReal (ε / 8)))
  have hpositive : ∀ᶠ δ : ℝ in 𝓝[Ioi (0 : ℝ)] 0, 0 < δ := self_mem_nhdsWithin
  obtain ⟨δ, hδ, hsmall⟩ := (hpositive.and hsmall).exists
  let C : ℝ → ℂ := fun x => (actualCutoffEta a δ x : ℂ) * M x
  have hCm : Measurable C :=
    (Complex.ofRealCLM.continuous.comp (actualCutoffEta_contDiff a δ).continuous).measurable.mul hM
  have hC₂ : MemLp C 2 volume := by
    apply hM₂.of_le hCm.aestronglyMeasurable
    exact Eventually.of_forall fun x => by
      change ‖(actualCutoffEta a δ x : ℂ) * M x‖ ≤ ‖M x‖
      rw [norm_mul, Complex.norm_of_nonneg (actualCutoffEta_range a δ x).1]
      calc
        _ ≤ 1 * ‖M x‖ := mul_le_mul_of_nonneg_right
          (actualCutoffEta_range a δ x).2 (norm_nonneg _)
        _ = _ := one_mul _
  have hCcompact : HasCompactSupport C := actualCutoffEta_mul_hasCompactSupport hδ M
  have hCsupport : tsupport C ⊆ Icc (-a + δ) (a - δ) :=
    actualCutoffEta_mul_tsupport_subset_Icc hδ M
  have hCerrorfin :
      coreGraphSize actualGammaExitMeasure (fun x => C x - M x) < (⊤ : ℝ≥0∞) :=
    hsmall.trans ENNReal.ofReal_lt_top
  have hCeq : C = (fun x => (C x - M x) + M x) := by
    funext x
    ring
  have hCsize : coreGraphSize actualGammaExitMeasure C < (⊤ : ℝ≥0∞) := by
    calc
      _ = coreGraphSize actualGammaExitMeasure (fun x => (C x - M x) + M x) :=
        congrArg (coreGraphSize actualGammaExitMeasure) hCeq
      _ ≤ 2 * coreGraphSize actualGammaExitMeasure (fun x => C x - M x) +
          2 * coreGraphSize actualGammaExitMeasure M :=
        coreGraphSize_add_le actualGammaExitMeasure _ _ (hCm.sub hM) hM
      _ < (⊤ : ℝ≥0∞) := ENNReal.add_lt_top.mpr
        ⟨ENNReal.mul_lt_top (by norm_num) hCerrorfin,
          ENNReal.mul_lt_top (by norm_num) hMsize⟩
  have hCE : directionalEnergy actualGammaExitMeasure C < (⊤ : ℝ≥0∞) :=
    (ENNReal.add_lt_top.mp hCsize).2
  obtain ⟨H, hHsmooth, hHcompact, hHsupport, hHsmall⟩ :=
    exists_smooth_actual_gamma_approximation_of_inward_support
      C hCm hC₂ hCcompact hCE a δ hδ hCsupport (ε / 8) (by positivity)
  have hHM : coreGraphSize actualGammaExitMeasure (fun x => H x - M x) <
      ENNReal.ofReal ε := by
    have hsplit : (fun x => H x - M x) =
        (fun x => (H x - C x) + (C x - M x)) := by
      funext x
      ring
    calc
      _ = coreGraphSize actualGammaExitMeasure
          (fun x => (H x - C x) + (C x - M x)) :=
        congrArg (coreGraphSize actualGammaExitMeasure) hsplit
      _ ≤ 2 * coreGraphSize actualGammaExitMeasure (fun x => H x - C x) +
          2 * coreGraphSize actualGammaExitMeasure (fun x => C x - M x) :=
        coreGraphSize_add_le actualGammaExitMeasure _ _
          (hHsmooth.continuous.measurable.sub hCm) (hCm.sub hM)
      _ ≤ 2 * ENNReal.ofReal (ε / 8) + 2 * ENNReal.ofReal (ε / 8) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left
            (by simpa [coreGraphSize] using hHsmall.le) (by norm_num))
          (mul_le_mul_of_nonneg_left hsmall.le (by norm_num))
      _ < ENNReal.ofReal ε := core_eighth_budget hε
  refine ⟨H, hHsmooth, hHcompact, hHsupport, ?_⟩
  change coreGraphSize actualGammaExitMeasure (fun x => H x - F x) < ENNReal.ofReal ε
  have herr : (fun x => H x - F x) =ᵐ[volume] (fun x => H x - M x) := by
    filter_upwards [hFM] with x hx
    dsimp only [F]
    rw [hx]
  rw [coreGraphSize_congr_ae actualGammaExitMeasure herr]
  exact hHM

theorem coreL2Mass_error_eq_original_ioc
    (a : ℝ) (u H : ℝ → ℂ) (hHsupport : tsupport H ⊆ Ioo (-a) a) :
    coreL2Mass (fun x => H x -
      D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.zeroExtension (2 * a) (-a) u x) =
        ∫⁻ x in Ioc (-a) a, ‖H x - u x‖ₑ ^ 2 := by
  have hend : -a + 2 * a = a := by ring
  calc
    _ = ∫⁻ x : ℝ, (Ioc (-a) a).indicator (fun y => ‖H y - u y‖ₑ ^ 2) x := by
      apply lintegral_congr_ae
      exact Eventually.of_forall fun x => by
        by_cases hx : x ∈ Ioc (-a) a
        · simp [D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.zeroExtension, hend, hx]
        · have hHzero : H x = 0 := by
            by_contra h
            have hi := hHsupport (subset_tsupport H h)
            exact hx ⟨hi.1, hi.2.le⟩
          simp [D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.zeroExtension, hend, hx, hHzero]
    _ = _ := lintegral_indicator measurableSet_Ioc _

end D5.S3.Weil.ZetaGamma.FormCore
