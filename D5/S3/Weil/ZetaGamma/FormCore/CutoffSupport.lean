/- GID: D5/S3/Weil/ZetaGamma/FormCore/CutoffSupport
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaGamma/FormCore/CutoffSupport
   mirror-E: none(waiver:analytic-Gamma-form-core)
   anchors: []
   utility: none
   digest: Inward cutoff support and physical mass convergence. -/


import D5.S3.Weil.PrimePoleTerms
import D5.S3.Weil.TestFunctions.ConvolutionSquarePositivity
import D5.S3.Weil.ZetaBridge.ClassicExplicitFormula
import D5.S3.Weil.ZetaCore.ExplicitFormulaBridge
import D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition
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

namespace D5.S3.Weil.ZetaGamma.FormCore.Corner

private theorem actualCutoffEta_eq_zero_of_le_left {a ε x : ℝ} (hε : 0 < ε)
    (hx : x ≤ -a + ε) : actualCutoffEta a ε x = 0 := by
  have hq : (x + a) / ε ≤ 1 := (div_le_iff₀ hε).2 (by linarith)
  have harg : (x + a) / ε - 1 ≤ 0 := by linarith
  simp only [actualCutoffEta, Real.smoothTransition.zero_of_nonpos harg, zero_mul]

private theorem actualCutoffEta_eq_zero_of_right_le {a ε x : ℝ} (hε : 0 < ε)
    (hx : a - ε ≤ x) : actualCutoffEta a ε x = 0 := by
  have hq : (a - x) / ε ≤ 1 := (div_le_iff₀ hε).2 (by linarith)
  have harg : (a - x) / ε - 1 ≤ 0 := by linarith
  simp only [actualCutoffEta, Real.smoothTransition.zero_of_nonpos harg, mul_zero]

private theorem actualCutoffEta_support_subset_Ioo {a ε : ℝ} (hε : 0 < ε) :
    Function.support (actualCutoffEta a ε) ⊆ Ioo (-a + ε) (a - ε) := by
  intro x hx
  change actualCutoffEta a ε x ≠ 0 at hx
  constructor
  · by_contra h
    exact hx (actualCutoffEta_eq_zero_of_le_left hε (not_lt.mp h))
  · by_contra h
    exact hx (actualCutoffEta_eq_zero_of_right_le hε (not_lt.mp h))

private theorem actualCutoffEta_tsupport_subset_Icc {a ε : ℝ} (hε : 0 < ε) :
    tsupport (actualCutoffEta a ε) ⊆ Icc (-a + ε) (a - ε) := by
  change closure (Function.support (actualCutoffEta a ε)) ⊆ _
  apply closure_minimal _ isClosed_Icc
  intro x hx
  have hx' := actualCutoffEta_support_subset_Ioo hε hx
  exact ⟨hx'.1.le, hx'.2.le⟩

private theorem actualCutoffEta_hasCompactSupport {a ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (actualCutoffEta a ε) := by
  change IsCompact (tsupport (actualCutoffEta a ε))
  exact isCompact_Icc.of_isClosed_subset (isClosed_tsupport _)
    (actualCutoffEta_tsupport_subset_Icc hε)

private theorem actualCutoffEta_tsupport_subset_interior {a ε : ℝ} (hε : 0 < ε) :
    tsupport (actualCutoffEta a ε) ⊆ Ioo (-a) a := by
  intro x hx
  have hx' := actualCutoffEta_tsupport_subset_Icc hε hx
  constructor <;> linarith [hx'.1, hx'.2]

private theorem actualCutoffEta_smooth_compact_interior {a ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ ∞ (actualCutoffEta a ε) ∧
      HasCompactSupport (actualCutoffEta a ε) ∧
      tsupport (actualCutoffEta a ε) ⊆ Icc (-a + ε) (a - ε) ∧
      tsupport (actualCutoffEta a ε) ⊆ Ioo (-a) a :=
  ⟨actualCutoffEta_contDiff a ε, actualCutoffEta_hasCompactSupport hε,
    actualCutoffEta_tsupport_subset_Icc hε, actualCutoffEta_tsupport_subset_interior hε⟩

private theorem actualCutoffEta_at_zero_eq_one {a ε : ℝ} (hε : 0 < ε)
    (hsmall : ε < a / 2) : actualCutoffEta a ε 0 = 1 := by
  have hq : 2 ≤ a / ε := (le_div_iff₀ hε).2 (by linarith)
  have harg : 1 ≤ a / ε - 1 := by linarith
  simp only [actualCutoffEta, zero_add, sub_zero,
    Real.smoothTransition.one_of_one_le harg, one_mul]

private theorem actualCutoffMask_support_subset (a ε : ℝ) :
    Function.support (actualCutoffMask a ε) ⊆ Ioo (-a) a := by
  intro x hx
  change actualCutoffMask a ε x ≠ 0 at hx
  by_contra hout
  exact hx (by simp only [actualCutoffMask, if_neg hout])

theorem actualCutoffEta_mul_eq_sub_mask (a ε : ℝ) (F : ℝ → ℂ)
    (hzero : ∀ x ∉ Ioo (-a) a, F x = 0) (x : ℝ) :
    (actualCutoffEta a ε x : ℂ) * F x =
      F x - (actualCutoffMask a ε x : ℂ) * F x := by
  by_cases hx : x ∈ Ioo (-a) a
  · simp only [actualCutoffMask, if_pos hx]
    push_cast
    ring
  · simp only [actualCutoffMask, if_neg hx, hzero x hx,
      mul_zero, Complex.ofReal_zero, zero_mul, sub_self]

theorem actualCutoffEta_mul_tsupport_subset_Icc {a ε : ℝ} (hε : 0 < ε)
    (F : ℝ → ℂ) :
    tsupport (fun x => (actualCutoffEta a ε x : ℂ) * F x) ⊆
      Icc (-a + ε) (a - ε) := by
  change closure (Function.support (fun x => (actualCutoffEta a ε x : ℂ) * F x)) ⊆ _
  apply closure_minimal _ isClosed_Icc
  intro x hx
  change (actualCutoffEta a ε x : ℂ) * F x ≠ 0 at hx
  have hη : actualCutoffEta a ε x ≠ 0 := by
    intro h
    exact hx (by rw [h, Complex.ofReal_zero, zero_mul])
  have hx' := actualCutoffEta_support_subset_Ioo hε hη
  exact ⟨hx'.1.le, hx'.2.le⟩

theorem actualCutoffEta_mul_hasCompactSupport {a ε : ℝ} (hε : 0 < ε)
    (F : ℝ → ℂ) :
    HasCompactSupport (fun x => (actualCutoffEta a ε x : ℂ) * F x) := by
  change IsCompact (tsupport (fun x => (actualCutoffEta a ε x : ℂ) * F x))
  exact isCompact_Icc.of_isClosed_subset (isClosed_tsupport _)
    (actualCutoffEta_mul_tsupport_subset_Icc hε F)

private theorem actualCutoffMask_mul_enorm_sq_le (a ε : ℝ) (F : ℝ → ℂ) (x : ℝ) :
    ‖(actualCutoffMask a ε x : ℂ) * F x‖ₑ ^ 2 ≤ ‖F x‖ₑ ^ 2 := by
  have hb := actualCutoffMask_range a ε x
  have hnorm : ‖(actualCutoffMask a ε x : ℂ) * F x‖ ≤ ‖F x‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb.1]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hb.2 (norm_nonneg (F x))
  exact pow_le_pow_left' (enorm_le_iff_norm_le.mpr hnorm) 2

private theorem actualCutoffMask_mul_mass_le (a ε : ℝ) (F : ℝ → ℂ) :
    (∫⁻ x : ℝ, ‖(actualCutoffMask a ε x : ℂ) * F x‖ₑ ^ 2) ≤
      ∫⁻ x : ℝ, ‖F x‖ₑ ^ 2 :=
  lintegral_mono (actualCutoffMask_mul_enorm_sq_le a ε F)

private theorem actualCutoffMask_mul_mass_tendsto_zero (a : ℝ) (F : ℝ → ℂ)
    (hF : Measurable F)
    (hmass : (∫⁻ x : ℝ, ‖F x‖ₑ ^ 2) < (⊤ : ℝ≥0∞)) :
    Tendsto (fun ε => ∫⁻ x : ℝ, ‖(actualCutoffMask a ε x : ℂ) * F x‖ₑ ^ 2)
      (𝓝[Ioi (0 : ℝ)] 0) (𝓝 0) := by
  have hmeas : ∀ ε : ℝ,
      Measurable (fun x => ‖(actualCutoffMask a ε x : ℂ) * F x‖ₑ ^ 2) := by
    intro ε
    have hb : Measurable (fun x => (actualCutoffMask a ε x : ℂ)) :=
      Complex.continuous_ofReal.measurable.comp (actualCutoffMask_measurable a ε)
    exact (hb.mul hF).enorm.pow_const 2
  have hpoint : ∀ x : ℝ,
      Tendsto (fun ε => ‖(actualCutoffMask a ε x : ℂ) * F x‖ₑ ^ 2)
        (𝓝[Ioi (0 : ℝ)] 0) (𝓝 (0 : ℝ≥0∞)) := by
    intro x
    apply tendsto_const_nhds.congr'
    change ∀ᶠ ε in 𝓝[Ioi (0 : ℝ)] 0,
      (0 : ℝ≥0∞) = ‖(actualCutoffMask a ε x : ℂ) * F x‖ₑ ^ 2
    filter_upwards [actualCutoffMask_eventually_zero a x] with ε hε
    simp only [hε, Complex.ofReal_zero, zero_mul, enorm_zero, zero_pow (by norm_num : 2 ≠ 0)]
  have hdct := tendsto_lintegral_filter_of_dominated_convergence
    (μ := (volume : Measure ℝ)) (l := 𝓝[Ioi (0 : ℝ)] 0)
    (f := fun _ : ℝ => (0 : ℝ≥0∞))
    (fun x : ℝ => ‖F x‖ₑ ^ 2)
    (Eventually.of_forall hmeas)
    (Eventually.of_forall fun ε =>
      Eventually.of_forall (actualCutoffMask_mul_enorm_sq_le a ε F))
    hmass.ne (Eventually.of_forall hpoint)
  simpa only [lintegral_zero] using hdct

private theorem actualCutoffMask_mul_mass_tendsto_zero_of_memLp (a : ℝ) (F : ℝ → ℂ)
    (hF : Measurable F) (hF₂ : MemLp F 2) :
    Tendsto (fun ε => ∫⁻ x : ℝ, ‖(actualCutoffMask a ε x : ℂ) * F x‖ₑ ^ 2)
      (𝓝[Ioi (0 : ℝ)] 0) (𝓝 0) := by
  apply actualCutoffMask_mul_mass_tendsto_zero a F hF
  have hm := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
    (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num) hF₂
  simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_two] using hm

theorem actualCutoffEta_mul_sub_mass_tendsto_zero (a : ℝ) (F : ℝ → ℂ)
    (hF : Measurable F)
    (hmass : (∫⁻ x : ℝ, ‖F x‖ₑ ^ 2) < (⊤ : ℝ≥0∞))
    (hzero : ∀ x ∉ Ioo (-a) a, F x = 0) :
    Tendsto (fun ε =>
        ∫⁻ x : ℝ, ‖(actualCutoffEta a ε x : ℂ) * F x - F x‖ₑ ^ 2)
      (𝓝[Ioi (0 : ℝ)] 0) (𝓝 0) := by
  apply (actualCutoffMask_mul_mass_tendsto_zero a F hF hmass).congr'
  exact Eventually.of_forall fun ε => by
    apply lintegral_congr_ae
    exact Eventually.of_forall fun x => by
      have hid : (actualCutoffEta a ε x : ℂ) * F x - F x =
          -((actualCutoffMask a ε x : ℂ) * F x) := by
        rw [actualCutoffEta_mul_eq_sub_mask a ε F hzero x]
        abel
      dsimp only
      rw [hid, enorm_neg]

end D5.S3.Weil.ZetaGamma.FormCore.Corner
