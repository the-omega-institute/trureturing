/- GID: D5/S3/Weil/ZetaGamma/FormCore/DirectionalEnergy
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaGamma/FormCore/DirectionalEnergy
   mirror-E: none(waiver:analytic-Gamma-form-core)
   anchors: []
   utility: none
   digest: Exit potential and cutoff product estimates. -/


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

namespace D5.S3.Weil.ZetaGamma.FormCore

def directionalEnergy (nu : Measure ℝ) (F : ℝ → ℂ) : ℝ≥0∞ :=
  ∫⁻ s : ℝ, ∫⁻ x : ℝ, ‖F x - F (x - s)‖ₑ ^ 2 ∂volume ∂nu

def exteriorExitPair (Omega : Set ℝ) (x s : ℝ) : ℝ≥0∞ :=
  (if x - s ∈ Omega then 0 else 1) +
    (if x + s ∈ Omega then 0 else 1)

def exteriorPotential (nu : Measure ℝ) (Omega : Set ℝ) (x : ℝ) : ℝ≥0∞ :=
  ∫⁻ s : ℝ, exteriorExitPair Omega x s ∂nu

private theorem exit_pair_pointwise_le (Omega : Set ℝ) (F : ℝ → ℂ)
    (hzero : ∀ x ∉ Omega, F x = 0) (x s : ℝ) :
    (if x - s ∈ Omega then 0 else ‖F x‖ₑ ^ 2) +
      (if x ∈ Omega then 0 else ‖F (x - s)‖ₑ ^ 2) ≤
        ‖F x - F (x - s)‖ₑ ^ 2 := by
  by_cases hx : x ∈ Omega
  · by_cases hy : x - s ∈ Omega
    · simp only [if_pos hx, if_pos hy, zero_add, zero_le]
    · simp [hx, hy, hzero (x - s) hy]
  · by_cases hy : x - s ∈ Omega
    · simp [hx, hy, hzero x hx]
    · simp [hx, hy, hzero x hx, hzero (x - s) hy]

private theorem exit_pair_lintegral_le (Omega : Set ℝ)
    (hOmega : MeasurableSet Omega) (F : ℝ → ℂ) (hF : Measurable F)
    (hzero : ∀ x ∉ Omega, F x = 0) (s : ℝ) :
    (∫⁻ x : ℝ, ‖F x‖ₑ ^ 2 * exteriorExitPair Omega x s) ≤
      ∫⁻ x : ℝ, ‖F x - F (x - s)‖ₑ ^ 2 := by
  have hminus : Measurable (fun x : ℝ =>
      if x - s ∈ Omega then (0 : ℝ≥0∞) else ‖F x‖ₑ ^ 2) :=
    Measurable.ite (hOmega.preimage (measurable_id.sub_const s))
      measurable_const (hF.enorm.pow_const 2)
  have hright : Measurable (fun x : ℝ =>
      if x ∈ Omega then (0 : ℝ≥0∞) else ‖F (x - s)‖ₑ ^ 2) :=
    Measurable.ite hOmega measurable_const
      ((hF.comp (measurable_id.sub_const s)).enorm.pow_const 2)
  have hshift :
      (∫⁻ x : ℝ, if x ∈ Omega then (0 : ℝ≥0∞) else ‖F (x - s)‖ₑ ^ 2) =
        ∫⁻ x : ℝ, if x + s ∈ Omega then (0 : ℝ≥0∞) else ‖F x‖ₑ ^ 2 := by
    simpa only [Function.comp_def, add_sub_cancel_right] using
      ((measurePreserving_add_right (volume : Measure ℝ) s).lintegral_comp hright).symm
  have hbound := lintegral_mono (μ := (volume : Measure ℝ))
    (fun x : ℝ => exit_pair_pointwise_le Omega F hzero x s)
  rw [lintegral_add_left hminus, hshift] at hbound
  calc
    _ = (∫⁻ x : ℝ, if x - s ∈ Omega then (0 : ℝ≥0∞) else ‖F x‖ₑ ^ 2) +
        ∫⁻ x : ℝ, if x + s ∈ Omega then (0 : ℝ≥0∞) else ‖F x‖ₑ ^ 2 := by
      rw [← lintegral_add_left hminus]
      apply lintegral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        dsimp only
        unfold exteriorExitPair
        by_cases hm : x - s ∈ Omega <;> by_cases hp : x + s ∈ Omega <;>
          simp [hm, hp, mul_add]
    _ ≤ _ := hbound

theorem exterior_mass_le_directionalEnergy
    (nu : Measure ℝ) [SFinite nu] (Omega : Set ℝ)
    (hOmega : MeasurableSet Omega) (F : ℝ → ℂ) (hF : Measurable F)
    (hzero : ∀ x ∉ Omega, F x = 0) :
    (∫⁻ x : ℝ, ‖F x‖ₑ ^ 2 * exteriorPotential nu Omega x) ≤
      directionalEnergy nu F := by
  have hpair : Measurable (fun p : ℝ × ℝ => exteriorExitPair Omega p.1 p.2) := by
    unfold exteriorExitPair
    exact (Measurable.ite (hOmega.preimage (measurable_fst.sub measurable_snd))
      (measurable_const : Measurable (fun _ : ℝ × ℝ => (0 : ℝ≥0∞)))
      measurable_const).add
      (Measurable.ite (hOmega.preimage (measurable_fst.add measurable_snd))
        measurable_const measurable_const)
  have hproduct : Measurable (fun p : ℝ × ℝ =>
      ‖F p.1‖ₑ ^ 2 * exteriorExitPair Omega p.1 p.2) :=
    ((hF.comp measurable_fst).enorm.pow_const 2).mul hpair
  calc
    _ = ∫⁻ x : ℝ, ∫⁻ s : ℝ,
        ‖F x‖ₑ ^ 2 * exteriorExitPair Omega x s ∂nu := by
      apply lintegral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        dsimp only
        unfold exteriorPotential
        exact (lintegral_const_mul' _ _ (by finiteness)).symm
    _ = ∫⁻ s : ℝ, ∫⁻ x : ℝ,
        ‖F x‖ₑ ^ 2 * exteriorExitPair Omega x s ∂volume ∂nu :=
      lintegral_lintegral_swap hproduct.aemeasurable
    _ ≤ _ := lintegral_mono fun s =>
      exit_pair_lintegral_le Omega hOmega F hF hzero s

theorem complex_norm_add_sq_le (z w : ℂ) :
    ‖z + w‖ ^ 2 ≤ 2 * ‖z‖ ^ 2 + 2 * ‖w‖ ^ 2 := by
  have ht := norm_add_le z w
  have hz := norm_nonneg z
  have hw := norm_nonneg w
  have hzw := norm_nonneg (z + w)
  nlinarith [sq_nonneg (‖z‖ - ‖w‖)]

private theorem cutoff_product_gap_sq_le (a b : ℝ) (z w : ℂ) :
    ‖(a : ℂ) * z - (b : ℂ) * w‖ ^ 2 ≤
      (a ^ 2 + b ^ 2) * ‖z - w‖ ^ 2 +
        (‖z‖ ^ 2 + ‖w‖ ^ 2) * (a - b) ^ 2 := by
  have hleft : (a : ℂ) * z - (b : ℂ) * w =
      (a : ℂ) * (z - w) + ((a - b : ℝ) : ℂ) * w := by push_cast; ring
  have hright : (a : ℂ) * z - (b : ℂ) * w =
      (b : ℂ) * (z - w) + ((a - b : ℝ) : ℂ) * z := by push_cast; ring
  have h₁ := complex_norm_add_sq_le ((a : ℂ) * (z - w)) (((a - b : ℝ) : ℂ) * w)
  have h₂ := complex_norm_add_sq_le ((b : ℂ) * (z - w)) (((a - b : ℝ) : ℂ) * z)
  rw [← hleft] at h₁
  rw [← hright] at h₂
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs] at h₁ h₂
  nlinarith

end D5.S3.Weil.ZetaGamma.FormCore

namespace D5.S3.Weil.ZetaGamma.FormCore

open MeasureTheory Set Filter
open scoped ENNReal Topology

theorem cutoff_outer_majorant_finite
    (nu : Measure ℝ) [SFinite nu] (Omega : Set ℝ)
    (hOmega : MeasurableSet Omega) (F : ℝ → ℂ) (hF : Measurable F)
    (hzero : ∀ x ∉ Omega, F x = 0)
    (hmass : (∫⁻ x : ℝ, ‖F x‖ₑ ^ 2) < (⊤ : ℝ≥0∞))
    (henergy : directionalEnergy nu F < (⊤ : ℝ≥0∞)) (C : ℝ) :
    (∫⁻ x : ℝ, ENNReal.ofReal C * ‖F x‖ₑ ^ 2 +
      2 * (‖F x‖ₑ ^ 2 * exteriorPotential nu Omega x)) < (⊤ : ℝ≥0∞) := by
  have hpotential :
      (∫⁻ x : ℝ, ‖F x‖ₑ ^ 2 * exteriorPotential nu Omega x) < (⊤ : ℝ≥0∞) :=
    lt_of_le_of_lt
      (exterior_mass_le_directionalEnergy nu Omega hOmega F hF hzero) henergy
  have hM : Measurable (fun x : ℝ => ENNReal.ofReal C * ‖F x‖ₑ ^ 2) := by fun_prop
  rw [lintegral_add_left hM,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_const_mul' _ _ (by norm_num)]
  exact ENNReal.add_lt_top.mpr
    ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hmass,
      ENNReal.mul_lt_top (by norm_num) hpotential⟩

def cutoffFirstDensity (b : ℝ → ℝ) (F : ℝ → ℂ)
    (p : ℝ × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((b p.2 ^ 2 + b (p.2 - p.1) ^ 2) *
    ‖F p.2 - F (p.2 - p.1)‖ ^ 2)

def cutoffFirstEnergy (nu : Measure ℝ) (b : ℝ → ℝ)
    (F : ℝ → ℂ) : ℝ≥0∞ :=
  ∫⁻ p : ℝ × ℝ, cutoffFirstDensity b F p ∂nu.prod volume

private theorem cutoffFirstDensity_measurable
    (b : ℝ → ℝ) (hb : Measurable b) (F : ℝ → ℂ) (hF : Measurable F) :
    Measurable (cutoffFirstDensity b F) := by
  unfold cutoffFirstDensity
  fun_prop

private theorem cutoffFirstDensity_le_two_gap
    (b : ℝ → ℝ) (hb : ∀ x, 0 ≤ b x ∧ b x ≤ 1)
    (F : ℝ → ℂ) (p : ℝ × ℝ) :
    cutoffFirstDensity b F p ≤
      2 * ENNReal.ofReal (‖F p.2 - F (p.2 - p.1)‖ ^ 2) := by
  have hx := hb p.2
  have hy := hb (p.2 - p.1)
  have hcoef : b p.2 ^ 2 + b (p.2 - p.1) ^ 2 ≤ 2 := by
    nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr hx.2),
      mul_nonneg hy.1 (sub_nonneg.mpr hy.2)]
  have hpoint := mul_le_mul_of_nonneg_right hcoef
    (sq_nonneg ‖F p.2 - F (p.2 - p.1)‖)
  calc
    _ ≤ ENNReal.ofReal (2 * ‖F p.2 - F (p.2 - p.1)‖ ^ 2) :=
      ENNReal.ofReal_le_ofReal hpoint
    _ = _ := by simp only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]

theorem cutoffFirstEnergy_tendsto_zero
    (nu : Measure ℝ) [SFinite nu] (F : ℝ → ℂ) (hF : Measurable F)
    (henergy : directionalEnergy nu F < (⊤ : ℝ≥0∞)) (b : ℝ → ℝ → ℝ)
    (hb : ∀ ε, Measurable (b ε))
    (hbound : ∀ ε > 0, ∀ x, 0 ≤ b ε x ∧ b ε x ≤ 1)
    (hzero : ∀ x, Tendsto (fun ε => b ε x) (𝓝[Ioi (0 : ℝ)] 0) (𝓝 0)) :
    Tendsto (fun ε => cutoffFirstEnergy nu (b ε) F)
      (𝓝[Ioi (0 : ℝ)] 0) (𝓝 0) := by
  let gap : ℝ × ℝ → ℝ≥0∞ :=
    fun p => ENNReal.ofReal (‖F p.2 - F (p.2 - p.1)‖ ^ 2)
  have hgap : Measurable gap := by dsimp only [gap]; fun_prop
  have hgapIntegral : (∫⁻ p : ℝ × ℝ, gap p ∂nu.prod volume) =
      directionalEnergy nu F := by
    rw [lintegral_prod _ hgap.aemeasurable]
    unfold directionalEnergy
    apply lintegral_congr_ae
    exact Eventually.of_forall fun s => by
      apply lintegral_congr_ae
      exact Eventually.of_forall fun x => by
        dsimp only [gap]
        rw [ENNReal.ofReal_pow (norm_nonneg _) 2, ofReal_norm]
  have hfinite : (∫⁻ p : ℝ × ℝ, 2 * gap p ∂nu.prod volume) ≠ (⊤ : ℝ≥0∞) := by
    rw [lintegral_const_mul' _ _ (by norm_num), hgapIntegral]
    exact (ENNReal.mul_lt_top (by norm_num) henergy).ne
  have hmeas : ∀ᶠ ε in 𝓝[Ioi (0 : ℝ)] 0,
      Measurable (cutoffFirstDensity (b ε) F) :=
    Eventually.of_forall fun ε => cutoffFirstDensity_measurable _ (hb ε) _ hF
  have hdom : ∀ᶠ ε in 𝓝[Ioi (0 : ℝ)] 0,
      ∀ᵐ p ∂nu.prod volume, cutoffFirstDensity (b ε) F p ≤ 2 * gap p := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact Eventually.of_forall fun p => cutoffFirstDensity_le_two_gap _ (hbound ε hε) F p
  have hlim : ∀ᵐ p ∂nu.prod volume,
      Tendsto (fun ε => cutoffFirstDensity (b ε) F p)
        (𝓝[Ioi (0 : ℝ)] 0) (𝓝 (0 : ℝ≥0∞)) := by
    exact Eventually.of_forall fun p => by
      have hreal : Tendsto (fun ε =>
          (b ε p.2 ^ 2 + b ε (p.2 - p.1) ^ 2) *
            ‖F p.2 - F (p.2 - p.1)‖ ^ 2)
          (𝓝[Ioi (0 : ℝ)] 0) (𝓝 (0 : ℝ)) := by
        simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add, zero_mul] using
          (((hzero p.2).pow 2).add ((hzero (p.2 - p.1)).pow 2)).mul_const
            (‖F p.2 - F (p.2 - p.1)‖ ^ 2)
      simpa only [cutoffFirstDensity, ENNReal.ofReal_zero, Function.comp_def] using
        (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hreal
  simpa only [cutoffFirstEnergy, lintegral_zero] using
    tendsto_lintegral_filter_of_dominated_convergence
      (μ := nu.prod volume) (fun p => 2 * gap p) hmeas hdom hfinite hlim

end D5.S3.Weil.ZetaGamma.FormCore

namespace D5.S3.Weil.ZetaGamma.FormCore

open MeasureTheory Set Filter
open scoped ENNReal Topology

def radialMaskEnergy (nu : Measure ℝ) (b : ℝ → ℝ) (y : ℝ) : ℝ≥0∞ :=
  ∫⁻ s : ℝ, ENNReal.ofReal
    ((b (y + s) - b y) ^ 2 + (b (y - s) - b y) ^ 2) ∂nu

theorem radialMaskEnergy_measurable
    (nu : Measure ℝ) [SFinite nu] (b : ℝ → ℝ) (hb : Measurable b) :
    Measurable (radialMaskEnergy nu b) := by
  have hpair : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal
      ((b (p.1 + p.2) - b p.1) ^ 2 + (b (p.1 - p.2) - b p.1) ^ 2)) := by
    fun_prop
  exact hpair.lintegral_prod_right'

private theorem cutoff_commutator_lintegral_eq_radial
    (b : ℝ → ℝ) (hb : Measurable b) (F : ℝ → ℂ) (hF : Measurable F) (s : ℝ) :
    (∫⁻ x : ℝ, ENNReal.ofReal
      ((‖F x‖ ^ 2 + ‖F (x - s)‖ ^ 2) * (b x - b (x - s)) ^ 2)) =
      ∫⁻ y : ℝ, ‖F y‖ₑ ^ 2 * ENNReal.ofReal
        ((b (y + s) - b y) ^ 2 + (b (y - s) - b y) ^ 2) := by
  have hnorm (z : ℂ) : ENNReal.ofReal (‖z‖ ^ 2) = ‖z‖ₑ ^ 2 := by
    rw [ENNReal.ofReal_pow (norm_nonneg _) 2, ofReal_norm]
  have hsplit (x : ℝ) : ENNReal.ofReal
      ((‖F x‖ ^ 2 + ‖F (x - s)‖ ^ 2) * (b x - b (x - s)) ^ 2) =
        ‖F x‖ₑ ^ 2 * ENNReal.ofReal ((b x - b (x - s)) ^ 2) +
          ‖F (x - s)‖ₑ ^ 2 * ENNReal.ofReal ((b x - b (x - s)) ^ 2) := by
    rw [ENNReal.ofReal_mul (add_nonneg (sq_nonneg ‖F x‖) (sq_nonneg ‖F (x - s)‖)),
      ENNReal.ofReal_add (sq_nonneg ‖F x‖) (sq_nonneg ‖F (x - s)‖)]
    simp only [hnorm, add_mul]
  have hminus : Measurable (fun x : ℝ =>
      ‖F x‖ₑ ^ 2 * ENNReal.ofReal ((b x - b (x - s)) ^ 2)) := by fun_prop
  have hshifted : Measurable (fun x : ℝ =>
      ‖F (x - s)‖ₑ ^ 2 * ENNReal.ofReal ((b x - b (x - s)) ^ 2)) := by fun_prop
  have hplus : Measurable (fun y : ℝ =>
      ‖F y‖ₑ ^ 2 * ENNReal.ofReal ((b (y + s) - b y) ^ 2)) := by fun_prop
  have hshift :
      (∫⁻ x : ℝ, ‖F (x - s)‖ₑ ^ 2 * ENNReal.ofReal ((b x - b (x - s)) ^ 2)) =
        ∫⁻ y : ℝ, ‖F y‖ₑ ^ 2 * ENNReal.ofReal ((b (y + s) - b y) ^ 2) := by
    simpa only [Function.comp_def, add_sub_cancel_right] using
      ((measurePreserving_add_right (volume : Measure ℝ) s).lintegral_comp hshifted).symm
  calc
    _ = ∫⁻ x : ℝ,
        ‖F x‖ₑ ^ 2 * ENNReal.ofReal ((b x - b (x - s)) ^ 2) +
          ‖F (x - s)‖ₑ ^ 2 * ENNReal.ofReal ((b x - b (x - s)) ^ 2) :=
      lintegral_congr_ae (Eventually.of_forall hsplit)
    _ = (∫⁻ x : ℝ, ‖F x‖ₑ ^ 2 * ENNReal.ofReal ((b x - b (x - s)) ^ 2)) +
        ∫⁻ x : ℝ, ‖F (x - s)‖ₑ ^ 2 * ENNReal.ofReal ((b x - b (x - s)) ^ 2) :=
      lintegral_add_left hminus _
    _ = (∫⁻ x : ℝ, ‖F x‖ₑ ^ 2 * ENNReal.ofReal ((b x - b (x - s)) ^ 2)) +
        ∫⁻ y : ℝ, ‖F y‖ₑ ^ 2 * ENNReal.ofReal ((b (y + s) - b y) ^ 2) := by
      rw [hshift]
    _ = (∫⁻ y : ℝ, ‖F y‖ₑ ^ 2 * ENNReal.ofReal ((b (y + s) - b y) ^ 2)) +
        ∫⁻ y : ℝ, ‖F y‖ₑ ^ 2 * ENNReal.ofReal ((b y - b (y - s)) ^ 2) := add_comm _ _
    _ = ∫⁻ y : ℝ,
        ‖F y‖ₑ ^ 2 * ENNReal.ofReal ((b (y + s) - b y) ^ 2) +
          ‖F y‖ₑ ^ 2 * ENNReal.ofReal ((b y - b (y - s)) ^ 2) :=
      (lintegral_add_left hplus _).symm
    _ = _ := by
      apply lintegral_congr_ae
      exact Eventually.of_forall fun y => by
        dsimp only
        have hsq : (b y - b (y - s)) ^ 2 = (b (y - s) - b y) ^ 2 := by ring
        rw [hsq, ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _), mul_add]

theorem directionalEnergy_cutoff_le
    (nu : Measure ℝ) [SFinite nu] (b : ℝ → ℝ) (hb : Measurable b)
    (F : ℝ → ℂ) (hF : Measurable F) :
    directionalEnergy nu (fun x => (b x : ℂ) * F x) ≤
      cutoffFirstEnergy nu b F +
        ∫⁻ y : ℝ, ‖F y‖ₑ ^ 2 * radialMaskEnergy nu b y := by
  let G : ℝ × ℝ → ℝ≥0∞ := fun p =>
    ‖(b p.2 : ℂ) * F p.2 - (b (p.2 - p.1) : ℂ) * F (p.2 - p.1)‖ₑ ^ 2
  let J : ℝ × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal
    ((‖F p.2‖ ^ 2 + ‖F (p.2 - p.1)‖ ^ 2) * (b p.2 - b (p.2 - p.1)) ^ 2)
  have hG : Measurable G := by dsimp only [G]; fun_prop
  have hJ : Measurable J := by dsimp only [J]; fun_prop
  have hR : Measurable (fun p : ℝ × ℝ =>
      ‖F p.2‖ₑ ^ 2 * ENNReal.ofReal
        ((b (p.2 + p.1) - b p.2) ^ 2 + (b (p.2 - p.1) - b p.2) ^ 2)) := by
    fun_prop
  have hpoint (p : ℝ × ℝ) : G p ≤ cutoffFirstDensity b F p + J p := by
    have h := ENNReal.ofReal_le_ofReal
      (cutoff_product_gap_sq_le (b p.2) (b (p.2 - p.1)) (F p.2) (F (p.2 - p.1)))
    rw [ENNReal.ofReal_add
      (mul_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _))
      (mul_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)),
      ENNReal.ofReal_pow (norm_nonneg _) 2, ofReal_norm] at h
    exact h
  have hJradial : (∫⁻ p : ℝ × ℝ, J p ∂nu.prod volume) =
      ∫⁻ y : ℝ, ‖F y‖ₑ ^ 2 * radialMaskEnergy nu b y := by
    calc
      _ = ∫⁻ s : ℝ, ∫⁻ x : ℝ, J (s, x) ∂volume ∂nu :=
        lintegral_prod J hJ.aemeasurable
      _ = ∫⁻ s : ℝ, ∫⁻ y : ℝ, ‖F y‖ₑ ^ 2 * ENNReal.ofReal
          ((b (y + s) - b y) ^ 2 + (b (y - s) - b y) ^ 2) ∂volume ∂nu := by
        apply lintegral_congr_ae
        exact Eventually.of_forall fun s => cutoff_commutator_lintegral_eq_radial b hb F hF s
      _ = ∫⁻ y : ℝ, ∫⁻ s : ℝ, ‖F y‖ₑ ^ 2 * ENNReal.ofReal
          ((b (y + s) - b y) ^ 2 + (b (y - s) - b y) ^ 2) ∂nu ∂volume :=
        lintegral_lintegral_swap hR.aemeasurable
      _ = _ := by
        apply lintegral_congr_ae
        exact Eventually.of_forall fun y => by
          unfold radialMaskEnergy
          exact lintegral_const_mul' _ _ (by finiteness)
  calc
    _ = ∫⁻ p : ℝ × ℝ, G p ∂nu.prod volume :=
      (lintegral_prod G hG.aemeasurable).symm
    _ ≤ ∫⁻ p : ℝ × ℝ, cutoffFirstDensity b F p + J p ∂nu.prod volume :=
      lintegral_mono hpoint
    _ = cutoffFirstEnergy nu b F + ∫⁻ p : ℝ × ℝ, J p ∂nu.prod volume :=
      lintegral_add_left (cutoffFirstDensity_measurable b hb F hF) _
    _ = _ := by rw [hJradial]

end D5.S3.Weil.ZetaGamma.FormCore
