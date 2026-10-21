/- GID: D5/S3/Weil/ZetaGamma/FormCore/CommonCutoff
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaGamma/FormCore/CommonCutoff
   mirror-E: none(waiver:analytic-Gamma-form-core)
   anchors: []
   utility: none
   digest: Actual common-cutoff identity over canonical interval carriers. -/


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

namespace D5.S3.Weil.ZetaGamma.FormCore.CommonCutoff

open D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport

abbrev density :=
  D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.archimedeanJumpDensity

def cutoffKernel (ε s : ℝ) : ℝ :=
  if ε < |s| then density |s| else 0

theorem actual_density_tail_integrable {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn density (Ioi ε) := by
  let D : ℝ := 1 - Real.exp (-2 * ε)
  have hD : 0 < D := by
    dsimp only [D]
    exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have hExp : IntegrableOn (fun s : ℝ => Real.exp (-s / 2)) (Ioi ε) := by
    convert integrableOn_exp_mul_Ioi (a := -(1 / 2 : ℝ)) (by norm_num) ε using 1
    ext s
    congr 1
    ring
  have hDom := hExp.div_const D
  have hMeas : Measurable density := by
    change Measurable (fun x : ℝ => Real.exp (-x / 2) / (1 - Real.exp (-2 * x)))
    fun_prop
  apply hDom.mono' hMeas.aestronglyMeasurable
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
  have hs' : ε < s := hs
  have hDen : D ≤ 1 - Real.exp (-2 * s) := by
    dsimp only [D]
    have he : Real.exp (-2 * s) ≤ Real.exp (-2 * ε) :=
      Real.exp_le_exp.mpr (by linarith)
    linarith
  have hDs : 0 < 1 - Real.exp (-2 * s) := hD.trans_le hDen
  have hk : 0 ≤ density s := by
    exact div_nonneg (Real.exp_pos _).le hDs.le
  rw [Real.norm_of_nonneg hk]
  exact div_le_div_of_nonneg_left (Real.exp_pos _).le hD hDen

private theorem actual_density_nonneg {s : ℝ} (hs : 0 < s) : 0 ≤ density s := by
  have hden : 0 < 1 - Real.exp (-2 * s) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  exact div_nonneg (Real.exp_pos _).le hden.le

private def differenceCorrelation
    (d t ε : ℝ) [Fact (0 < d)] (u : ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  (cutoffKernel ε p.2 : ℂ) * conj (u p.1) *
    (periodicExtension d t u (p.1 - p.2) - zeroExtension d t u (p.1 - p.2))

def imageKernel (d ε x y : ℝ) : ℝ :=
  ∑' m : ℤ, if m = 0 then 0 else cutoffKernel ε (x - y + m • d)

private theorem lattice_image_integrable_and_identity
    (d t ε : ℝ) [Fact (0 < d)] (u : ℝ → ℂ)
    (hF : Integrable (differenceCorrelation d t ε u)
      ((windowMeasure d t).prod volume)) :
    Integrable (fun p : ℝ × ℝ =>
      conj (u p.1) * (imageKernel d ε p.1 p.2 : ℂ) * u p.2)
      ((windowMeasure d t).prod (windowMeasure d t)) ∧
    ((∫ p, differenceCorrelation d t ε u p ∂((windowMeasure d t).prod volume)) =
      ∫ p, conj (u p.1) * (imageKernel d ε p.1 p.2 : ℂ) * u p.2
        ∂((windowMeasure d t).prod (windowMeasure d t))) := by
  simpa only [differenceCorrelation, imageKernel,
    D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.weightedDifferenceCorrelation,
    D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.weightedImageKernel] using
    (D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.weightedLattice_image_integrable_and_identity
      d t (cutoffKernel ε) u hF)

open MeasureTheory.Measure

private theorem zero_extension_memLp
    (d t : ℝ) (u : ℝ → ℂ) (hu : MemLp u 2 (windowMeasure d t)) :
    MemLp (zeroExtension d t u) 2 volume := by
  exact (memLp_indicator_iff_restrict (μ := volume)
    measurableSet_Ioc.nullMeasurableSet).mpr hu

private theorem zero_shift_memLp
    (d t : ℝ) (u : ℝ → ℂ) (hu : MemLp u 2 (windowMeasure d t)) (s : ℝ) :
    MemLp (fun x => zeroExtension d t u (x - s)) 2 (windowMeasure d t) := by
  have hzero := (zero_extension_memLp d t u hu).comp_measurePreserving
    (measurePreserving_sub_right (volume : Measure ℝ) s)
  exact hzero.restrict (Ioc t (t + d))

private theorem mask_correlation_integrable_le
    (d t : ℝ) [Fact (0 < d)] (u : ℝ → ℂ)
    (hu : MemLp u 2 (windowMeasure d t)) (s : ℝ) :
    Integrable (fun x => ‖u x‖ *
      ‖periodicExtension d t u (x - s) - zeroExtension d t u (x - s)‖)
      (windowMeasure d t) ∧
    (∫ x, ‖u x‖ *
      ‖periodicExtension d t u (x - s) - zeroExtension d t u (x - s)‖
        ∂windowMeasure d t) ≤ windowEnergy d t u := by
  obtain ⟨hc, hcle⟩ := periodic_correlation_integrable_le d t u hu s
  have hm := ((periodic_shift_memLp d t u hu s).sub
    (zero_shift_memLp d t u hu s)).norm
  have hpoint (x : ℝ) :
      ‖u x‖ * ‖periodicExtension d t u (x - s) - zeroExtension d t u (x - s)‖ ≤
        ‖u x‖ * ‖periodicExtension d t u (x - s)‖ :=
    mul_le_mul_of_nonneg_left (periodic_minus_zero_norm_le d t u (x - s))
      (norm_nonneg _)
  have hi : Integrable (fun x => ‖u x‖ *
      ‖periodicExtension d t u (x - s) - zeroExtension d t u (x - s)‖)
      (windowMeasure d t) := by
    apply hc.mono' (hu.aestronglyMeasurable.norm.mul hm.aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun x => by
      simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply]
      rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
      exact hpoint x
  exact ⟨hi, (integral_mono hi hc hpoint).trans hcle⟩

private theorem cutoffKernel_nonneg {ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    0 ≤ cutoffKernel ε s := by
  by_cases hs : ε < |s|
  · simpa only [cutoffKernel, if_pos hs] using actual_density_nonneg (hε.trans hs)
  · simp only [cutoffKernel, if_neg hs, le_refl]

private theorem cutoffKernel_eq_tail_plus_reflection {ε : ℝ} (hε : 0 < ε) :
    cutoffKernel ε = fun s =>
      (Ioi ε).indicator density s + (Ioi ε).indicator density (-s) := by
  funext s
  by_cases hs : 0 ≤ s
  · have hn : ¬ ε < -s := by linarith
    simp [cutoffKernel, Set.indicator, abs_of_nonneg hs, hn]
  · have hs' : s ≤ 0 := le_of_not_ge hs
    have hn : ¬ ε < s := by linarith
    simp [cutoffKernel, Set.indicator, abs_of_nonpos hs', hn]

private theorem cutoffKernel_integrable_mass {ε : ℝ} (hε : 0 < ε) :
    Integrable (cutoffKernel ε) volume ∧
      (∫ s : ℝ, cutoffKernel ε s) = 2 * ∫ s in Ioi ε, density s := by
  have hg : Integrable ((Ioi ε).indicator density) volume :=
    (actual_density_tail_integrable hε).integrable_indicator measurableSet_Ioi
  have hgn := hg.comp_neg
  have heq := cutoffKernel_eq_tail_plus_reflection hε
  refine ⟨?_, ?_⟩
  · rw [heq]
    exact hg.add hgn
  · rw [heq, integral_add hg hgn,
      integral_neg_eq_self ((Ioi ε).indicator density) volume,
      integral_indicator measurableSet_Ioi]
    ring

private theorem differenceCorrelation_swapped_aestronglyMeasurable
    (d t ε : ℝ) [Fact (0 < d)] (hε : 0 < ε) (u : ℝ → ℂ)
    (hu : MemLp u 2 (windowMeasure d t)) :
    AEStronglyMeasurable
      (fun p : ℝ × ℝ => differenceCorrelation d t ε u p.swap)
      (volume.prod (windowMeasure d t)) := by
  have hk := (cutoffKernel_integrable_mass hε).1.1
  have hkc : AEStronglyMeasurable (fun s => (cutoffKernel ε s : ℂ)) volume :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable hk
  have huj : AEStronglyMeasurable (fun p : ℝ × ℝ => conj (u p.2))
      (volume.prod (windowMeasure d t)) :=
    Complex.continuous_conj.comp_aestronglyMeasurable hu.aestronglyMeasurable.comp_snd
  exact (hkc.comp_fst.mul huj).mul
    ((periodic_shift_joint_aestronglyMeasurable d t u hu).sub
      (zero_shift_joint_aestronglyMeasurable d t u hu))

private theorem differenceCorrelation_integrable_and_bound
    (d t ε : ℝ) [Fact (0 < d)] (hε : 0 < ε) (u : ℝ → ℂ)
    (hu : MemLp u 2 (windowMeasure d t)) :
    Integrable (differenceCorrelation d t ε u) ((windowMeasure d t).prod volume) ∧
    (∫ p, ‖differenceCorrelation d t ε u p‖ ∂((windowMeasure d t).prod volume)) ≤
      2 * windowEnergy d t u * ∫ s in Ioi ε, density s := by
  let F : ℝ × ℝ → ℂ := fun p => differenceCorrelation d t ε u p.swap
  let N : ℝ → ℝ := fun s => ∫ x, ‖F (s, x)‖ ∂windowMeasure d t
  obtain ⟨hk, hkmass⟩ := cutoffKernel_integrable_mass hε
  have hFm : AEStronglyMeasurable F (volume.prod (windowMeasure d t)) :=
    differenceCorrelation_swapped_aestronglyMeasurable d t ε hε u hu
  have hnorm (s x : ℝ) : ‖F (s, x)‖ = cutoffKernel ε s *
      (‖u x‖ * ‖periodicExtension d t u (x - s) - zeroExtension d t u (x - s)‖) := by
    simp only [F, differenceCorrelation, Prod.swap_prod_mk, norm_mul,
      Complex.norm_conj, Complex.norm_real,
      Real.norm_of_nonneg (cutoffKernel_nonneg hε s)]
    ring
  have hSlice (s : ℝ) : Integrable (fun x => F (s, x)) (windowMeasure d t) := by
    have hc : Integrable (fun x => cutoffKernel ε s *
        (‖u x‖ * ‖periodicExtension d t u (x - s) - zeroExtension d t u (x - s)‖))
        (windowMeasure d t) :=
      (mask_correlation_integrable_le d t u hu s).1.const_mul (cutoffKernel ε s)
    have hsm : AEStronglyMeasurable (fun x => F (s, x)) (windowMeasure d t) := by
      change AEStronglyMeasurable (fun x : ℝ => (cutoffKernel ε s : ℂ) * conj (u x) *
        (periodicExtension d t u (x - s) - zeroExtension d t u (x - s)))
        (windowMeasure d t)
      have hconstant : AEStronglyMeasurable (fun _ : ℝ => (cutoffKernel ε s : ℂ))
          (windowMeasure d t) := aestronglyMeasurable_const
      have hconj : AEStronglyMeasurable (fun x => conj (u x)) (windowMeasure d t) :=
        Complex.continuous_conj.comp_aestronglyMeasurable hu.aestronglyMeasurable
      have hdiff : AEStronglyMeasurable (fun x =>
          periodicExtension d t u (x - s) - zeroExtension d t u (x - s))
          (windowMeasure d t) :=
        ((periodic_shift_memLp d t u hu s).sub
          (zero_shift_memLp d t u hu s)).aestronglyMeasurable
      exact (hconstant.mul hconj).mul hdiff
    apply hc.mono' hsm
    exact Filter.Eventually.of_forall fun x => (hnorm s x).le
  have hNm : AEStronglyMeasurable N volume := hFm.norm.integral_prod_right'
  have hNnonneg (s : ℝ) : 0 ≤ N s := integral_nonneg fun _ => norm_nonneg _
  have hNle (s : ℝ) : N s ≤ cutoffKernel ε s * windowEnergy d t u := by
    dsimp only [N]
    simp_rw [hnorm s]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left
      (mask_correlation_integrable_le d t u hu s).2 (cutoffKernel_nonneg hε s)
  have hNint : Integrable N volume := by
    apply (hk.const_mul (windowEnergy d t u)).mono' hNm
    exact Filter.Eventually.of_forall fun s => by
      change ‖N s‖ ≤ windowEnergy d t u * cutoffKernel ε s
      rw [Real.norm_of_nonneg (hNnonneg s), mul_comm (windowEnergy d t u)]
      exact hNle s
  have hFint : Integrable F (volume.prod (windowMeasure d t)) :=
    (integrable_prod_iff hFm).mpr
      ⟨Filter.Eventually.of_forall hSlice, hNint⟩
  refine ⟨?_, ?_⟩
  · simpa only [Function.comp_def, F, Prod.swap_swap] using hFint.swap
  · calc
      _ = ∫ p, ‖F p‖ ∂(volume.prod (windowMeasure d t)) :=
        (integral_prod_swap
          (μ := windowMeasure d t) (ν := (volume : Measure ℝ))
          (fun p => ‖differenceCorrelation d t ε u p‖)).symm
      _ = ∫ s, N s := integral_prod (fun p => ‖F p‖) hFint.norm
      _ ≤ ∫ s, windowEnergy d t u * cutoffKernel ε s :=
        integral_mono hNint (hk.const_mul _) fun s => by
          simpa only [mul_comm] using hNle s
      _ = windowEnergy d t u * (2 * ∫ s in Ioi ε, density s) := by
        rw [integral_const_mul, hkmass]
      _ = 2 * windowEnergy d t u * ∫ s in Ioi ε, density s := by ring

def zeroCutoffEnergy (d t ε : ℝ) (u : ℝ → ℂ) : ℝ :=
  ∫ s in Ioi ε, density s * zeroTranslationEnergy d t u s

def periodicCutoffEnergy (d t ε : ℝ) [Fact (0 < d)] (u : ℝ → ℂ) : ℝ :=
  ∫ s in Ioi ε, density s * periodicTranslationEnergy d t u s

private theorem differenceCorrelation_slice
    (d t ε : ℝ) [Fact (0 < d)] (u : ℝ → ℂ)
    (hu : MemLp u 2 (windowMeasure d t)) (s : ℝ) :
    (∫ x, differenceCorrelation d t ε u (x, s) ∂windowMeasure d t) =
      (cutoffKernel ε s : ℂ) *
        (periodicCorrelation d t u s - zeroCorrelation d t u s) := by
  simp only [differenceCorrelation, mul_assoc]
  rw [integral_const_mul, correlation_difference_slice d t u hu s]

private theorem cutoffKernel_of_mem_tail {ε s : ℝ} (hε : 0 < ε) (hs : s ∈ Ioi ε) :
    cutoffKernel ε s = density s := by
  have hs' : ε < s := hs
  have hs0 : 0 < s := hε.trans hs'
  simp only [cutoffKernel, abs_of_pos hs0, if_pos hs']

private theorem signed_cutoff_integral_eq_twice_positive
    {ε : ℝ} (hε : 0 < ε) (R : ℝ → ℝ) (hR : ∀ s, R (-s) = R s)
    (hInt : Integrable (fun s => cutoffKernel ε s * R s) volume) :
    (∫ s : ℝ, cutoffKernel ε s * R s) = 2 * ∫ s in Ioi ε, density s * R s := by
  let H : ℝ → ℝ := (Ioi ε).indicator (fun s => density s * R s)
  have hH : H = (Ioi ε).indicator (fun s => cutoffKernel ε s * R s) := by
    funext s
    by_cases hs : s ∈ Ioi ε
    · simp only [H, Set.indicator_of_mem hs, cutoffKernel_of_mem_tail hε hs]
    · simp only [H, Set.indicator_of_notMem hs]
  have hHi : Integrable H volume := by rw [hH]; exact hInt.indicator measurableSet_Ioi
  have hHpoint (s : ℝ) : H s = (Ioi ε).indicator density s * R s := by
    by_cases hs : s ∈ Ioi ε <;> simp [H, hs]
  have hsplit : (fun s => cutoffKernel ε s * R s) = fun s => H s + H (-s) := by
    funext s
    rw [hHpoint, hHpoint, hR]
    have hkernel := congrFun (cutoffKernel_eq_tail_plus_reflection hε) s
    rw [hkernel]
    ring
  rw [hsplit, integral_add hHi hHi.comp_neg, integral_neg_eq_self H volume]
  rw [show (∫ s, H s) = ∫ s in Ioi ε, density s * R s from
    integral_indicator measurableSet_Ioi]
  ring

private theorem cutoff_energy_integrable_of_bound
    {ε : ℝ} (hε : 0 < ε) (E : ℝ → ℝ) (C : ℝ)
    (hEm : AEStronglyMeasurable E volume) (hE : ∀ s, 0 ≤ E s ∧ E s ≤ C) :
    IntegrableOn (fun s => density s * E s) (Ioi ε) := by
  have hk := actual_density_tail_integrable hε
  apply (hk.mul_const C).mono' (hk.1.mul hEm.restrict)
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
  have hks := actual_density_nonneg (hε.trans hs)
  change ‖density s * E s‖ ≤ density s * C
  rw [Real.norm_of_nonneg (mul_nonneg hks (hE s).1)]
  exact mul_le_mul_of_nonneg_left (hE s).2 hks

private theorem zeroCutoffEnergy_integrable
    (d t ε : ℝ) (hε : 0 < ε) (u : ℝ → ℂ)
    (hu : MemLp u 2 (windowMeasure d t)) :
    IntegrableOn (fun s => density s * zeroTranslationEnergy d t u s) (Ioi ε) :=
  cutoff_energy_integrable_of_bound hε _ _
    (zeroTranslationEnergy_aestronglyMeasurable d t u hu)
    (zeroTranslationEnergy_nonneg_le d t u hu)

private theorem periodicCutoffEnergy_integrable
    (d t ε : ℝ) [Fact (0 < d)] (hε : 0 < ε) (u : ℝ → ℂ)
    (hu : MemLp u 2 (windowMeasure d t)) :
    IntegrableOn (fun s => density s * periodicTranslationEnergy d t u s) (Ioi ε) :=
  cutoff_energy_integrable_of_bound hε _ _
    (periodicTranslationEnergy_aestronglyMeasurable d t u hu)
    (periodicTranslationEnergy_nonneg_le d t u hu)

theorem actual_common_cutoff_integrable_and_identity
    (d t ε : ℝ) [Fact (0 < d)] (hε : 0 < ε) (u : ℝ → ℂ)
    (hu : MemLp u 2 (windowMeasure d t)) :
    IntegrableOn (fun s => density s * zeroTranslationEnergy d t u s) (Ioi ε) ∧
    IntegrableOn (fun s => density s * periodicTranslationEnergy d t u s) (Ioi ε) ∧
    Integrable (fun p : ℝ × ℝ =>
      conj (u p.1) * (imageKernel d ε p.1 p.2 : ℂ) * u p.2)
      ((windowMeasure d t).prod (windowMeasure d t)) ∧
    zeroCutoffEnergy d t ε u = periodicCutoffEnergy d t ε u +
      (∫ p : ℝ × ℝ,
        conj (u p.1) * (imageKernel d ε p.1 p.2 : ℂ) * u p.2
          ∂((windowMeasure d t).prod (windowMeasure d t))).re := by
  have hE0 := zeroCutoffEnergy_integrable d t ε hε u hu
  have hEP := periodicCutoffEnergy_integrable d t ε hε u hu
  have hF := (differenceCorrelation_integrable_and_bound d t ε hε u hu).1
  obtain ⟨hB, hFB⟩ := lattice_image_integrable_and_identity d t ε u hF
  let R : ℝ → ℝ := fun s =>
    (periodicCorrelation d t u s - zeroCorrelation d t u s).re
  have hRneg (s : ℝ) : R (-s) = R s := by
    simp only [R, periodicCorrelation_neg, zeroCorrelation_neg, map_sub, Complex.sub_re, Complex.conj_re]
  have hSlice : Integrable
      (fun s => ∫ x, differenceCorrelation d t ε u (x, s) ∂windowMeasure d t) volume :=
    hF.integral_prod_right
  have hSliceRe (s : ℝ) :
      (∫ x, differenceCorrelation d t ε u (x, s) ∂windowMeasure d t).re =
        cutoffKernel ε s * R s := by
    rw [differenceCorrelation_slice d t ε u hu s]
    simp only [R, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hRint : Integrable (fun s => cutoffKernel ε s * R s) volume := by
    convert hSlice.re using 1
    funext s
    exact (hSliceRe s).symm
  have hBreal :
      (∫ p : ℝ × ℝ,
        conj (u p.1) * (imageKernel d ε p.1 p.2 : ℂ) * u p.2
          ∂((windowMeasure d t).prod (windowMeasure d t))).re =
        2 * ∫ s in Ioi ε, density s * R s := by
    calc
      _ = (∫ p, differenceCorrelation d t ε u p
          ∂((windowMeasure d t).prod volume)).re := congrArg Complex.re hFB.symm
      _ = (∫ s, ∫ x, differenceCorrelation d t ε u (x, s)
          ∂windowMeasure d t).re := congrArg Complex.re
            (integral_prod_symm (differenceCorrelation d t ε u) hF)
      _ = ∫ s, (∫ x, differenceCorrelation d t ε u (x, s)
          ∂windowMeasure d t).re := (integral_re hSlice).symm
      _ = ∫ s : ℝ, cutoffKernel ε s * R s := by simp_rw [hSliceRe]
      _ = _ := signed_cutoff_integral_eq_twice_positive hε R hRneg hRint
  have hEnergyDifference :
      zeroCutoffEnergy d t ε u - periodicCutoffEnergy d t ε u =
        2 * ∫ s in Ioi ε, density s * R s := by
    unfold zeroCutoffEnergy periodicCutoffEnergy
    rw [← integral_sub hE0 hEP]
    calc
      _ = ∫ s in Ioi ε, 2 * (density s * R s) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun s => by
          change density s * zeroTranslationEnergy d t u s -
            density s * periodicTranslationEnergy d t u s = 2 * (density s * R s)
          rw [zeroTranslationEnergy_expansion d t u hu s,
            periodicTranslationEnergy_expansion d t u hu s]
          simp only [R, Complex.sub_re]
          ring
      _ = _ := integral_const_mul 2 _
  refine ⟨hE0, hEP, hB, ?_⟩
  linarith [hBreal, hEnergyDifference]

end D5.S3.Weil.ZetaGamma.FormCore.CommonCutoff
