/-
  GID: D5/S3/Arith/Robin/CompleteLowHWeightedSpectralMean
  generality: I
  mirror-B: none (source-only SSHX delivery)
  utility: kind=none

  Complete multiplicity-preserving low-height spectral mean.  The theorem
  consumes only the explicit strip/height/reciprocal-square/count facts and
  lower-level Gaussian estimates.  It never assumes the requested
  final bound.  Integrability follows from the full-real Gaussian majorant;
  shell summability and its estimate follow from indexed shell counting.
-/

import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Set.Card
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

import Mathlib.Analysis.Complex.ExponentialBounds
import D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticFourthMoment

import D5.S3.Arith.Robin.CompleteLowHGaussianMoment
import D5.S3.Arith.Robin.CompleteCoefficientLaplace

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ComplexConjugate
open scoped BigOperators NNReal ENNReal

namespace D5.S3.Arith.Robin.CompleteLowHWeightedSpectralMean

set_option autoImplicit false

abbrev ZeroIndex := ℕ

/-- A faithful countable zero family.  The function is allowed to repeat a
    value, so multiplicities are retained by the index rather than collapsed
    into a set. -/
structure CompleteZeroFamily where
  zero : ZeroIndex → ℂ
  strip : ∀ n, 0 < (zero n).re ∧ (zero n).re < 1
  height : ∀ n, 10 < |(zero n).im|
  reciprocalSquare : Summable (fun n => ((zero n).im)⁻¹ ^ 2)
  reciprocalSquare_lt_two : ∑' n, ((zero n).im)⁻¹ ^ 2 < 2
  finite_count_shell : ∀ T : ℝ, 10 ≤ T →
    Set.Finite {n : ZeroIndex | |(zero n).im| ≤ T}
  count_both : ∀ T : ℝ, 10 ≤ T →
    Set.ncard {n : ZeroIndex | |(zero n).im| ≤ T} ≤
      Nat.floor (2 * T ^ 2)

def D (γ : ℝ) : ℝ := γ + 10

def centre (m : ℝ) : ℝ := 16 * m

def gaussianDensity (m y : ℝ) : ℝ :=
  Real.exp (-(y - centre m) ^ 2 / (4 * m)) /
    Real.sqrt (4 * Real.pi * m)

def gaussianCoordinate (m y : ℝ) : ℝ := (y - centre m) / (2 * m)

def physicalEnvelope (m γ y : ℝ) : ℝ :=
  3 * (y + 1) * (gaussianCoordinate m y ^ 2 + γ ^ 2 + 1) *
    gaussianDensity m y

def resolventCoefficient (ρ : ℂ) (h : ℝ) : ℂ :=
  (ρ * (1 + h - ρ))⁻¹

def spectralKernel (Z : CompleteZeroFamily) (h y : ℝ) : ℂ :=
  ∑' n, Complex.exp ((Z.zero n - h) * y) *
    resolventCoefficient (Z.zero n) h

def lowHIntegrand (Z : CompleteZeroFamily) (m γ y : ℝ) : ℂ :=
  (physicalEnvelope m γ y : ℂ) *
    ∫ h in Icc (0 : ℝ) 2, ((1 + h : ℝ) : ℂ) * spectralKernel Z h y

def lowHMean (Z : CompleteZeroFamily) (m γ : ℝ) : ℂ :=
  ∫ y in Ioi (1 : ℝ), lowHIntegrand Z m γ y

def zeroJointMajorant (Z : CompleteZeroFamily) (m γ : ℝ) (p : ℝ × ℝ) : ℝ :=
  ‖(physicalEnvelope m γ p.1 : ℂ)‖ * (1 + |p.2|) *
    ∑' n, ‖Complex.exp ((Z.zero n - p.2) * p.1)‖ *
      ‖resolventCoefficient (Z.zero n) p.2‖

def lowHProductIntegrand (Z : CompleteZeroFamily) (m γ : ℝ) (p : ℝ × ℝ) : ℂ :=
  (physicalEnvelope m γ p.1 : ℂ) *
    ((1 + p.2 : ℝ) : ℂ) * spectralKernel Z p.2 p.1

/-- The denominator is nonzero on the full h-window.  The height hypothesis is
    used here, rather than any reality or parity property of the zero. -/
lemma resolvent_denominator_ne_zero
    (Z : CompleteZeroFamily) (n : ZeroIndex) (h : ℝ) (hh : h ∈ Icc (0 : ℝ) 2) :
    (Z.zero n) * (1 + h - Z.zero n) ≠ 0 := by
  have him : (Z.zero n).im ≠ 0 := by
    intro hz
    have := Z.height n
    simp only [hz, abs_zero] at this
    linarith
  have hfirst : Z.zero n ≠ 0 := by
    intro hz
    have := congrArg Complex.im hz
    simpa using him this
  have hsecond : (1 + h - Z.zero n : ℂ) ≠ 0 := by
    intro hz
    have hz' := congrArg Complex.im hz
    simp at hz'
    have hz'' : (Z.zero n).im = 0 := by linarith
    exact him hz''
  exact mul_ne_zero hfirst hsecond

/-- Uniform reciprocal-square control, with the actual nonzero denominator
    proved before the norm comparison. -/
lemma resolvent_norm_le_reciprocal_square
    (Z : CompleteZeroFamily) (n : ZeroIndex) (h : ℝ) (hh : h ∈ Icc (0 : ℝ) 2) :
    ‖resolventCoefficient (Z.zero n) h‖ ≤ ((Z.zero n).im)⁻¹ ^ 2 := by
  have hden := resolvent_denominator_ne_zero Z n h hh
  have him : (Z.zero n).im ≠ 0 := by
    intro hz
    have ht := Z.height n
    simp only [hz, abs_zero] at ht
    linarith
  have himpos : 0 < |(Z.zero n).im| := abs_pos.mpr him
  have hdenpos : 0 < ‖Z.zero n‖ * ‖(1 + h - Z.zero n : ℂ)‖ := by
    simpa only [norm_mul] using (norm_pos_iff.mpr hden)
  have hρ : |(Z.zero n).im| ≤ ‖Z.zero n‖ := Complex.abs_im_le_norm _
  have hρ' : |(Z.zero n).im| ≤ ‖(1 + h - Z.zero n : ℂ)‖ := by
    have ht := Complex.abs_im_le_norm ((1 + h : ℂ) - Z.zero n)
    simpa using ht
  have hprod : |(Z.zero n).im| ^ 2 ≤
      ‖Z.zero n‖ * ‖(1 + h - Z.zero n : ℂ)‖ := by
    simpa only [pow_two] using mul_le_mul hρ hρ' (abs_nonneg _) (norm_nonneg _)
  rw [resolventCoefficient, norm_inv, norm_mul]
  calc
    (‖Z.zero n‖ * ‖1 + ↑h - Z.zero n‖)⁻¹ ≤
        (|(Z.zero n).im| ^ 2)⁻¹ := by
          exact (inv_le_inv₀ hdenpos (sq_pos_of_pos himpos)).mpr hprod
    _ = ((Z.zero n).im)⁻¹ ^ 2 := by
      simp only [sq_abs, inv_pow]

/-- The all-real exponential comparison used by the series majorant. -/
lemma norm_exp_shift_le_exp_add_exp_neg_two
    (Z : CompleteZeroFamily) (n : ZeroIndex) (h y : ℝ)
    (hh : h ∈ Icc (0 : ℝ) 2) :
    ‖Complex.exp ((Z.zero n - h) * y)‖ ≤
      Real.exp y + Real.exp (-2 * y) := by
  rw [Complex.norm_exp]
  by_cases hy : 0 ≤ y
  · have hcoef : (Z.zero n).re - h ≤ 1 := by
      linarith [Z.strip n |>.2, hh.1]
    have heq : ((Z.zero n - h) * y : ℂ).re = ((Z.zero n).re - h) * y := by
      simp [Complex.mul_re]
    rw [heq]
    calc
      Real.exp (((Z.zero n).re - h) * y) ≤ Real.exp y := by
        exact Real.exp_le_exp.mpr (by simpa using mul_le_mul_of_nonneg_right hcoef hy)
      _ ≤ Real.exp y + Real.exp (-2 * y) :=
        le_add_of_nonneg_right (Real.exp_pos _).le
  · have hy' : y ≤ 0 := le_of_not_ge hy
    have hcoef : -2 ≤ (Z.zero n).re - h := by
      linarith [Z.strip n |>.1, hh.2]
    have heq : ((Z.zero n - h) * y : ℂ).re = ((Z.zero n).re - h) * y := by
      simp [Complex.mul_re]
    rw [heq]
    calc
      Real.exp (((Z.zero n).re - h) * y) ≤ Real.exp (-2 * y) := by
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right hcoef hy')
      _ ≤ Real.exp y + Real.exp (-2 * y) :=
        le_add_of_nonneg_left (Real.exp_pos _).le

lemma zero_term_norm_le
    (Z : CompleteZeroFamily) (n : ZeroIndex) (h y : ℝ)
    (hh : h ∈ Icc (0 : ℝ) 2) :
    ‖Complex.exp ((Z.zero n - h) * y)‖ *
        ‖resolventCoefficient (Z.zero n) h‖ ≤
      (Real.exp y + Real.exp (-2 * y)) * ((Z.zero n).im)⁻¹ ^ 2 := by
  exact mul_le_mul (norm_exp_shift_le_exp_add_exp_neg_two Z n h y hh)
    (resolvent_norm_le_reciprocal_square Z n h hh)
    (norm_nonneg _) (by positivity)

lemma zero_series_summable_and_bound
    (Z : CompleteZeroFamily) (h y : ℝ)
    (hh : h ∈ Icc (0 : ℝ) 2) :
    Summable (fun n : ZeroIndex =>
      ‖Complex.exp ((Z.zero n - h) * y)‖ *
        ‖resolventCoefficient (Z.zero n) h‖) ∧
      (∑' n, ‖Complex.exp ((Z.zero n - h) * y)‖ *
        ‖resolventCoefficient (Z.zero n) h‖) ≤
      (Real.exp y + Real.exp (-2 * y)) *
        (∑' n, ((Z.zero n).im)⁻¹ ^ 2) := by
  let c : ℝ := Real.exp y + Real.exp (-2 * y)
  have hbound : ∀ k : ZeroIndex,
      ‖Complex.exp ((Z.zero k - h) * y)‖ *
          ‖resolventCoefficient (Z.zero k) h‖ ≤
        c * ((Z.zero k).im)⁻¹ ^ 2 := by
    intro k
    exact zero_term_norm_le Z k h y hh
  have hsum : Summable (fun k : ZeroIndex =>
      ‖Complex.exp ((Z.zero k - h) * y)‖ *
        ‖resolventCoefficient (Z.zero k) h‖) := by
    refine Summable.of_nonneg_of_le (fun k => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      hbound ?_
    simpa [c] using Z.reciprocalSquare.mul_left c
  refine ⟨hsum, ?_⟩
  simpa only [c, tsum_mul_left] using hsum.tsum_le_tsum hbound
    (Z.reciprocalSquare.mul_left c)

/-- The two real endpoint norms inherit integrability from the preserved
    certificate-free all-complex cubic Gaussian theorem. -/
lemma physical_exp_norm_integrable
    (m γ : ℝ) (hm : 0 < m) (z : ℂ) :
    Integrable (fun y : ℝ =>
      ‖(physicalEnvelope m γ y : ℂ)‖ * ‖Complex.exp (z * (y : ℂ))‖) := by
  have hi :=
    (D5.S3.Arith.Robin.CompleteLowHGaussianMoment.cubic_gaussian_integrable
      m γ hm z).norm.const_mul (3 : ℝ)
  refine hi.congr (ae_of_all volume fun y => ?_)
  simp only [physicalEnvelope, gaussianCoordinate, gaussianDensity, centre,
    D5.S3.Arith.Robin.CompleteLowHGaussianMoment.gaussianCoordinate,
    D5.S3.Arith.Robin.CompleteLowHGaussianMoment.gaussianDensity,
    D5.S3.Arith.Robin.CompleteLowHGaussianMoment.centre,
    norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
  ring

lemma zero_joint_majorant_measurable (Z : CompleteZeroFamily) (m γ : ℝ) :
    Measurable (zeroJointMajorant Z m γ) := by
  have hsum : Measurable (fun p : ℝ × ℝ =>
      ∑' n, ‖Complex.exp ((Z.zero n - p.2) * p.1)‖ *
        ‖resolventCoefficient (Z.zero n) p.2‖) := by
    apply Measurable.tsum
    intro n
    unfold resolventCoefficient
    fun_prop
  have hp : Measurable (fun p : ℝ × ℝ =>
      ‖(physicalEnvelope m γ p.1 : ℂ)‖ * (1 + |p.2|)) := by
    unfold physicalEnvelope gaussianCoordinate gaussianDensity centre
    fun_prop
  convert hp.mul hsum using 1 <;> ext p <;> rfl

lemma lowH_product_measurable (Z : CompleteZeroFamily) (m γ : ℝ) :
    Measurable (lowHProductIntegrand Z m γ) := by
  have hsum : Measurable (fun p : ℝ × ℝ =>
      ∑' n, Complex.exp ((Z.zero n - p.2) * p.1) *
        resolventCoefficient (Z.zero n) p.2) := by
    apply Measurable.tsum
    intro n
    unfold resolventCoefficient
    fun_prop
  have hp : Measurable (fun p : ℝ × ℝ =>
      (physicalEnvelope m γ p.1 : ℂ) * ((1 + p.2 : ℝ) : ℂ)) := by
    unfold physicalEnvelope gaussianCoordinate gaussianDensity centre
    fun_prop
  convert hp.mul hsum using 1 <;> ext p <;> rfl

/-- All-real y and the original closed h-window are controlled by the two
    Gaussian endpoints and the complete reciprocal-square series. -/
theorem complete_zero_joint_majorant_integrable_full
    (Z : CompleteZeroFamily) (m γ : ℝ) (hm : 0 < m) :
    Integrable (zeroJointMajorant Z m γ)
      (volume.prod (volume.restrict (Icc (0 : ℝ) 2))) := by
  let μ : Measure ℝ := volume
  let ν : Measure ℝ := volume.restrict (Icc (0 : ℝ) 2)
  change Integrable (zeroJointMajorant Z m γ) (μ.prod ν)
  have h1 := physical_exp_norm_integrable m γ hm (1 : ℂ)
  have h2 := physical_exp_norm_integrable m γ hm (-2 : ℂ)
  have hbase : Integrable (fun y : ℝ =>
      ‖(physicalEnvelope m γ y : ℂ)‖ *
        (Real.exp y + Real.exp (-2 * y))) μ := by
    have h1' : Integrable (fun y : ℝ =>
        ‖(physicalEnvelope m γ y : ℂ)‖ * Real.exp y) μ := by
      simpa [Complex.norm_exp] using h1
    have h2' : Integrable (fun y : ℝ =>
        ‖(physicalEnvelope m γ y : ℂ)‖ * Real.exp (-2 * y)) μ := by
      simpa [Complex.norm_exp] using h2
    convert h1'.add h2' using 1 <;> ext y <;> simp only [Pi.add_apply, mul_add]
  have hh : Integrable (fun h : ℝ => 1 + |h|) ν := by
    dsimp [ν]
    exact (continuous_const.add continuous_abs).integrableOn_Icc
  have hprod : Integrable (fun p : ℝ × ℝ =>
      (‖(physicalEnvelope m γ p.1 : ℂ)‖ *
        (Real.exp p.1 + Real.exp (-2 * p.1))) * (1 + |p.2|))
      (μ.prod ν) := by
    exact hbase.mul_prod hh
  let R : ℝ := ∑' n, ((Z.zero n).im)⁻¹ ^ 2
  have hbound : Integrable (fun p : ℝ × ℝ =>
      ((‖(physicalEnvelope m γ p.1 : ℂ)‖ *
        (Real.exp p.1 + Real.exp (-2 * p.1))) * (1 + |p.2|)) * R)
      (μ.prod ν) := by
    simpa [R, mul_assoc, mul_left_comm, mul_comm] using hprod.const_mul R
  have hmeas : Measurable (zeroJointMajorant Z m γ) :=
    zero_joint_majorant_measurable Z m γ
  refine Integrable.mono_nonneg hbound hmeas.aestronglyMeasurable ?_ ?_
  · exact ae_of_all _ fun p => by
      unfold zeroJointMajorant
      exact mul_nonneg (mul_nonneg (norm_nonneg _) (by positivity))
        (tsum_nonneg fun n => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hBmeas : Measurable (fun p : ℝ × ℝ =>
      ((‖(physicalEnvelope m γ p.1 : ℂ)‖ *
        (Real.exp p.1 + Real.exp (-2 * p.1))) * (1 + |p.2|)) * R) := by
    unfold physicalEnvelope gaussianCoordinate gaussianDensity centre
    fun_prop
  apply (Measure.ae_prod_iff_ae_ae
    (measurableSet_le hmeas hBmeas)).2
  exact (ae_of_all μ fun y => (ae_restrict_mem measurableSet_Icc).mono fun h hh => by
    dsimp [zeroJointMajorant, R]
    have hsum : (∑' n, ‖Complex.exp ((Z.zero n - h) * y)‖ *
        ‖resolventCoefficient (Z.zero n) h‖) ≤
        (Real.exp y + Real.exp (-2 * y)) * R := by
      simpa [R] using (zero_series_summable_and_bound Z h y hh).2
    have hfactor : 0 ≤ ‖(physicalEnvelope m γ y : ℂ)‖ * (1 + |h|) := by positivity
    calc
      ‖(physicalEnvelope m γ y : ℂ)‖ * (1 + |h|) *
              (∑' n, ‖Complex.exp ((Z.zero n - h) * y)‖ *
                ‖resolventCoefficient (Z.zero n) h‖) ≤
            ‖(physicalEnvelope m γ y : ℂ)‖ * (1 + |h|) *
              ((Real.exp y + Real.exp (-2 * y)) * R) :=
          mul_le_mul_of_nonneg_left hsum hfactor
      _ = ((‖(physicalEnvelope m γ y : ℂ)‖ *
              (Real.exp y + Real.exp (-2 * y))) * (1 + |h|)) * R := by ring)

theorem complete_zero_joint_absolute_majorant
    (Z : CompleteZeroFamily) (m γ : ℝ) (hm : 0 < m) :
    Integrable (fun p : ℝ × ℝ =>
      ‖(physicalEnvelope m γ p.1 : ℂ)‖ *
        (1 + |p.2|) *
        ∑' n, ‖Complex.exp ((Z.zero n - p.2) * p.1)‖ *
          ‖resolventCoefficient (Z.zero n) p.2‖)
      ((volume.restrict (Ioi (1 : ℝ))).prod
        (volume.restrict (Icc (0 : ℝ) 2))) := by
  change Integrable (zeroJointMajorant Z m γ)
    ((volume.restrict (Ioi (1 : ℝ))).prod
      (volume.restrict (Icc (0 : ℝ) 2)))
  exact (complete_zero_joint_majorant_integrable_full Z m γ hm).mono_measure
    (Measure.prod_mono Measure.restrict_le_self le_rfl)


lemma complete_zero_lowH_product_integrable
    (Z : CompleteZeroFamily) (m γ : ℝ) (hm : 0 < m) :
    Integrable (lowHProductIntegrand Z m γ)
      ((volume.restrict (Ioi (1 : ℝ))).prod
        (volume.restrict (Icc (0 : ℝ) 2))) := by
  let μ : Measure ℝ := volume.restrict (Ioi (1 : ℝ))
  let ν : Measure ℝ := volume.restrict (Icc (0 : ℝ) 2)
  change Integrable (lowHProductIntegrand Z m γ) (μ.prod ν)
  have hj := complete_zero_joint_absolute_majorant Z m γ hm
  change Integrable (zeroJointMajorant Z m γ) (μ.prod ν) at hj
  have hmeas : Measurable (lowHProductIntegrand Z m γ) :=
    lowH_product_measurable Z m γ
  have hnorm : ∀ᵐ p ∂(μ.prod ν),
      ‖lowHProductIntegrand Z m γ p‖ ≤ zeroJointMajorant Z m γ p := by
    have hleft : Measurable (fun p : ℝ × ℝ =>
        ‖lowHProductIntegrand Z m γ p‖) := hmeas.norm
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_le hleft (zero_joint_majorant_measurable Z m γ))).2
    exact (ae_restrict_mem measurableSet_Ioi).mono fun y hy =>
      (ae_restrict_mem measurableSet_Icc).mono fun h hh => by
        dsimp [lowHProductIntegrand, zeroJointMajorant]
        have hs := (zero_series_summable_and_bound Z h y hh).1
        calc
          ‖(physicalEnvelope m γ y : ℂ) * ((1 + h : ℝ) : ℂ) *
              spectralKernel Z h y‖ ≤
              ‖(physicalEnvelope m γ y : ℂ)‖ *
                ‖((1 + h : ℝ) : ℂ)‖ *
                (∑' n, ‖Complex.exp ((Z.zero n - h) * y)‖ *
                  ‖resolventCoefficient (Z.zero n) h‖) := by
            rw [norm_mul, norm_mul]
            have hsn : Summable (fun n : ZeroIndex =>
                ‖Complex.exp ((Z.zero n - h) * y) *
                  resolventCoefficient (Z.zero n) h‖) := by
              simpa only [norm_mul] using hs
            have hkernel : ‖spectralKernel Z h y‖ ≤
                ∑' n, ‖Complex.exp ((Z.zero n - h) * y)‖ *
                  ‖resolventCoefficient (Z.zero n) h‖ := by
              simpa only [spectralKernel, norm_mul] using norm_tsum_le_tsum_norm hsn
            exact mul_le_mul_of_nonneg_left hkernel (by positivity)
          _ = ‖(physicalEnvelope m γ y : ℂ)‖ * (1 + |h|) *
                (∑' n, ‖Complex.exp ((Z.zero n - h) * y)‖ *
                  ‖resolventCoefficient (Z.zero n) h‖) := by
            have hw : ‖((1 + h : ℝ) : ℂ)‖ = 1 + |h| := by
              rw [Complex.norm_real, Real.norm_eq_abs,
                abs_of_nonneg (by linarith [hh.1] : 0 ≤ 1 + h), abs_of_nonneg hh.1]
            rw [hw]
  exact Integrable.mono' hj hmeas.aestronglyMeasurable hnorm

lemma complete_zero_lowH_integrable
    (Z : CompleteZeroFamily) (m γ : ℝ) (hm : 0 < m) :
    IntegrableOn (lowHIntegrand Z m γ) (Ioi (1 : ℝ)) := by
  let μ : Measure ℝ := volume.restrict (Ioi (1 : ℝ))
  let ν : Measure ℝ := volume.restrict (Icc (0 : ℝ) 2)
  change IntegrableOn (lowHIntegrand Z m γ) (Ioi (1 : ℝ))
  have hp := complete_zero_lowH_product_integrable Z m γ hm
  have hi := hp.integral_prod_left
  refine hi.congr (ae_of_all μ fun y => ?_)
  simpa [μ, ν, lowHProductIntegrand, lowHIntegrand, integral_const_mul,
    spectralKernel, mul_assoc]

/- The two extension terms are kept as named integrals rather than absorbed
   into an absolute-value integral.  The temporary envelope is allowed to be
   negative for y < -1; its certificate uses its absolute value. -/
def positiveExtension (Z : CompleteZeroFamily) (m γ : ℝ) : ℂ :=
  -∫ y in Ioc (0 : ℝ) 1, lowHIntegrand Z m γ y

def negativeExtension (Z : CompleteZeroFamily) (m γ : ℝ) : ℂ :=
  -∫ y in Iio (0 : ℝ), lowHIntegrand Z m γ y

def cubicPolynomial (m γ : ℝ) (z : ℂ) : ℂ :=
  (centre m + 2 * m * z + 1) *
      (z ^ 2 + γ ^ 2 + 1 + 1 / (2 * m)) + 2 * z

def dividedCubicCoefficient (m γ : ℝ) (ρ : ℂ) (h : ℝ) : ℂ :=
  resolventCoefficient ρ h *
    (cubicPolynomial m γ (ρ - h) * Complex.exp
      (m * (ρ - h) ^ 2 + centre m * (ρ - h)))

def shellWeight (m : ℝ) (ρ : ℂ) : ℝ :=
  (|(ρ.im)| + 1) * Real.exp (-m * (ρ.im) ^ 2)

def shellSum (Z : CompleteZeroFamily) (m : ℝ) : ℝ :=
  ∑' n, shellWeight m (Z.zero n)

def shellTerm (Z : CompleteZeroFamily) (m γ : ℝ) (n : ZeroIndex) : ℂ :=
  ∫ h in Icc (0 : ℝ) 2,
    (3 : ℂ) * ((1 + h : ℝ) : ℂ) *
      dividedCubicCoefficient m γ (Z.zero n) h

def completeRealLineMean (Z : CompleteZeroFamily) (m γ : ℝ) : ℂ :=
  ∑' n, shellTerm Z m γ n

/-- The complete multiplicity-indexed Gaussian shell series is summable, with
    its original quantitative bound.  Only the existing height, finite-count
    and two-sided count fields are used.  Finite sums are partitioned first,
    so no convergence or enumeration-order hypothesis enters the argument. -/
theorem shell_summable_and_count_bound (Z : CompleteZeroFamily) (m : ℝ)
    (hm : 1 ≤ m) :
    Summable (fun n => shellWeight m (Z.zero n)) ∧
      shellSum Z m ≤ 10000 * Real.exp (-100 * m) := by
  classical
  have hm0 : 0 ≤ m := by linarith
  have hnonneg : 0 ≤ (fun n => shellWeight m (Z.zero n)) := by
    intro n
    unfold shellWeight
    positivity
  have hpoly (k : ℕ) :
      2 * (11 + (k : ℝ)) ^ 2 * (12 + (k : ℝ)) ≤ 2904 * (8 : ℝ) ^ k := by
    induction k with
    | zero => norm_num
    | succ k ih =>
      have hk0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
      calc
        2 * (11 + ((k + 1 : ℕ) : ℝ)) ^ 2 * (12 + ((k + 1 : ℕ) : ℝ)) =
            2 * (12 + (k : ℝ)) ^ 2 * (13 + (k : ℝ)) := by
          push_cast
          ring
        _ ≤ 2 * (2 * (11 + (k : ℝ))) ^ 2 * (2 * (12 + (k : ℝ))) := by
          gcongr <;> linarith
        _ = 8 * (2 * (11 + (k : ℝ)) ^ 2 * (12 + (k : ℝ))) := by ring
        _ ≤ 8 * (2904 * (8 : ℝ) ^ k) :=
          mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = 2904 * (8 : ℝ) ^ (k + 1) := by rw [pow_succ]; ring
  have hdecay (k : ℕ) :
      Real.exp (-m * (10 + (k : ℝ)) ^ 2) ≤
        Real.exp (-100 * m) * Real.exp (-20) ^ k := by
    have hk0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
    have hmk : 0 ≤ (m - 1) * (k : ℝ) := mul_nonneg (by linarith) hk0
    have hmk2 : 0 ≤ m * (k : ℝ) ^ 2 := mul_nonneg hm0 (sq_nonneg _)
    calc
      Real.exp (-m * (10 + (k : ℝ)) ^ 2) ≤
          Real.exp (-100 * m + (k : ℝ) * (-20)) := by
        apply Real.exp_le_exp.mpr
        nlinarith
      _ = Real.exp (-100 * m) * Real.exp (-20) ^ k := by
        rw [Real.exp_add, Real.exp_nat_mul]
  have hratio : 8 * Real.exp (-20) ≤ (1 / 2 : ℝ) := by
    rw [Real.exp_neg, ← div_eq_mul_inv]
    apply (div_le_iff₀ (Real.exp_pos (20 : ℝ))).mpr
    linarith [Real.add_one_le_exp (20 : ℝ)]
  have hgeom : HasSum
      (fun k : ℕ => (2904 * Real.exp (-100 * m)) * (1 / 2 : ℝ) ^ k)
      (5808 * Real.exp (-100 * m)) := by
    convert hasSum_geometric_two.mul_left (2904 * Real.exp (-100 * m)) using 1 <;> ring
  have hshell (k : ℕ) (s : Finset ZeroIndex)
      (hs : ∀ n ∈ s, 10 + (k : ℝ) ≤ |(Z.zero n).im| ∧
        |(Z.zero n).im| < 11 + (k : ℝ)) :
      (∑ n ∈ s, shellWeight m (Z.zero n)) ≤
        (2904 * Real.exp (-100 * m)) * (1 / 2 : ℝ) ^ k := by
    have hk0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
    have hT : 10 ≤ 11 + (k : ℝ) := by linarith
    have hsub : (s : Set ZeroIndex) ⊆
        {n : ZeroIndex | |(Z.zero n).im| ≤ 11 + (k : ℝ)} := by
      intro n hn
      exact (hs n hn).2.le
    have hcard_nat : s.card ≤ Nat.floor (2 * (11 + (k : ℝ)) ^ 2) := by
      have hc := Set.ncard_le_ncard hsub (Z.finite_count_shell _ hT)
      rw [Set.ncard_coe_finset] at hc
      exact hc.trans (Z.count_both _ hT)
    have hcard : (s.card : ℝ) ≤ 2 * (11 + (k : ℝ)) ^ 2 :=
      (Nat.cast_le.mpr hcard_nat).trans (Nat.floor_le (by positivity))
    have hpoint (n : ZeroIndex) (hn : n ∈ s) :
        shellWeight m (Z.zero n) ≤
          (12 + (k : ℝ)) * Real.exp (-m * (10 + (k : ℝ)) ^ 2) := by
      obtain ⟨hlo, hhi⟩ := hs n hn
      have hsq : (10 + (k : ℝ)) ^ 2 ≤ (Z.zero n).im ^ 2 := by
        have hh := mul_nonneg (sub_nonneg.mpr hlo)
          (add_nonneg (abs_nonneg (Z.zero n).im)
            (show 0 ≤ 10 + (k : ℝ) by positivity))
        nlinarith [sq_abs (Z.zero n).im]
      have he : Real.exp (-m * (Z.zero n).im ^ 2) ≤
          Real.exp (-m * (10 + (k : ℝ)) ^ 2) := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_left hsq hm0]
      unfold shellWeight
      exact mul_le_mul (by linarith) he (Real.exp_nonneg _) (by positivity)
    calc
      (∑ n ∈ s, shellWeight m (Z.zero n)) ≤
          ∑ _n ∈ s, (12 + (k : ℝ)) * Real.exp (-m * (10 + (k : ℝ)) ^ 2) :=
        Finset.sum_le_sum hpoint
      _ = (s.card : ℝ) *
          ((12 + (k : ℝ)) * Real.exp (-m * (10 + (k : ℝ)) ^ 2)) := by simp
      _ ≤ (2 * (11 + (k : ℝ)) ^ 2) *
          ((12 + (k : ℝ)) * Real.exp (-m * (10 + (k : ℝ)) ^ 2)) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = (2 * (11 + (k : ℝ)) ^ 2 * (12 + (k : ℝ))) *
          Real.exp (-m * (10 + (k : ℝ)) ^ 2) := by ring
      _ ≤ (2904 * (8 : ℝ) ^ k) *
          (Real.exp (-100 * m) * Real.exp (-20) ^ k) :=
        mul_le_mul (hpoly k) (hdecay k) (Real.exp_nonneg _) (by positivity)
      _ = (2904 * Real.exp (-100 * m)) * (8 * Real.exp (-20)) ^ k := by
        rw [mul_pow]
        ring
      _ ≤ (2904 * Real.exp (-100 * m)) * (1 / 2 : ℝ) ^ k := by
        gcongr <;> exact hratio
  have huniform (s : Finset ZeroIndex) :
      (∑ n ∈ s, shellWeight m (Z.zero n)) ≤ 5808 * Real.exp (-100 * m) := by
    -- floor(|Im rho| - 10) = floor(|Im rho|) - 10; using the shifted
    -- expression directly avoids natural subtraction in the endpoint proof.
    let b : ZeroIndex → ℕ := fun n => Nat.floor (|(Z.zero n).im| - 10)
    have hbounds (n : ZeroIndex) :
        10 + (b n : ℝ) ≤ |(Z.zero n).im| ∧
          |(Z.zero n).im| < 11 + (b n : ℝ) := by
      have hlo := Nat.floor_le (show 0 ≤ |(Z.zero n).im| - 10 by
        linarith [Z.height n])
      have hhi := Nat.lt_floor_add_one (|(Z.zero n).im| - 10)
      change 10 + (Nat.floor (|(Z.zero n).im| - 10) : ℝ) ≤ _ ∧
        _ < 11 + (Nat.floor (|(Z.zero n).im| - 10) : ℝ)
      constructor <;> linarith
    calc
      (∑ n ∈ s, shellWeight m (Z.zero n)) =
          ∑ k ∈ s.image b, ∑ n ∈ s.filter (fun n => b n = k),
            shellWeight m (Z.zero n) :=
        (Finset.sum_fiberwise_of_maps_to
          (fun n hn => Finset.mem_image_of_mem b hn) _).symm
      _ ≤ ∑ k ∈ s.image b, (2904 * Real.exp (-100 * m)) * (1 / 2 : ℝ) ^ k := by
        apply Finset.sum_le_sum
        intro k _hk
        apply hshell k (s.filter (fun n => b n = k))
        intro n hn
        have heq := (Finset.mem_filter.mp hn).2
        simpa only [heq] using hbounds n
      _ ≤ ∑' k : ℕ, (2904 * Real.exp (-100 * m)) * (1 / 2 : ℝ) ^ k :=
        hgeom.summable.sum_le_tsum _ (fun _ _ => by positivity)
      _ = 5808 * Real.exp (-100 * m) := hgeom.tsum_eq
  refine ⟨summable_of_sum_le hnonneg huniform, ?_⟩
  exact (Real.tsum_le_of_sum_le hnonneg huniform).trans
    (mul_le_mul_of_nonneg_right (by norm_num : (5808 : ℝ) ≤ 10000) (Real.exp_nonneg _))

private def fullLineTerm (Z : CompleteZeroFamily) (m γ : ℝ)
    (n : ZeroIndex) (p : ℝ × ℝ) : ℂ :=
  (physicalEnvelope m γ p.1 : ℂ) * ((1 + p.2 : ℝ) : ℂ) *
    (Complex.exp ((Z.zero n - p.2) * p.1) *
      resolventCoefficient (Z.zero n) p.2)

private theorem fullLineTerm_measurable
    (Z : CompleteZeroFamily) (m γ : ℝ) (n : ZeroIndex) :
    Measurable (fullLineTerm Z m γ n) := by
  unfold fullLineTerm physicalEnvelope gaussianCoordinate gaussianDensity
    centre resolventCoefficient
  fun_prop

private theorem ae_fullLine_h :
    ∀ᵐ p : ℝ × ℝ ∂(volume.prod (volume.restrict (Icc (0 : ℝ) 2))),
      p.2 ∈ Icc (0 : ℝ) 2 := by
  apply (Measure.ae_prod_iff_ae_ae
    (measurableSet_Icc.preimage measurable_snd)).2
  exact ae_of_all volume fun _ => ae_restrict_mem measurableSet_Icc

/-- This is absolute norm summability, not just convergence of the complex
    series.  The equality uses the *actual* factor 1+h on the original window. -/
private theorem fullLineTerm_norm_series
    (Z : CompleteZeroFamily) (m γ y h : ℝ) (hh : h ∈ Icc (0 : ℝ) 2) :
    Summable (fun n => ‖fullLineTerm Z m γ n (y, h)‖) ∧
      (∑' n, ‖fullLineTerm Z m γ n (y, h)‖) =
        zeroJointMajorant Z m γ (y, h) := by
  let c : ℝ := ‖(physicalEnvelope m γ y : ℂ)‖ * (1 + |h|)
  have hweight : ‖((1 + h : ℝ) : ℂ)‖ = 1 + |h| := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (show 0 ≤ 1 + h by linarith [hh.1]), abs_of_nonneg hh.1]
  have heq (n : ZeroIndex) :
      ‖fullLineTerm Z m γ n (y, h)‖ = c *
        (‖Complex.exp ((Z.zero n - h) * y)‖ *
          ‖resolventCoefficient (Z.zero n) h‖) := by
    simp only [fullLineTerm, norm_mul, hweight, c]
  have hs := (zero_series_summable_and_bound Z h y hh).1
  have hn : Summable (fun n => ‖fullLineTerm Z m γ n (y, h)‖) := by
    simpa only [heq] using hs.mul_left c
  refine ⟨hn, ?_⟩
  calc
    (∑' n, ‖fullLineTerm Z m γ n (y, h)‖) =
        ∑' n, c * (‖Complex.exp ((Z.zero n - h) * y)‖ *
          ‖resolventCoefficient (Z.zero n) h‖) := tsum_congr heq
    _ = c * (∑' n, ‖Complex.exp ((Z.zero n - h) * y)‖ *
        ‖resolventCoefficient (Z.zero n) h‖) := (hs.hasSum.mul_left c).tsum_eq
    _ = zeroJointMajorant Z m γ (y, h) := rfl

/-- The norm series itself is integrable on the *full* product measure.
    The positive-half-line certificate is not an input to this proof. -/
private theorem fullLine_norm_series_integrable
    (Z : CompleteZeroFamily) (m γ : ℝ) (hm : 0 < m) :
    Integrable (fun p : ℝ × ℝ => ∑' n, ‖fullLineTerm Z m γ n p‖)
      (volume.prod (volume.restrict (Icc (0 : ℝ) 2))) := by
  refine (complete_zero_joint_majorant_integrable_full Z m γ hm).congr ?_
  filter_upwards [ae_fullLine_h] with p hp
  exact (fullLineTerm_norm_series Z m γ p.1 p.2 hp).2.symm

/-- Every term is Bochner integrable, the sum is Bochner integrable, and the
    integral and all-index sum commute.  Finite subsets only prove a uniform
    bound for the integral-norm series; no finite-zero replacement is made. -/
private theorem fullLine_absolute_exchange
    (Z : CompleteZeroFamily) (m γ : ℝ) (hm : 0 < m) :
    (∀ n, Integrable (fullLineTerm Z m γ n)
      (volume.prod (volume.restrict (Icc (0 : ℝ) 2)))) ∧
    Integrable (fun p : ℝ × ℝ => ∑' n, fullLineTerm Z m γ n p)
      (volume.prod (volume.restrict (Icc (0 : ℝ) 2))) ∧
    (∫ p : ℝ × ℝ, (∑' n, fullLineTerm Z m γ n p)
      ∂(volume.prod (volume.restrict (Icc (0 : ℝ) 2)))) =
      ∑' n, ∫ p : ℝ × ℝ, fullLineTerm Z m γ n p
        ∂(volume.prod (volume.restrict (Icc (0 : ℝ) 2))) := by
  let μ : Measure (ℝ × ℝ) := volume.prod (volume.restrict (Icc (0 : ℝ) 2))
  let N : ℝ × ℝ → ℝ := fun p => ∑' n, ‖fullLineTerm Z m γ n p‖
  have hN : Integrable N μ := fullLine_norm_series_integrable Z m γ hm
  have hterm (n : ZeroIndex) : Integrable (fullLineTerm Z m γ n) μ := by
    refine hN.mono' (fullLineTerm_measurable Z m γ n).aestronglyMeasurable ?_
    filter_upwards [ae_fullLine_h] with p hp
    have hs := (fullLineTerm_norm_series Z m γ p.1 p.2 hp).1
    simpa [N] using hs.sum_le_tsum ({n} : Finset ZeroIndex)
      (fun _ _ => norm_nonneg _)
  have hsum_meas : Measurable (fun p : ℝ × ℝ => ∑' n, fullLineTerm Z m γ n p) :=
    Measurable.tsum (fun n => fullLineTerm_measurable Z m γ n)
  have hsum : Integrable (fun p : ℝ × ℝ => ∑' n, fullLineTerm Z m γ n p) μ := by
    refine hN.mono' hsum_meas.aestronglyMeasurable ?_
    filter_upwards [ae_fullLine_h] with p hp
    exact norm_tsum_le_tsum_norm (fullLineTerm_norm_series Z m γ p.1 p.2 hp).1
  have hnorm_integrals : Summable (fun n => ∫ p, ‖fullLineTerm Z m γ n p‖ ∂μ) := by
    apply summable_of_sum_le (fun n => integral_nonneg (fun _ => norm_nonneg _))
    intro s
    calc
      (∑ n ∈ s, ∫ p, ‖fullLineTerm Z m γ n p‖ ∂μ) =
          ∫ p, ∑ n ∈ s, ‖fullLineTerm Z m γ n p‖ ∂μ :=
        (integral_finsetSum s (fun n _ => (hterm n).norm)).symm
      _ ≤ ∫ p, N p ∂μ := by
        refine integral_mono_ae
          (integrable_finsetSum s (fun n _ => (hterm n).norm)) hN ?_
        filter_upwards [ae_fullLine_h] with p hp
        exact (fullLineTerm_norm_series Z m γ p.1 p.2 hp).1.sum_le_tsum s
          (fun _ _ => norm_nonneg _)
  refine ⟨hterm, hsum, ?_⟩
  -- This pinned API invokes integral_tsum after proving the ENNReal
  -- norm-integral sum is finite; its equality is oriented tsum = integral.
  exact (integral_tsum_of_summable_integral_norm hterm hnorm_integrals).symm

private theorem fullLine_tsum_eq_product
    (Z : CompleteZeroFamily) (m γ y h : ℝ) (hh : h ∈ Icc (0 : ℝ) 2) :
    (∑' n, fullLineTerm Z m γ n (y, h)) =
      (physicalEnvelope m γ y : ℂ) *
        (((1 + h : ℝ) : ℂ) * spectralKernel Z h y) := by
  have hn : Summable (fun n =>
      ‖Complex.exp ((Z.zero n - h) * y) * resolventCoefficient (Z.zero n) h‖) := by
    simpa only [norm_mul] using (zero_series_summable_and_bound Z h y hh).1
  have hs := hn.of_norm.hasSum.mul_left
    ((physicalEnvelope m γ y : ℂ) * ((1 + h : ℝ) : ℂ))
  simpa only [fullLineTerm, spectralKernel, mul_assoc] using hs.tsum_eq

private theorem fullLine_inner_eq_lowHIntegrand
    (Z : CompleteZeroFamily) (m γ y : ℝ) :
    (∫ h in Icc (0 : ℝ) 2, ∑' n, fullLineTerm Z m γ n (y, h)) =
      lowHIntegrand Z m γ y := by
  calc
    _ = ∫ h in Icc (0 : ℝ) 2,
        (physicalEnvelope m γ y : ℂ) *
          (((1 + h : ℝ) : ℂ) * spectralKernel Z h y) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with h hh
      exact fullLine_tsum_eq_product Z m γ y h hh
    _ = lowHIntegrand Z m γ y := by rw [integral_const_mul]; rfl

/-- Transport the compiled complete complex cubic Gaussian moment to the
    original physical envelope.  Its factor 3 is retained literally. -/
private theorem physicalEnvelope_gaussian_moment
    (m γ : ℝ) (hm : 0 < m) (z : ℂ) :
    (∫ y : ℝ, (physicalEnvelope m γ y : ℂ) * Complex.exp (z * (y : ℂ))) =
      (3 : ℂ) * (cubicPolynomial m γ z *
        Complex.exp (m * z ^ 2 + centre m * z)) := by
  have hscalar :
      (∫ y : ℝ,
        (((y + 1) * (((y - 16 * m) / (2 * m)) ^ 2 + γ ^ 2 + 1) *
          Real.exp (-(y - 16 * m) ^ 2 / (4 * m)) /
          Real.sqrt (4 * Real.pi * m) : ℝ) : ℂ) *
          Complex.exp (z * (y : ℂ))) =
        cubicPolynomial m γ z * Complex.exp (m * z ^ 2 + centre m * z) := by
    simpa [cubicPolynomial, centre] using
      (D5.S3.Arith.Robin.CompleteLowHGaussianMoment.cubic_gaussian_moment_explicit
        m γ hm z)
  calc
    _ = (3 : ℂ) * (∫ y : ℝ,
        (((y + 1) * (((y - 16 * m) / (2 * m)) ^ 2 + γ ^ 2 + 1) *
          Real.exp (-(y - 16 * m) ^ 2 / (4 * m)) /
          Real.sqrt (4 * Real.pi * m) : ℝ) : ℂ) *
          Complex.exp (z * (y : ℂ))) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact ae_of_all volume fun y => by
        dsimp [physicalEnvelope, gaussianCoordinate, gaussianDensity, centre]
        push_cast
        ring
    _ = _ := by rw [hscalar]

private theorem fullLine_term_moment
    (Z : CompleteZeroFamily) (m γ : ℝ) (hm : 0 < m) (n : ZeroIndex) (h : ℝ) :
    (∫ y : ℝ, fullLineTerm Z m γ n (y, h)) =
      (3 : ℂ) * ((1 + h : ℝ) : ℂ) * dividedCubicCoefficient m γ (Z.zero n) h := by
  calc
    _ = (((1 + h : ℝ) : ℂ) * resolventCoefficient (Z.zero n) h) *
        (∫ y : ℝ, (physicalEnvelope m γ y : ℂ) *
          Complex.exp ((Z.zero n - h) * y)) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact ae_of_all volume fun y => by dsimp [fullLineTerm]; ring
    _ = _ := by
      rw [physicalEnvelope_gaussian_moment m γ hm]
      dsimp [dividedCubicCoefficient]
      ring

/-- Full-y Bochner integrability and the actual complete spectral moment.
    No shell-term estimate or extra analytic certificate is assumed. -/
theorem complete_zero_fullLine_integrable_and_moment
    (Z : CompleteZeroFamily) (m γ : ℝ) (hm : 0 < m) :
    Integrable (lowHIntegrand Z m γ) ∧
      (∫ y : ℝ, lowHIntegrand Z m γ y) = completeRealLineMean Z m γ := by
  have ha := fullLine_absolute_exchange Z m γ hm
  have hi : Integrable (lowHIntegrand Z m γ) := by
    refine ha.2.1.integral_prod_left.congr ?_
    exact ae_of_all volume fun y => fullLine_inner_eq_lowHIntegrand Z m γ y
  refine ⟨hi, ?_⟩
  calc
    (∫ y : ℝ, lowHIntegrand Z m γ y) =
        ∫ y : ℝ, ∫ h in Icc (0 : ℝ) 2, ∑' n, fullLineTerm Z m γ n (y, h) := by
      apply integral_congr_ae
      exact ae_of_all volume fun y => (fullLine_inner_eq_lowHIntegrand Z m γ y).symm
    _ = ∫ p : ℝ × ℝ, (∑' n, fullLineTerm Z m γ n p)
        ∂(volume.prod (volume.restrict (Icc (0 : ℝ) 2))) :=
      (integral_prod _ ha.2.1).symm
    _ = ∑' n, ∫ p : ℝ × ℝ, fullLineTerm Z m γ n p
        ∂(volume.prod (volume.restrict (Icc (0 : ℝ) 2))) := ha.2.2
    _ = completeRealLineMean Z m γ := by
      unfold completeRealLineMean
      apply tsum_congr
      intro n
      rw [integral_prod_symm _ (ha.1 n)]
      change (∫ h in Icc (0 : ℝ) 2, ∫ y : ℝ, fullLineTerm Z m γ n (y, h)) = _
      apply integral_congr_ae
      exact ae_of_all (volume.restrict (Icc (0 : ℝ) 2)) fun h =>
        fullLine_term_moment Z m γ hm n h

/-- The exact original all-index identity, for m > 0 and every real γ.
    Ioi 1, Ioc 0 1, and Iio 0 omit only the null singleton {0}. -/
theorem complete_zero_fubini_exchange
    (Z : CompleteZeroFamily) (m γ : ℝ) (hm : 0 < m) :
    lowHMean Z m γ = completeRealLineMean Z m γ +
      positiveExtension Z m γ + negativeExtension Z m γ := by
  have hf := complete_zero_fullLine_integrable_and_moment Z m γ hm
  have hpartition :
      (∫ y in Ioi (1 : ℝ), lowHIntegrand Z m γ y) +
        (∫ y in Ioc (0 : ℝ) 1, lowHIntegrand Z m γ y) +
        (∫ y in Iio (0 : ℝ), lowHIntegrand Z m γ y) =
          ∫ y : ℝ, lowHIntegrand Z m γ y := by
    have hset : Iic (1 : ℝ) = Ioc (0 : ℝ) 1 ∪ Iic (0 : ℝ) := by
      ext y
      simp only [mem_Iic, mem_union, mem_Ioc]
      constructor
      · intro hy
        by_cases hp : 0 < y
        · exact Or.inl ⟨hp, hy⟩
        · exact Or.inr (le_of_not_gt hp)
      · rintro (⟨_, hy⟩ | hy) <;> linarith
    have hd : Disjoint (Ioc (0 : ℝ) 1) (Iic (0 : ℝ)) := by
      apply disjoint_left.mpr
      intro y hy hz
      exact (not_lt_of_ge hz) hy.1
    -- Actual full-line integrability is available before restriction/splitting.
    have hpos : IntegrableOn (lowHIntegrand Z m γ) (Ioc (0 : ℝ) 1) := hf.1.integrableOn
    have hnonpos : IntegrableOn (lowHIntegrand Z m γ) (Iic (0 : ℝ)) := hf.1.integrableOn
    have hfull := integral_add_compl (s := Ioi (1 : ℝ)) measurableSet_Ioi hf.1
    rw [compl_Ioi, hset, setIntegral_union hd measurableSet_Iic hpos hnonpos,
      integral_Iic_eq_integral_Iio] at hfull
    simpa only [add_assoc] using hfull
  calc
    lowHMean Z m γ = (∫ y : ℝ, lowHIntegrand Z m γ y) -
        (∫ y in Ioc (0 : ℝ) 1, lowHIntegrand Z m γ y) -
        (∫ y in Iio (0 : ℝ), lowHIntegrand Z m γ y) := by
      unfold lowHMean
      linear_combination hpartition
    _ = completeRealLineMean Z m γ + positiveExtension Z m γ +
        negativeExtension Z m γ := by
      rw [hf.2]
      simp only [positiveExtension, negativeExtension, sub_eq_add_neg]


private lemma resolvent_denominator_ne_zero_of_height
    (ρ : ℂ) (h : ℝ) (hρ : 10 < |ρ.im|) :
    ρ * (1 + h - ρ) ≠ 0 := by
  have hi : ρ.im ≠ 0 := by
    intro he
    simp only [he, abs_zero] at hρ
    linarith
  apply mul_ne_zero
  · intro he
    exact hi (by simpa using congrArg Complex.im he)
  · intro he
    have he' := congrArg Complex.im he
    simp at he'
    have : ρ.im = 0 := by linarith
    exact hi this

private lemma resolvent_norm_le_abs_im_sq_inv
    (ρ : ℂ) (h : ℝ) (hρ : 10 < |ρ.im|) :
    ‖resolventCoefficient ρ h‖ ≤ (|ρ.im| ^ 2)⁻¹ := by
  have ht : 0 < |ρ.im| := by linarith
  have hden := resolvent_denominator_ne_zero_of_height ρ h hρ
  have hp : 0 < ‖ρ‖ * ‖(1 + h - ρ : ℂ)‖ := by
    simpa only [norm_mul] using norm_pos_iff.mpr hden
  have h1 : |ρ.im| ≤ ‖ρ‖ := Complex.abs_im_le_norm _
  have h2 : |ρ.im| ≤ ‖(1 + h - ρ : ℂ)‖ := by
    simpa using Complex.abs_im_le_norm (1 + h - ρ : ℂ)
  have hprod : |ρ.im| ^ 2 ≤ ‖ρ‖ * ‖(1 + h - ρ : ℂ)‖ := by
    simpa only [pow_two] using mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)
  rw [resolventCoefficient, norm_inv, norm_mul]
  exact (inv_le_inv₀ hp (sq_pos_of_pos ht)).mpr hprod

/-- A genuine bound stronger than the paper's core 20.  First divide by the
    actual complex denominator.  With t=|Im ρ|>10, |Re ρ-h|≤2 gives
    ‖z‖≤2t, ‖16m+2mz+1‖≤6mt and ‖z²+γ²+1+1/(2m)‖≤4t²+D².
    The three numerator terms 24mt³, 6mD²t, 4t are each paid explicitly
    before cancelling t².  Neither sign of Im ρ is selected. -/
private theorem divided_cubic_polynomial_bound_two
    (m γ : ℝ) (ρ : ℂ) (h : ℝ)
    (hm : 1 ≤ m) (hγ : 10 < γ)
    (hstrip : 0 < ρ.re ∧ ρ.re < 1) (hheight : 10 < |ρ.im|)
    (hh : h ∈ Icc (0 : ℝ) 2) :
    ‖resolventCoefficient ρ h * cubicPolynomial m γ (ρ - h)‖ ≤
      2 * m * D γ ^ 2 * (|ρ.im| + 1) := by
  let t : ℝ := |ρ.im|
  let z : ℂ := ρ - h
  have ht : 10 < t := hheight
  have ht0 : 0 < t := by linarith
  have hm0 : 0 ≤ m := by linarith
  have hd24 : 24 ≤ D γ ^ 2 := by dsimp [D]; nlinarith
  have hdγ : γ ^ 2 + 2 ≤ D γ ^ 2 := by dsimp [D]; nlinarith
  have hmd : 1 ≤ m * D γ ^ 2 := by
    have := mul_le_mul_of_nonneg_right hm (sq_nonneg (D γ))
    nlinarith only [this, hd24]
  have hzre : |z.re| ≤ 2 := by
    apply abs_le.mpr
    dsimp [z]
    constructor <;> linarith [hstrip.1, hstrip.2, hh.1, hh.2]
  have hzim : |z.im| = t := by simp [z, t]
  have hz : ‖z‖ ≤ 2 * t := by
    have := Complex.norm_le_abs_re_add_abs_im z
    rw [hzim] at this
    linarith
  have hnm : ‖(m : ℂ)‖ = m := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hm0]
  have hnc : ‖(centre m : ℂ)‖ = 16 * m := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (show 0 ≤ centre m by dsimp [centre]; positivity)]
    rfl
  have hA : ‖(centre m : ℂ) + 2 * m * z + 1‖ ≤ 6 * m * t := by
    calc
      _ ≤ ‖(centre m : ℂ)‖ + ‖(2 : ℂ) * m * z‖ + ‖(1 : ℂ)‖ :=
        norm_add₃_le
      _ = 16 * m + 2 * m * ‖z‖ + 1 := by
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_one]
        rw [abs_of_nonneg hm0]
        dsimp [centre]
        rw [abs_of_nonneg (by positivity : 0 ≤ 16 * m)]
        norm_num
      _ ≤ 16 * m + 2 * m * (2 * t) + 1 := by gcongr
      _ ≤ 6 * m * t := by
        have hmt : 10 * m ≤ m * t :=
          (by simpa [mul_comm] using
            (mul_le_mul_of_nonneg_left (by linarith : (10 : ℝ) ≤ t) hm0))
        nlinarith only [hmt, hm]
  have hfrac : ‖(1 : ℂ) / (2 * m)‖ ≤ 1 := by
    have he : ‖(1 : ℂ) / (2 * m)‖ = 1 / (2 * m) := by
      rw [norm_div, norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hm0]
      norm_num
    rw [he]
    exact (div_le_one (by linarith : 0 < 2 * m)).mpr (by linarith)
  have hng : ‖(γ : ℂ) ^ 2‖ = γ ^ 2 := by
    simp [norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hB : ‖z ^ 2 + (γ : ℂ) ^ 2 + 1 + 1 / (2 * m)‖ ≤
      4 * t ^ 2 + D γ ^ 2 := by
    calc
      _ ≤ ‖z ^ 2 + (γ : ℂ) ^ 2 + 1‖ + ‖(1 : ℂ) / (2 * m)‖ :=
        norm_add_le _ _
      _ ≤ (‖z ^ 2‖ + ‖(γ : ℂ) ^ 2‖ + ‖(1 : ℂ)‖) +
          ‖(1 : ℂ) / (2 * m)‖ := by
        have htri : ‖z ^ 2 + (γ : ℂ) ^ 2 + 1‖ ≤
            ‖z ^ 2‖ + ‖(γ : ℂ) ^ 2‖ + ‖(1 : ℂ)‖ := by
          calc
            _ ≤ ‖z ^ 2 + (γ : ℂ) ^ 2‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
            _ ≤ (‖z ^ 2‖ + ‖(γ : ℂ) ^ 2‖) + ‖(1 : ℂ)‖ := by
              exact add_le_add (norm_add_le _ _) (le_refl _)
        exact add_le_add htri (le_refl _)
      _ ≤ (2 * t) ^ 2 + γ ^ 2 + 1 + 1 := by
        rw [norm_pow, hng, norm_one]
        exact add_le_add (by gcongr) hfrac
      _ ≤ 4 * t ^ 2 + D γ ^ 2 := by nlinarith only [hdγ]
  have hP : ‖cubicPolynomial m γ z‖ ≤
      (6 * m * t) * (4 * t ^ 2 + D γ ^ 2) + 4 * t := by
    unfold cubicPolynomial
    calc
      _ ≤ ‖((centre m : ℂ) + 2 * m * z + 1) *
            (z ^ 2 + (γ : ℂ) ^ 2 + 1 + 1 / (2 * m))‖ + ‖(2 : ℂ) * z‖ :=
        norm_add_le _ _
      _ = ‖(centre m : ℂ) + 2 * m * z + 1‖ *
          ‖z ^ 2 + (γ : ℂ) ^ 2 + 1 + 1 / (2 * m)‖ + 2 * ‖z‖ := by
        simp [norm_mul]
      _ ≤ (6 * m * t) * (4 * t ^ 2 + D γ ^ 2) + 4 * t := by
        exact add_le_add
          (mul_le_mul hA hB (norm_nonneg _) (by positivity))
          (by linarith)
  have hN1 : (6 * m * t) * (4 * t ^ 2) ≤
      (m * D γ ^ 2 * t) * t ^ 2 := by
    have := mul_le_mul_of_nonneg_left hd24
      (show 0 ≤ m * t * t ^ 2 by positivity)
    nlinarith only [this]
  have hN2 : (6 * m * t) * D γ ^ 2 ≤ (m * D γ ^ 2) * t ^ 2 := by
    have ht6 : 6 * t ≤ t ^ 2 := by
      nlinarith [mul_nonneg ht0.le (by linarith : 0 ≤ t - 6)]
    have := mul_le_mul_of_nonneg_left ht6
      (show 0 ≤ m * D γ ^ 2 by positivity)
    nlinarith only [this]
  have hN3 : 4 * t ≤ (m * D γ ^ 2) * t ^ 2 := by
    have ht4 : 4 * t ≤ t ^ 2 := by
      nlinarith [mul_nonneg ht0.le (by linarith : 0 ≤ t - 4)]
    exact ht4.trans (by
      nlinarith only [mul_le_mul_of_nonneg_right hmd (sq_nonneg t)])
  have hN : (6 * m * t) * (4 * t ^ 2 + D γ ^ 2) + 4 * t ≤
      (2 * m * D γ ^ 2 * (t + 1)) * t ^ 2 := by
    calc
      _ = (6 * m * t) * (4 * t ^ 2) + (6 * m * t) * D γ ^ 2 + 4 * t := by ring
      _ ≤ (m * D γ ^ 2 * t) * t ^ 2 +
          (m * D γ ^ 2) * t ^ 2 + (m * D γ ^ 2) * t ^ 2 :=
        add_le_add (add_le_add hN1 hN2) hN3
      _ = m * D γ ^ 2 * (t + 2) * t ^ 2 := by ring
      _ ≤ (2 * m * D γ ^ 2 * (t + 1)) * t ^ 2 := by
        have hp : 0 ≤ m * D γ ^ 2 * t * t ^ 2 := by positivity
        nlinarith only [hp]
  rw [norm_mul]
  change ‖resolventCoefficient ρ h‖ * ‖cubicPolynomial m γ z‖ ≤
    2 * m * D γ ^ 2 * (t + 1)
  calc
    _ ≤ (t ^ 2)⁻¹ * ‖cubicPolynomial m γ z‖ :=
      mul_le_mul_of_nonneg_right (resolvent_norm_le_abs_im_sq_inv ρ h hheight)
        (norm_nonneg _)
    _ ≤ (t ^ 2)⁻¹ * ((2 * m * D γ ^ 2 * (t + 1)) * t ^ 2) :=
      mul_le_mul_of_nonneg_left (hP.trans hN) (by positivity)
    _ = 2 * m * D γ ^ 2 * (t + 1) := by
      field_simp [ne_of_gt ht0] <;> ring

/-- Original-paper divided-polynomial core estimate, for arbitrary complex ρ
    in the full strip and both signed heights. -/
theorem divided_cubic_polynomial_bound
    (m γ : ℝ) (ρ : ℂ) (h : ℝ)
    (hm : 1 ≤ m) (hγ : 10 < γ)
    (hstrip : 0 < ρ.re ∧ ρ.re < 1) (hheight : 10 < |ρ.im|)
    (hh : h ∈ Icc (0 : ℝ) 2) :
    ‖resolventCoefficient ρ h * cubicPolynomial m γ (ρ - h)‖ ≤
      20 * m * D γ ^ 2 * (|ρ.im| + 1) := by
  have hm0 : 0 ≤ m := by linarith
  refine (divided_cubic_polynomial_bound_two m γ ρ h hm hγ hstrip hheight hh).trans ?_
  gcongr <;> norm_num

private lemma divided_cubic_exponential_bound
    (m : ℝ) (ρ : ℂ) (h : ℝ) (hm : 1 ≤ m)
    (hstrip : 0 < ρ.re ∧ ρ.re < 1) (hh : h ∈ Icc (0 : ℝ) 2) :
    ‖Complex.exp (m * (ρ - h) ^ 2 + centre m * (ρ - h))‖ ≤
      Real.exp (17 * m) * Real.exp (-m * ρ.im ^ 2) := by
  have hm0 : 0 ≤ m := by linarith
  have hxlo : -2 ≤ ρ.re - h := by linarith [hstrip.1, hh.2]
  have hxhi : ρ.re - h ≤ 1 := by linarith [hstrip.2, hh.1]
  have hquad : (ρ.re - h) ^ 2 + 16 * (ρ.re - h) ≤ 17 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - (ρ.re - h))
      (by linarith : 0 ≤ 17 + (ρ.re - h))]
  have heq : (m * (ρ - h) ^ 2 + centre m * (ρ - h) : ℂ).re =
      m * ((ρ.re - h) ^ 2 - ρ.im ^ 2) + 16 * m * (ρ.re - h) := by
    simp only [pow_two, Complex.add_re, Complex.mul_re, Complex.mul_im,
      Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
    dsimp [centre]
    ring
  rw [Complex.norm_exp, heq, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_left hquad hm0]

private theorem divided_cubic_coefficient_core_two
    (m γ : ℝ) (ρ : ℂ) (h : ℝ)
    (hm : 1 ≤ m) (hγ : 10 < γ)
    (hstrip : 0 < ρ.re ∧ ρ.re < 1) (hheight : 10 < |ρ.im|)
    (hh : h ∈ Icc (0 : ℝ) 2) :
    ‖dividedCubicCoefficient m γ ρ h‖ ≤
      2 * m * D γ ^ 2 * shellWeight m ρ * Real.exp (17 * m) := by
  rw [dividedCubicCoefficient, ← mul_assoc, norm_mul]
  calc
    _ ≤ (2 * m * D γ ^ 2 * (|ρ.im| + 1)) *
        (Real.exp (17 * m) * Real.exp (-m * ρ.im ^ 2)) :=
      mul_le_mul
        (divided_cubic_polynomial_bound_two m γ ρ h hm hγ hstrip hheight hh)
        (divided_cubic_exponential_bound m ρ h hm hstrip hh)
        (norm_nonneg _) (by positivity)
    _ = _ := by unfold shellWeight; ring

theorem divided_cubic_coefficient_core_bound
    (m γ : ℝ) (ρ : ℂ) (h : ℝ)
    (hm : 1 ≤ m) (hγ : 10 < γ)
    (hstrip : 0 < ρ.re ∧ ρ.re < 1) (hheight : 10 < |ρ.im|)
    (hh : h ∈ Icc (0 : ℝ) 2) :
    ‖dividedCubicCoefficient m γ ρ h‖ ≤
      20 * m * D γ ^ 2 * shellWeight m ρ * Real.exp (17 * m) := by
  rw [dividedCubicCoefficient, ← mul_assoc, norm_mul]
  calc
    _ ≤ (20 * m * D γ ^ 2 * (|ρ.im| + 1)) *
        (Real.exp (17 * m) * Real.exp (-m * ρ.im ^ 2)) :=
      mul_le_mul
        (divided_cubic_polynomial_bound m γ ρ h hm hγ hstrip hheight hh)
        (divided_cubic_exponential_bound m ρ h hm hstrip hh)
        (norm_nonneg _) (by positivity)
    _ = _ := by unfold shellWeight; ring

/-- The actual whole-prefactor pointwise bound supplies the finite majorant
    for Bochner integrability. -/
theorem divided_coefficient_bound
    (Z : CompleteZeroFamily) (m γ : ℝ) (hm : 1 ≤ m) (hγ : 10 < γ)
    (n : ZeroIndex) (h : ℝ) (hh : h ∈ Icc (0 : ℝ) 2) :
    ‖(3 : ℂ) * ((1 + h : ℝ) : ℂ) *
        dividedCubicCoefficient m γ (Z.zero n) h‖ ≤
      240 * m * D γ ^ 2 * shellWeight m (Z.zero n) * Real.exp (17 * m) := by
  have hw : ‖((1 + h : ℝ) : ℂ)‖ = 1 + h := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [hh.1])]
  have hm0 : 0 ≤ m := by linarith
  have hs0 : 0 ≤ shellWeight m (Z.zero n) := by unfold shellWeight; positivity
  calc
    _ = 3 * (1 + h) * ‖dividedCubicCoefficient m γ (Z.zero n) h‖ := by
      simp only [norm_mul, hw]
      norm_num
    _ ≤ 3 * (1 + h) *
        (20 * m * D γ ^ 2 * shellWeight m (Z.zero n) * Real.exp (17 * m)) :=
      mul_le_mul_of_nonneg_left
        (divided_cubic_coefficient_core_bound m γ (Z.zero n) h hm hγ
          (Z.strip n) (Z.height n) hh) (by linarith [hh.1])
    _ ≤ 240 * m * D γ ^ 2 * shellWeight m (Z.zero n) * Real.exp (17 * m) := by
      have hp : 0 ≤ m * D γ ^ 2 * shellWeight m (Z.zero n) * Real.exp (17 * m) :=
        by positivity
      have hh' : 3 * (1 + h) * 20 ≤ (240 : ℝ) := by linarith [hh.2]
      nlinarith [mul_le_mul_of_nonneg_right hh' hp]

private lemma divided_cubic_coefficient_continuous
    (m γ : ℝ) (ρ : ℂ) (hheight : 10 < |ρ.im|) :
    Continuous (dividedCubicCoefficient m γ ρ) := by
  have hd : Continuous (fun h : ℝ => ρ * (1 + h - ρ)) := by fun_prop
  have hr : Continuous (fun h : ℝ => resolventCoefficient ρ h) :=
    hd.inv₀ (fun h => resolvent_denominator_ne_zero_of_height ρ h hheight)
  have hp : Continuous (fun h : ℝ => cubicPolynomial m γ (ρ - h) *
      Complex.exp (m * (ρ - h) ^ 2 + centre m * (ρ - h))) := by
    unfold cubicPolynomial
    fun_prop
  exact hr.mul hp

theorem shell_term_integrable
    (Z : CompleteZeroFamily) (m γ : ℝ) (hm : 1 ≤ m) (hγ : 10 < γ)
    (n : ZeroIndex) :
    IntegrableOn (fun h => (3 : ℂ) * ((1 + h : ℝ) : ℂ) *
      dividedCubicCoefficient m γ (Z.zero n) h) (Icc (0 : ℝ) 2) := by
  have hc : Continuous (fun h : ℝ => (3 : ℂ) * ((1 + h : ℝ) : ℂ) *
      dividedCubicCoefficient m γ (Z.zero n) h) := by
    exact (by fun_prop : Continuous (fun h : ℝ => (3 : ℂ) * ((1 + h : ℝ) : ℂ))).mul
      (divided_cubic_coefficient_continuous m γ (Z.zero n) (Z.height n))
  have hi : IntegrableOn (fun _h : ℝ =>
      240 * m * D γ ^ 2 * shellWeight m (Z.zero n) * Real.exp (17 * m))
      (Icc (0 : ℝ) 2) := continuous_const.integrableOn_Icc
  refine Integrable.mono' hi hc.aestronglyMeasurable ?_
  exact (ae_restrict_mem measurableSet_Icc).mono fun h hh =>
    divided_coefficient_bound Z m γ hm hγ n h hh

private lemma h_weight_integral :
    (∫ h in Icc (0 : ℝ) 2, (1 + h)) = 4 := by
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    (∫ h in (0 : ℝ)..2, (1 + h)) =
        (∫ _h in (0 : ℝ)..2, (1 : ℝ)) + (∫ h in (0 : ℝ)..2, h) :=
      intervalIntegral.integral_add
        (continuous_const.intervalIntegrable 0 2)
        (continuous_id.intervalIntegrable 0 2)
    _ = 4 := by norm_num [intervalIntegral.integral_const, integral_id]

/- This internal integration lemma has actual pointwise evidence as a proof
   argument at each call below.  No coefficient premise is exposed in the
   final certificate.  In particular it integrates 3*(1+h), whose integral
   is 12; it does not integrate a whole-prefactor 240 into a spurious 24. -/
private lemma shell_term_bound_of_core
    (Z : CompleteZeroFamily) (m γ : ℝ) (hm : 1 ≤ m) (hγ : 10 < γ)
    (n : ZeroIndex) (c : ℝ)
    (hcore : ∀ h, h ∈ Icc (0 : ℝ) 2 →
      ‖dividedCubicCoefficient m γ (Z.zero n) h‖ ≤
        c * shellWeight m (Z.zero n) * Real.exp (17 * m)) :
    ‖shellTerm Z m γ n‖ ≤
      12 * c * shellWeight m (Z.zero n) * Real.exp (17 * m) := by
  let B : ℝ := c * shellWeight m (Z.zero n) * Real.exp (17 * m)
  have hi := shell_term_integrable Z m γ hm hγ n
  have hg : IntegrableOn (fun h : ℝ => 3 * (1 + h) * B) (Icc (0 : ℝ) 2) := by
    exact (by fun_prop : Continuous (fun h : ℝ => 3 * (1 + h) * B)).integrableOn_Icc
  have hnorm : ∀ᵐ h ∂volume.restrict (Icc (0 : ℝ) 2),
      ‖(3 : ℂ) * ((1 + h : ℝ) : ℂ) *
        dividedCubicCoefficient m γ (Z.zero n) h‖ ≤ 3 * (1 + h) * B := by
    exact (ae_restrict_mem measurableSet_Icc).mono fun h hh => by
      have hw : ‖((1 + h : ℝ) : ℂ)‖ = 1 + h := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [hh.1])]
      have he : ‖(3 : ℂ) * ((1 + h : ℝ) : ℂ) *
          dividedCubicCoefficient m γ (Z.zero n) h‖ =
          3 * (1 + h) * ‖dividedCubicCoefficient m γ (Z.zero n) h‖ := by
        simp only [norm_mul, hw]
        norm_num
      rw [he]
      exact mul_le_mul_of_nonneg_left (hcore h hh) (by linarith [hh.1])
  calc
    ‖shellTerm Z m γ n‖ ≤ ∫ h in Icc (0 : ℝ) 2,
        ‖(3 : ℂ) * ((1 + h : ℝ) : ℂ) *
          dividedCubicCoefficient m γ (Z.zero n) h‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ h in Icc (0 : ℝ) 2, 3 * (1 + h) * B := integral_mono_ae hi.norm hg hnorm
    _ = (3 * B) * (∫ h in Icc (0 : ℝ) 2, (1 + h)) := by
      calc
        _ = ∫ h in Icc (0 : ℝ) 2, (3 * B) * (1 + h) := by
          apply integral_congr_ae
          exact ae_of_all _ fun h => by ring
        _ = _ := by rw [integral_const_mul]
    _ = 12 * c * shellWeight m (Z.zero n) * Real.exp (17 * m) := by
      rw [h_weight_integral]
      dsimp [B]
      ring

/-- The paper's actual integrated coefficient, 3*4*20=240. -/
theorem shell_term_bound240
    (Z : CompleteZeroFamily) (m γ : ℝ) (hm : 1 ≤ m) (hγ : 10 < γ)
    (n : ZeroIndex) :
    ‖shellTerm Z m γ n‖ ≤
      240 * m * D γ ^ 2 * shellWeight m (Z.zero n) * Real.exp (17 * m) := by
  have hb := shell_term_bound_of_core Z m γ hm hγ n (20 * m * D γ ^ 2)
    (fun h hh => divided_cubic_coefficient_core_bound m γ (Z.zero n) h hm hγ
      (Z.strip n) (Z.height n) hh)
  convert hb using 1 <;> ring

/-- The stronger integrated bound uses the divided-polynomial core 2 and
    the exact weight integral, giving 3*4*2=24. -/
theorem shell_term_bound24
    (Z : CompleteZeroFamily) (m γ : ℝ) (hm : 1 ≤ m) (hγ : 10 < γ)
    (n : ZeroIndex) :
    ‖shellTerm Z m γ n‖ ≤
      24 * m * D γ ^ 2 * shellWeight m (Z.zero n) * Real.exp (17 * m) := by
  have hb := shell_term_bound_of_core Z m γ hm hγ n (2 * m * D γ ^ 2)
    (fun h hh => divided_cubic_coefficient_core_two m γ (Z.zero n) h hm hγ
      (Z.strip n) (Z.height n) hh)
  convert hb using 1 <;> ring

/-- Comparison of the actual full complex shell norms with the already
    proved all-index shell series.  No convergence field or finite-family
    restriction is assumed, and no default value of tsum is invoked. -/
theorem shell_terms_norm_summable
    (Z : CompleteZeroFamily) (m γ : ℝ) (hm : 1 ≤ m) (hγ : 10 < γ) :
    Summable (fun n => ‖shellTerm Z m γ n‖) := by
  let c : ℝ := 24 * m * D γ ^ 2 * Real.exp (17 * m)
  have hs := (shell_summable_and_count_bound Z m hm).1.mul_left c
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) ?_ hs
  intro n
  simpa [c, mul_assoc, mul_left_comm, mul_comm] using shell_term_bound24 Z m γ hm hγ n

/-- Actual full-complex series consumer of the integrated paper bound. -/
theorem complete_real_line_mean_bound240
    (Z : CompleteZeroFamily) (m γ : ℝ) (hm : 1 ≤ m) (hγ : 10 < γ) :
    ‖completeRealLineMean Z m γ‖ ≤
      240 * m * D γ ^ 2 * shellSum Z m * Real.exp (17 * m) := by
  let c : ℝ := 240 * m * D γ ^ 2 * Real.exp (17 * m)
  have hs := (shell_summable_and_count_bound Z m hm).1
  have hc : HasSum (fun n => c * shellWeight m (Z.zero n))
      (c * shellSum Z m) := by
    simpa [shellSum] using hs.hasSum.mul_left c
  have hb : ∀ n, ‖shellTerm Z m γ n‖ ≤ c * shellWeight m (Z.zero n) := by
    intro n
    simpa [c, mul_assoc, mul_left_comm, mul_comm] using shell_term_bound240 Z m γ hm hγ n
  have hnorm := shell_terms_norm_summable Z m γ hm hγ
  simpa [completeRealLineMean, c, mul_assoc, mul_left_comm, mul_comm] using
    hnorm.of_norm.hasSum.norm_le_of_bounded hc hb


/-! The two original extension estimates.  These helpers keep the full zero
family and use the existing scalar Gaussian moment theorem; no moment formula
is re-ported here.  All new helpers below feed the two original extensions. -/

/-- Absolute convergence is paid by the existing all-real norm series.
The sharper exponential estimate is proved separately on each actual domain. -/
private theorem extension_kernel_norm_le
    (Z : CompleteZeroFamily) (h y c : ℝ) (hh : h ∈ Icc (0 : ℝ) 2)
    (hc : 0 ≤ c)
    (he : ∀ n, ‖Complex.exp ((Z.zero n - h) * y)‖ ≤ c) :
    ‖spectralKernel Z h y‖ ≤ c * (∑' n, ((Z.zero n).im)⁻¹ ^ 2) := by
  have hs := (zero_series_summable_and_bound Z h y hh).1
  have hn : Summable (fun n =>
      ‖Complex.exp ((Z.zero n - h) * y) * resolventCoefficient (Z.zero n) h‖) := by
    simpa only [norm_mul] using hs
  calc
    ‖spectralKernel Z h y‖ ≤
        ∑' n, ‖Complex.exp ((Z.zero n - h) * y)‖ *
          ‖resolventCoefficient (Z.zero n) h‖ := by
      simpa only [spectralKernel, norm_mul] using norm_tsum_le_tsum_norm hn
    _ ≤ ∑' n, c * ((Z.zero n).im)⁻¹ ^ 2 :=
      hs.tsum_le_tsum (fun n => mul_le_mul (he n)
        (resolvent_norm_le_reciprocal_square Z n h hh) (norm_nonneg _) hc)
        (Z.reciprocalSquare.mul_left c)
    _ = c * (∑' n, ((Z.zero n).im)⁻¹ ^ 2) := by rw [tsum_mul_left]

/-- Genuine fixed-y Bochner integrability on the complete h-window, followed
by the norm estimate with its exact weight integral 4 and complete R < 2. -/
private theorem extension_inner_integrable_and_bound
    (Z : CompleteZeroFamily) (y c : ℝ) (hc : 0 ≤ c)
    (he : ∀ n h, h ∈ Icc (0 : ℝ) 2 →
      ‖Complex.exp ((Z.zero n - h) * y)‖ ≤ c) :
    IntegrableOn (fun h : ℝ => ((1 + h : ℝ) : ℂ) * spectralKernel Z h y)
      (Icc (0 : ℝ) 2) ∧
    ‖∫ h in Icc (0 : ℝ) 2, ((1 + h : ℝ) : ℂ) * spectralKernel Z h y‖ ≤ 8 * c := by
  let R : ℝ := ∑' n, ((Z.zero n).im)⁻¹ ^ 2
  have hR2 : R ≤ 2 := Z.reciprocalSquare_lt_two.le
  have hmeas : Measurable (fun h : ℝ =>
      ((1 + h : ℝ) : ℂ) * spectralKernel Z h y) := by
    have hk : Measurable (fun h : ℝ => spectralKernel Z h y) := by
      unfold spectralKernel
      apply Measurable.tsum
      intro n
      unfold resolventCoefficient
      fun_prop
    exact (by fun_prop : Measurable (fun h : ℝ => ((1 + h : ℝ) : ℂ))).mul hk
  have hmajor : IntegrableOn (fun h : ℝ => (1 + h) * (c * R))
      (Icc (0 : ℝ) 2) :=
    ((continuous_const.add continuous_id).mul continuous_const).integrableOn_Icc
  have hbound : ∀ᵐ h ∂(volume.restrict (Icc (0 : ℝ) 2)),
      ‖((1 + h : ℝ) : ℂ) * spectralKernel Z h y‖ ≤ (1 + h) * (c * R) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with h hh
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (show 0 ≤ 1 + h by linarith [hh.1])]
    exact mul_le_mul_of_nonneg_left
      (extension_kernel_norm_le Z h y c hh hc (fun n => he n h hh))
      (by linarith [hh.1])
  have hint : IntegrableOn (fun h : ℝ =>
      ((1 + h : ℝ) : ℂ) * spectralKernel Z h y) (Icc (0 : ℝ) 2) :=
    hmajor.mono' hmeas.aestronglyMeasurable hbound
  refine ⟨hint, ?_⟩
  calc
    ‖∫ h in Icc (0 : ℝ) 2, ((1 + h : ℝ) : ℂ) * spectralKernel Z h y‖ ≤
        ∫ h in Icc (0 : ℝ) 2,
          ‖((1 + h : ℝ) : ℂ) * spectralKernel Z h y‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ h in Icc (0 : ℝ) 2, (1 + h) * (c * R) :=
      integral_mono_ae hint.norm hmajor hbound
    _ = 4 * (c * R) := by rw [integral_mul_const, h_weight_integral]
    _ ≤ 8 * c := by nlinarith [mul_le_mul_of_nonneg_left hR2 hc]

private theorem extension_positive_exp_le
    (Z : CompleteZeroFamily) (n : ZeroIndex) (h y : ℝ)
    (hh : h ∈ Icc (0 : ℝ) 2) (hy : y ∈ Ioc (0 : ℝ) 1) :
    ‖Complex.exp ((Z.zero n - h) * y)‖ ≤ 3 := by
  rw [Complex.norm_exp]
  have heq : ((Z.zero n - h) * y : ℂ).re = ((Z.zero n).re - h) * y := by
    simp [Complex.mul_re]
  rw [heq]
  have hcoef : (Z.zero n).re - h ≤ 1 := by linarith [Z.strip n |>.2, hh.1]
  calc
    Real.exp (((Z.zero n).re - h) * y) ≤ Real.exp y :=
      Real.exp_le_exp.mpr (by
        simpa using mul_le_mul_of_nonneg_right hcoef hy.1.le)
    _ ≤ Real.exp 1 := Real.exp_le_exp.mpr hy.2
    _ ≤ 3 := Real.exp_one_lt_three.le

private theorem extension_negative_exp_le
    (Z : CompleteZeroFamily) (n : ZeroIndex) (h y : ℝ)
    (hh : h ∈ Icc (0 : ℝ) 2) (hy : y ≤ 0) :
    ‖Complex.exp ((Z.zero n - h) * y)‖ ≤ Real.exp (-2 * y) := by
  rw [Complex.norm_exp]
  have heq : ((Z.zero n - h) * y : ℂ).re = ((Z.zero n).re - h) * y := by
    simp [Complex.mul_re]
  rw [heq]
  have hcoef : -2 ≤ (Z.zero n).re - h := by linarith [Z.strip n |>.1, hh.2]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right hcoef hy)

private theorem extension_density_nonneg (m y : ℝ) (hm : 0 < m) :
    0 ≤ gaussianDensity m y := by
  unfold gaussianDensity
  positivity

private theorem extension_physical_norm (m γ y : ℝ) (hm : 0 < m) :
    ‖(physicalEnvelope m γ y : ℂ)‖ =
      3 * |y + 1| * (gaussianCoordinate m y ^ 2 + γ ^ 2 + 1) *
        gaussianDensity m y := by
  rw [Complex.norm_real, Real.norm_eq_abs, physicalEnvelope,
    abs_mul, abs_mul, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3),
    abs_of_nonneg (show 0 ≤ gaussianCoordinate m y ^ 2 + γ ^ 2 + 1 by positivity),
    abs_of_nonneg (extension_density_nonneg m y hm)]

private theorem extension_positive_physical_le
    (m γ y : ℝ) (hm : 1 ≤ m) (hγ : 10 < γ) (hy : y ∈ Ioc (0 : ℝ) 1) :
    ‖(physicalEnvelope m γ y : ℂ)‖ ≤ 6 * D γ ^ 2 := by
  have hmpos : 0 < m := by linarith
  have hqlo : -8 ≤ gaussianCoordinate m y := by
    unfold gaussianCoordinate centre
    apply (le_div_iff₀ (show 0 < 2 * m by positivity)).2
    linarith [hy.1]
  have hqhi : gaussianCoordinate m y ≤ 0 := by
    unfold gaussianCoordinate centre
    exact div_nonpos_of_nonpos_of_nonneg (by linarith [hy.2]) (by positivity)
  have hq : gaussianCoordinate m y ^ 2 ≤ 64 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hqlo) (neg_nonneg.mpr hqhi)]
  have hpoly : gaussianCoordinate m y ^ 2 + γ ^ 2 + 1 ≤ D γ ^ 2 := by
    unfold D
    nlinarith
  have hs : 0 < Real.sqrt (4 * Real.pi * m) := by positivity
  have hs1 : 1 ≤ Real.sqrt (4 * Real.pi * m) := by
    have hp := Real.two_le_pi
    have hmπ : Real.pi ≤ Real.pi * m := by nlinarith [Real.pi_pos]
    have hsq := Real.sq_sqrt (show 0 ≤ 4 * Real.pi * m by positivity)
    nlinarith [Real.sqrt_nonneg (4 * Real.pi * m)]
  have he : Real.exp (-(y - centre m) ^ 2 / (4 * m)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity)
  have hd : gaussianDensity m y ≤ 1 := by
    unfold gaussianDensity
    apply (div_le_iff₀ hs).2
    simpa only [one_mul] using he.trans hs1
  rw [extension_physical_norm m γ y hmpos,
    abs_of_nonneg (show 0 ≤ y + 1 by linarith [hy.1])]
  calc
    3 * (y + 1) * (gaussianCoordinate m y ^ 2 + γ ^ 2 + 1) * gaussianDensity m y ≤
        (6 * D γ ^ 2) * 1 := by
      apply mul_le_mul _ hd (extension_density_nonneg m y hmpos) (by positivity)
      exact mul_le_mul (by linarith [hy.2]) hpoly (by positivity) (by norm_num)
    _ = 6 * D γ ^ 2 := mul_one _

theorem complete_zero_positive_extension_bound
    (Z : CompleteZeroFamily) (m γ : ℝ) (hm : 1 ≤ m) (hγ : 10 < γ) :
    ‖positiveExtension Z m γ‖ ≤ 2400 * m * D γ ^ 2 := by
  have hmpos : 0 < m := by linarith
  have hf : IntegrableOn (lowHIntegrand Z m γ) (Ioc (0 : ℝ) 1) :=
    (complete_zero_fullLine_integrable_and_moment Z m γ hmpos).1.integrableOn
  have hbound : ∀ᵐ y ∂(volume.restrict (Ioc (0 : ℝ) 1)),
      ‖lowHIntegrand Z m γ y‖ ≤ 144 * D γ ^ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    have hi := (extension_inner_integrable_and_bound Z y 3 (by norm_num)
      (fun n h hh => extension_positive_exp_le Z n h y hh hy)).2
    rw [lowHIntegrand, norm_mul]
    calc
      _ ≤ (6 * D γ ^ 2) * (8 * 3) :=
        mul_le_mul (extension_positive_physical_le m γ y hm hγ hy) hi
          (norm_nonneg _) (by positivity)
      _ = 144 * D γ ^ 2 := by ring
  calc
    ‖positiveExtension Z m γ‖ =
        ‖∫ y in Ioc (0 : ℝ) 1, lowHIntegrand Z m γ y‖ := by
      rw [positiveExtension, norm_neg]
    _ ≤ ∫ y in Ioc (0 : ℝ) 1, ‖lowHIntegrand Z m γ y‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ _y in Ioc (0 : ℝ) 1, 144 * D γ ^ 2 :=
      integral_mono_ae hf.norm (integrable_const _) hbound
    _ = 144 * D γ ^ 2 := by simp
    _ ≤ 2400 * m * D γ ^ 2 := by
      exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)

/-- Density transport of actual finite moments.  This follows the same
withDensity API as checked4328, now in ℝ. -/
private theorem extension_central_density_integrable
    (μ : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (n : ℕ) :
    Integrable (fun y : ℝ => ProbabilityTheory.gaussianPDFReal μ v y * (y - μ) ^ n) := by
  have hLp : MemLp (fun y : ℝ => y - μ) n (ProbabilityTheory.gaussianReal μ v) := by
    simpa only [Pi.sub_def, id_eq, ENNReal.coe_natCast] using
      (ProbabilityTheory.memLp_id_gaussianReal (μ := μ) (v := v) (n : ℝ≥0)).sub
        (memLp_const μ)
  have hpow : Integrable (fun y : ℝ => (y - μ) ^ n)
      (ProbabilityTheory.gaussianReal μ v) := by
    apply hLp.integrable_norm_pow'.mono' (hLp.aestronglyMeasurable.pow n)
    exact ae_of_all _ fun y => (norm_pow (y - μ) n).le
  rw [ProbabilityTheory.gaussianReal_of_var_ne_zero _ hv] at hpow
  have htransport := (integrable_withDensity_iff_integrable_smul'
    (ProbabilityTheory.measurable_gaussianPDF μ v)
    (ae_of_all volume fun _ => ProbabilityTheory.gaussianPDF_lt_top)).mp hpow
  simpa only [ProbabilityTheory.toReal_gaussianPDF, smul_eq_mul] using htransport

/-- The project supplier already contains the scalar even-moment proof and
its RemyDegenne/brownian-motion attribution.  Only n=1 and n=2 are used here. -/
private theorem extension_central_density_moments
    (μ : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    (∫ y : ℝ, ProbabilityTheory.gaussianPDFReal μ v y * (y - μ) ^ 2) = (v : ℝ) ∧
    (∫ y : ℝ, ProbabilityTheory.gaussianPDFReal μ v y * (y - μ) ^ 4) = 3 * (v : ℝ) ^ 2 := by
  have hs : (NNReal.sqrt v : ℝ) ^ 2 = (v : ℝ) := by
    exact_mod_cast NNReal.sq_sqrt v
  have hs4 : (NNReal.sqrt v : ℝ) ^ 4 = (v : ℝ) ^ 2 := by
    calc
      _ = ((NNReal.sqrt v : ℝ) ^ 2) ^ 2 := by ring
      _ = (v : ℝ) ^ 2 := by rw [hs]
  have h2 := D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticFourthMoment.centralMoment_two_mul
    μ (NNReal.sqrt v) 1
  have h4 := D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticFourthMoment.centralMoment_two_mul
    μ (NNReal.sqrt v) 2
  have h2' : (∫ y : ℝ, (y - μ) ^ 2 ∂ProbabilityTheory.gaussianReal μ v) = (v : ℝ) := by
    simpa only [ProbabilityTheory.centralMoment, id_eq,
      ProbabilityTheory.integral_id_gaussianReal, Pi.pow_apply, Pi.sub_apply,
      show (2 * 1 : ℕ) = 2 by rfl, show (2 * 1 - 1 : ℕ) = 1 by rfl,
      NNReal.sq_sqrt, show Nat.doubleFactorial 1 = 1 by decide,
      Nat.cast_one, mul_one, hs] using h2
  have h4' : (∫ y : ℝ, (y - μ) ^ 4 ∂ProbabilityTheory.gaussianReal μ v) =
      3 * (v : ℝ) ^ 2 := by
    simpa only [ProbabilityTheory.centralMoment, id_eq,
      ProbabilityTheory.integral_id_gaussianReal, Pi.pow_apply, Pi.sub_apply,
      show (2 * 2 : ℕ) = 4 by rfl, show (2 * 2 - 1 : ℕ) = 3 by rfl,
      NNReal.sq_sqrt, show Nat.doubleFactorial 3 = 3 by decide,
      Nat.cast_ofNat, hs4, mul_comm] using h4
  constructor
  · rw [ProbabilityTheory.integral_gaussianReal_eq_integral_smul hv] at h2'
    simpa only [smul_eq_mul] using h2'
  · rw [ProbabilityTheory.integral_gaussianReal_eq_integral_smul hv] at h4'
    simpa only [smul_eq_mul] using h4'

private theorem extension_negative_tilt (m y : ℝ) (hm : 0 < m) :
    gaussianDensity m y * Real.exp (-2 * y) =
      Real.exp (-28 * m) * ProbabilityTheory.gaussianPDFReal (12 * m)
        (D5.S3.Arith.Robin.CompleteLowHGaussianMoment.variance m hm) y := by
  have he : -(y - 16 * m) ^ 2 / (4 * m) + -2 * y =
      -28 * m + -(y - 12 * m) ^ 2 / (4 * m) := by
    field_simp [hm.ne'] <;> ring
  change (Real.exp (-(y - 16 * m) ^ 2 / (4 * m)) /
      Real.sqrt (4 * Real.pi * m)) * Real.exp (-2 * y) =
    Real.exp (-28 * m) * ((Real.sqrt (2 * Real.pi * (2 * m)))⁻¹ *
      Real.exp (-(y - 12 * m) ^ 2 / (2 * (2 * m))))
  rw [show 2 * Real.pi * (2 * m) = 4 * Real.pi * m by ring,
    show 2 * (2 * m) = 4 * m by ring]
  calc
    _ = Real.exp (-(y - 16 * m) ^ 2 / (4 * m) + -2 * y) /
        Real.sqrt (4 * Real.pi * m) := by rw [Real.exp_add]; ring
    _ = _ := by rw [he, Real.exp_add]; ring

private theorem extension_negative_polynomial_le
    (m γ y : ℝ) (hm : 1 ≤ m) :
    |y + 1| * (gaussianCoordinate m y ^ 2 + γ ^ 2 + 1) ≤
      (13 * m + 1 + (y - 12 * m) ^ 2 / (4 * m)) *
        ((y - 12 * m) ^ 2 / (2 * m ^ 2) + γ ^ 2 + 9) := by
  have hmpos : 0 < m := by linarith
  have habs : |y - 12 * m| ≤ m + (y - 12 * m) ^ 2 / (4 * m) := by
    have hh : |y - 12 * m| - m ≤ (y - 12 * m) ^ 2 / (4 * m) := by
      apply (le_div_iff₀ (show 0 < 4 * m by positivity)).2
      nlinarith [sq_nonneg (|y - 12 * m| - 2 * m), sq_abs (y - 12 * m)]
    linarith
  have hfirst : |y + 1| ≤ 13 * m + 1 + (y - 12 * m) ^ 2 / (4 * m) := by
    calc
      |y + 1| = |(y - 12 * m) + (12 * m + 1)| := by congr 1 <;> ring
      _ ≤ |y - 12 * m| + |12 * m + 1| := abs_add_le _ _
      _ = |y - 12 * m| + (12 * m + 1) := by
        rw [abs_of_nonneg (by positivity : 0 ≤ 12 * m + 1)]
      _ ≤ _ := by linarith
  have hcoord : gaussianCoordinate m y = (y - 12 * m) / (2 * m) - 2 := by
    unfold gaussianCoordinate centre
    field_simp [hmpos.ne'] <;> ring
  have hsecond : gaussianCoordinate m y ^ 2 + γ ^ 2 + 1 ≤
      (y - 12 * m) ^ 2 / (2 * m ^ 2) + γ ^ 2 + 9 := by
    have hsq : ((y - 12 * m) / (2 * m) - 2) ^ 2 ≤
        2 * ((y - 12 * m) / (2 * m)) ^ 2 + 8 := by
      nlinarith [sq_nonneg ((y - 12 * m) / (2 * m) + 2)]
    have heq : 2 * ((y - 12 * m) / (2 * m)) ^ 2 =
        (y - 12 * m) ^ 2 / (2 * m ^ 2) := by
      field_simp [hmpos.ne'] <;> ring
    rw [hcoord]
    rw [heq] at hsq
    linarith
  exact mul_le_mul hfirst hsecond (by positivity) (by positivity)

/-- Genuine density integrability and evaluation of the polynomial majorant.
The variance is 2m, so the existing moments give 2m and 12m². -/
private theorem extension_negative_majorant_integral
    (m γ : ℝ) (hm : 1 ≤ m) (hγ : 10 < γ) :
    let hmpos : 0 < m := by linarith
    let v := D5.S3.Arith.Robin.CompleteLowHGaussianMoment.variance m hmpos
    let F := fun y : ℝ => ProbabilityTheory.gaussianPDFReal (12 * m) v y *
      ((13 * m + 1 + (y - 12 * m) ^ 2 / (4 * m)) *
        ((y - 12 * m) ^ 2 / (2 * m ^ 2) + γ ^ 2 + 9))
    Integrable F ∧ (∫ y : ℝ, F y) ≤ 16 * m * D γ ^ 2 := by
  dsimp only
  let hmpos : 0 < m := by linarith
  let v := D5.S3.Arith.Robin.CompleteLowHGaussianMoment.variance m hmpos
  have hv : v ≠ 0 := D5.S3.Arith.Robin.CompleteLowHGaussianMoment.variance_ne_zero m hmpos
  have hvcoe : (v : ℝ) = 2 * m := rfl
  let A : ℝ := 13 * m + 1
  let B : ℝ := γ ^ 2 + 9
  let C : ℝ := A / (2 * m ^ 2) + B / (4 * m)
  let E : ℝ := 1 / (8 * m ^ 3)
  have hi0 := ProbabilityTheory.integrable_gaussianPDFReal (12 * m) v
  have hi2 := extension_central_density_integrable (12 * m) v hv 2
  have hi4 := extension_central_density_integrable (12 * m) v hv 4
  have hmom := extension_central_density_moments (12 * m) v hv
  have hfun : (fun y : ℝ => ProbabilityTheory.gaussianPDFReal (12 * m) v y *
      ((13 * m + 1 + (y - 12 * m) ^ 2 / (4 * m)) *
        ((y - 12 * m) ^ 2 / (2 * m ^ 2) + γ ^ 2 + 9))) =
      (fun y : ℝ => (A * B) * ProbabilityTheory.gaussianPDFReal (12 * m) v y +
        C * (ProbabilityTheory.gaussianPDFReal (12 * m) v y * (y - 12 * m) ^ 2) +
        E * (ProbabilityTheory.gaussianPDFReal (12 * m) v y * (y - 12 * m) ^ 4)) := by
    funext y
    dsimp [A, B, C, E]
    field_simp [hmpos.ne'] <;> ring
  have hi := ((hi0.const_mul (A * B)).add (hi2.const_mul C)).add (hi4.const_mul E)
  refine ⟨?_, ?_⟩
  · change Integrable (fun y : ℝ => ProbabilityTheory.gaussianPDFReal (12 * m) v y *
      ((13 * m + 1 + (y - 12 * m) ^ 2 / (4 * m)) *
        ((y - 12 * m) ^ 2 / (2 * m ^ 2) + γ ^ 2 + 9)))
    rw [hfun]
    exact hi
  have heval : (∫ y : ℝ, ProbabilityTheory.gaussianPDFReal (12 * m) v y *
      ((13 * m + 1 + (y - 12 * m) ^ 2 / (4 * m)) *
        ((y - 12 * m) ^ 2 / (2 * m ^ 2) + γ ^ 2 + 9))) =
      (13 * m + 3 / 2) * (γ ^ 2 + 9) + 13 + 5 / (2 * m) := by
    have hsplit := integral_add ((hi0.const_mul (A * B)).add (hi2.const_mul C))
      (hi4.const_mul E)
    have hsplit2 := integral_add (hi0.const_mul (A * B)) (hi2.const_mul C)
    simp only [Pi.add_apply] at hsplit hsplit2
    rw [hfun, hsplit, hsplit2]
    simp only [integral_const_mul, ProbabilityTheory.integral_gaussianPDFReal_eq_one _ hv,
      hmom.1, hmom.2, hvcoe]
    dsimp [A, B, C, E]
    field_simp [hmpos.ne'] <;> ring
  rw [heval]
  have hfrac : 5 / (2 * m) ≤ (5 / 2 : ℝ) := by
    apply (div_le_iff₀ (show 0 < 2 * m by positivity)).2
    linarith
  have hfirst : (13 * m + 3 / 2) * (γ ^ 2 + 9) ≤
      ((29 / 2 : ℝ) * m) * (γ ^ 2 + 9) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hscalar : (29 / 2 : ℝ) * γ ^ 2 + 146 ≤ 16 * D γ ^ 2 := by
    unfold D
    nlinarith [sq_nonneg γ]
  calc
    (13 * m + 3 / 2) * (γ ^ 2 + 9) + 13 + 5 / (2 * m) ≤
        ((29 / 2 : ℝ) * m) * (γ ^ 2 + 9) + (31 / 2 : ℝ) * m := by
      linarith
    _ = m * ((29 / 2 : ℝ) * γ ^ 2 + 146) := by ring
    _ ≤ m * (16 * D γ ^ 2) := mul_le_mul_of_nonneg_left hscalar hmpos.le
    _ = 16 * m * D γ ^ 2 := by ring

private theorem extension_negative_pointwise
    (Z : CompleteZeroFamily) (m γ y : ℝ) (hm : 1 ≤ m) (hy : y < 0) :
    let hmpos : 0 < m := by linarith
    ‖lowHIntegrand Z m γ y‖ ≤
      (24 * Real.exp (-28 * m)) *
        (ProbabilityTheory.gaussianPDFReal (12 * m)
          (D5.S3.Arith.Robin.CompleteLowHGaussianMoment.variance m hmpos) y *
          ((13 * m + 1 + (y - 12 * m) ^ 2 / (4 * m)) *
            ((y - 12 * m) ^ 2 / (2 * m ^ 2) + γ ^ 2 + 9))) := by
  dsimp only
  have hmpos : 0 < m := by linarith
  have hi := (extension_inner_integrable_and_bound Z y (Real.exp (-2 * y))
    (Real.exp_nonneg _) (fun n h hh => extension_negative_exp_le Z n h y hh hy.le)).2
  have hp := extension_negative_polynomial_le m γ y hm
  have hd := extension_density_nonneg m y hmpos
  rw [lowHIntegrand, norm_mul, extension_physical_norm m γ y hmpos]
  calc
    _ ≤ (3 * |y + 1| * (gaussianCoordinate m y ^ 2 + γ ^ 2 + 1) *
        gaussianDensity m y) * (8 * Real.exp (-2 * y)) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ = 24 * (|y + 1| * (gaussianCoordinate m y ^ 2 + γ ^ 2 + 1)) *
        (gaussianDensity m y * Real.exp (-2 * y)) := by ring
    _ = 24 * (|y + 1| * (gaussianCoordinate m y ^ 2 + γ ^ 2 + 1)) *
        (Real.exp (-28 * m) * ProbabilityTheory.gaussianPDFReal (12 * m)
          (D5.S3.Arith.Robin.CompleteLowHGaussianMoment.variance m hmpos) y) := by
      rw [extension_negative_tilt m y hmpos]
    _ ≤ 24 * ((13 * m + 1 + (y - 12 * m) ^ 2 / (4 * m)) *
        ((y - 12 * m) ^ 2 / (2 * m ^ 2) + γ ^ 2 + 9)) *
        (Real.exp (-28 * m) * ProbabilityTheory.gaussianPDFReal (12 * m)
          (D5.S3.Arith.Robin.CompleteLowHGaussianMoment.variance m hmpos) y) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by norm_num))
        (mul_nonneg (Real.exp_nonneg _) (ProbabilityTheory.gaussianPDFReal_nonneg _ _ _))
    _ = _ := by ring

theorem complete_zero_negative_extension_bound
    (Z : CompleteZeroFamily) (m γ : ℝ) (hm : 1 ≤ m) (hγ : 10 < γ) :
    ‖negativeExtension Z m γ‖ ≤ 384 * m * D γ ^ 2 * Real.exp (-28 * m) := by
  let hmpos : 0 < m := by linarith
  let v := D5.S3.Arith.Robin.CompleteLowHGaussianMoment.variance m hmpos
  let F := fun y : ℝ => ProbabilityTheory.gaussianPDFReal (12 * m) v y *
    ((13 * m + 1 + (y - 12 * m) ^ 2 / (4 * m)) *
      ((y - 12 * m) ^ 2 / (2 * m ^ 2) + γ ^ 2 + 9))
  have hF : Integrable F ∧ (∫ y : ℝ, F y) ≤ 16 * m * D γ ^ 2 :=
    extension_negative_majorant_integral m γ hm hγ
  have hFnonneg : ∀ y, 0 ≤ F y := by
    intro y
    dsimp [F]
    exact mul_nonneg (ProbabilityTheory.gaussianPDFReal_nonneg _ _ _)
      (mul_nonneg (by positivity) (by positivity))
  have hG : Integrable (fun y => (24 * Real.exp (-28 * m)) * F y) :=
    hF.1.const_mul _
  have hf : IntegrableOn (lowHIntegrand Z m γ) (Iio (0 : ℝ)) :=
    (complete_zero_fullLine_integrable_and_moment Z m γ hmpos).1.integrableOn
  have hbound : ∀ᵐ y ∂(volume.restrict (Iio (0 : ℝ))),
      ‖lowHIntegrand Z m γ y‖ ≤ (24 * Real.exp (-28 * m)) * F y := by
    filter_upwards [ae_restrict_mem measurableSet_Iio] with y hy
    exact extension_negative_pointwise Z m γ y hm hy
  calc
    ‖negativeExtension Z m γ‖ = ‖∫ y in Iio (0 : ℝ), lowHIntegrand Z m γ y‖ := by
      rw [negativeExtension, norm_neg]
    _ ≤ ∫ y in Iio (0 : ℝ), ‖lowHIntegrand Z m γ y‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ y in Iio (0 : ℝ), (24 * Real.exp (-28 * m)) * F y :=
      integral_mono_ae hf.norm hG.integrableOn hbound
    _ ≤ ∫ y : ℝ, (24 * Real.exp (-28 * m)) * F y :=
      setIntegral_le_integral hG (ae_of_all volume fun y =>
        mul_nonneg (by positivity) (hFnonneg y))
    _ = (24 * Real.exp (-28 * m)) * (∫ y : ℝ, F y) := integral_const_mul _ _
    _ ≤ (24 * Real.exp (-28 * m)) * (16 * m * D γ ^ 2) :=
      mul_le_mul_of_nonneg_left hF.2 (by positivity)
    _ = 384 * m * D γ ^ 2 * Real.exp (-28 * m) := by ring


structure LowHCertificates (Z : CompleteZeroFamily) (m γ : ℝ) : Prop where
  m_ge_one : 1 ≤ m
  gamma_gt_ten : 10 < γ

lemma shell_exp_constant (m γ : ℝ) (hm : 1 ≤ m) (hγ : 10 < γ) :
    24 * m * D γ ^ 2 * (10000 * Real.exp (-100 * m)) *
        Real.exp (17 * m) ≤
      m * D γ ^ 2 * (2400000 * Real.exp (-83 * m)) := by
  have hm0 : 0 ≤ m := by linarith
  have hd : 0 ≤ D γ ^ 2 := sq_nonneg _
  have he : -100 * m + 17 * m = -83 * m := by ring
  calc
    24 * m * D γ ^ 2 * (10000 * Real.exp (-100 * m)) *
        Real.exp (17 * m) =
      m * D γ ^ 2 * (240000 * Real.exp (-83 * m)) := by
        calc
          _ = (m * D γ ^ 2 * 240000) *
              (Real.exp (-100 * m) * Real.exp (17 * m)) := by ring
          _ = _ := by rw [← Real.exp_add, he]; ring
    _ ≤ m * D γ ^ 2 * (2400000 * Real.exp (-83 * m)) := by
      gcongr
      norm_num

lemma shell_exp_constant240 (m γ : ℝ) :
    240 * m * D γ ^ 2 * (10000 * Real.exp (-100 * m)) *
        Real.exp (17 * m) =
      m * D γ ^ 2 * (2400000 * Real.exp (-83 * m)) := by
  have he : -100 * m + 17 * m = -83 * m := by ring
  calc
    240 * m * D γ ^ 2 * (10000 * Real.exp (-100 * m)) *
        Real.exp (17 * m) =
      m * D γ ^ 2 * (2400000 * Real.exp (-83 * m)) := by
        calc
          _ = (m * D γ ^ 2 * 2400000) *
              (Real.exp (-100 * m) * Real.exp (17 * m)) := by ring
          _ = _ := by rw [← Real.exp_add, he]; ring

/-- All-index complex shell consumer, with the original numerical coefficient
    and decay exponent.  Fubini and extension assumptions are not needed. -/
theorem complete_real_line_mean_bound
    (Z : CompleteZeroFamily) (m γ : ℝ) (hm : 1 ≤ m) (hγ : 10 < γ) :
    ‖completeRealLineMean Z m γ‖ ≤
      m * D γ ^ 2 * (2400000 * Real.exp (-83 * m)) := by
  have hm0 : 0 ≤ m := by linarith
  have hcount := (shell_summable_and_count_bound Z m hm).2
  calc
    _ ≤ 240 * m * D γ ^ 2 * shellSum Z m * Real.exp (17 * m) :=
      complete_real_line_mean_bound240 Z m γ hm hγ
    _ ≤ 240 * m * D γ ^ 2 * (10000 * Real.exp (-100 * m)) *
        Real.exp (17 * m) := by
      gcongr <;> exact hcount
    _ = m * D γ ^ 2 * (2400000 * Real.exp (-83 * m)) := shell_exp_constant240 m γ

theorem complete_low_h_weighted_mean_bound
    (Z : CompleteZeroFamily) (m γ : ℝ)
    (h : LowHCertificates Z m γ) :
    IntegrableOn (lowHIntegrand Z m γ) (Ioi (1 : ℝ)) ∧
      ‖lowHMean Z m γ‖ ≤
        m * D γ ^ 2 *
          (2400000 * Real.exp (-83 * m) + 2400 +
            384 * Real.exp (-28 * m)) := by
  have hm : 0 < m := by linarith [h.m_ge_one]
  refine ⟨(complete_zero_fullLine_integrable_and_moment Z m γ hm).1.integrableOn, ?_⟩
  rw [complete_zero_fubini_exchange Z m γ hm]
  have hshell : ‖completeRealLineMean Z m γ‖ ≤
      m * D γ ^ 2 * (2400000 * Real.exp (-83 * m)) :=
    complete_real_line_mean_bound Z m γ h.m_ge_one h.gamma_gt_ten
  calc
    ‖completeRealLineMean Z m γ + positiveExtension Z m γ +
        negativeExtension Z m γ‖ ≤
        ‖completeRealLineMean Z m γ‖ +
          ‖positiveExtension Z m γ‖ + ‖negativeExtension Z m γ‖ := by
      exact norm_add₃_le
    _ ≤ m * D γ ^ 2 * (2400000 * Real.exp (-83 * m)) +
        2400 * m * D γ ^ 2 +
        384 * m * D γ ^ 2 * Real.exp (-28 * m) := by
      linarith [hshell,
        complete_zero_positive_extension_bound Z m γ h.m_ge_one h.gamma_gt_ten,
        complete_zero_negative_extension_bound Z m γ h.m_ge_one h.gamma_gt_ten]
    _ = m * D γ ^ 2 *
        (2400000 * Real.exp (-83 * m) + 2400 +
          384 * Real.exp (-28 * m)) := by ring

/- The native run records direct constants of the compiled proof terms.
This command adds no mathematical declaration. -/
run_cmd do
  let env ← Lean.getEnv
  for name in [``extension_kernel_norm_le,
      ``extension_inner_integrable_and_bound,
      ``extension_positive_exp_le,
      ``extension_negative_exp_le,
      ``extension_density_nonneg,
      ``extension_physical_norm,
      ``extension_positive_physical_le,
      ``complete_zero_positive_extension_bound,
      ``extension_central_density_integrable,
      ``extension_central_density_moments,
      ``extension_negative_tilt,
      ``extension_negative_polynomial_le,
      ``extension_negative_majorant_integral,
      ``extension_negative_pointwise,
      ``complete_zero_negative_extension_bound,
      ``physicalEnvelope_gaussian_moment,
      ``fullLine_term_moment,
      ``complete_zero_fullLine_integrable_and_moment,
      ``complete_zero_fubini_exchange,
      ``divided_cubic_polynomial_bound_two,
      ``divided_cubic_coefficient_core_two,
      ``shell_term_bound24,
      ``shell_terms_norm_summable,
      ``divided_cubic_coefficient_core_bound,
      ``shell_term_bound240,
      ``complete_real_line_mean_bound240,
      ``complete_real_line_mean_bound,
      ``complete_low_h_weighted_mean_bound] do
    let some info := env.find? name | throwError "missing native consumer {name}"
    let some value := info.value? (allowOpaque := true) |
      throwError "missing native proof {name}"
    let refs := value.getUsedConstants.filter fun n =>
      n.toString.startsWith "D5." || n.toString.startsWith "_private.D5."
    Lean.logInfo m!"RH_EXTENSION_NATIVE_CONSUMER {name}: {refs}"

end D5.S3.Arith.Robin.CompleteLowHWeightedSpectralMean
