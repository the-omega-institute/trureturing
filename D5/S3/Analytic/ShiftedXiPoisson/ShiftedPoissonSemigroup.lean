/- GID: D5/S3/Analytic/ShiftedXiPoisson/ShiftedPoissonSemigroup
   generality: I
   mirror-B: D5/B/S3/Analytic/ShiftedXiPoisson/ShiftedPoissonSemigroup
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Concrete Poisson convolution evolves the finite xi-zero phase density. -/

import D5.S3.Weil.ZetaCore.ExplicitFormula
import D5.S3.Zeros.Endpoints.XiEndpointValues
import Mathlib.Analysis.Analytic.Order
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Probability.Distributions.Cauchy

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Analytic.ShiftedXiPoisson.ShiftedPoissonSemigroup

open Complex MeasureTheory ProbabilityTheory
open D5.S3.Zeros.CompletedZeta
open D5.S3.Zeros.Endpoints.XiEndpointValues
open scoped BigOperators ENNReal NNReal Real FourierTransform MeasureTheory

/-- The source's finite set of distinct positive-ordinate xi zeros. Analytic
multiplicity is inserted canonically by `shiftedZeroMultiset`; the strip fields
record the standard zero strip used immediately before theorem 347.1. -/
structure ShiftedZeroWindow (T : ℝ) where
  height_pos : 0 < T
  points : Finset ℂ
  mem_iff : ∀ rho, rho ∈ points ↔
    xiReading rho = 0 ∧ 0 < rho.im ∧ rho.im ≤ T
  real_pos : ∀ rho ∈ points, 0 < rho.re

lemma xiReading_analyticOrderAt_ne_top (rho : ℂ) :
    analyticOrderAt xiReading rho ≠ ⊤ := by
  intro htop
  have hzero : xiReading = 0 :=
    (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero rho fun s =>
      xi_reading_differentiable.analyticAt s).mp htop
  have hzero_at_zero := congrFun hzero 0
  rw [xi_reading_endpoint_values.1] at hzero_at_zero
  norm_num at hzero_at_zero

/-- Every selected xi zero has a positive finite analytic multiplicity. -/
lemma ShiftedZeroWindow.multiplicity_pos {T : ℝ} (window : ShiftedZeroWindow T)
    {rho : ℂ} (hrho : rho ∈ window.points) :
    0 < analyticOrderNatAt xiReading rho := by
  have hzero : xiReading rho = 0 := (window.mem_iff rho).mp hrho |>.1
  have horder_ne_zero : analyticOrderAt xiReading rho ≠ 0 :=
    (xi_reading_differentiable.analyticAt rho).analyticOrderAt_ne_zero.mpr hzero
  have hcast := Nat.cast_analyticOrderNatAt (xiReading_analyticOrderAt_ne_top rho)
  apply Nat.pos_of_ne_zero
  intro hnat
  rw [hnat] at hcast
  exact horder_ne_zero hcast.symm

/-- The Cauchy probability measure of scale one half, whose Fourier transform
is the elementary pair already proved in `ExplicitFormula`. -/
def halfCauchyMeasure : Measure ℝ :=
  cauchyMeasure 0 (1 / 2)

instance : IsProbabilityMeasure halfCauchyMeasure := by
  unfold halfCauchyMeasure
  infer_instance

private def halfLaplace (u : ℝ) : ℂ :=
  Real.exp (-|u| / 2)

private lemma paperFT_halfLaplace_neg (tau : ℝ) :
    Zeta23.paperFT halfLaplace (((-tau : ℝ) : ℂ)) =
      1 / ((1 / 4 : ℂ) + (tau : ℂ) ^ 2) := by
  rw [Zeta23.paperFT]
  calc
    (∫ u : ℝ, halfLaplace u *
        Complex.exp (Complex.I * ((-tau : ℝ) : ℂ) * (u : ℂ))) =
        ∫ u : ℝ, (Real.exp (-|u| / 2) : ℂ) *
          Complex.exp (-Complex.I * tau * u) := by
      apply integral_congr_ae
      filter_upwards [] with u
      unfold halfLaplace
      congr 1
      push_cast
      ring
    _ = 1 / ((1 / 4 : ℂ) + tau ^ 2) :=
      Zeta23.EF.integral_exp_neg_abs_half tau

private lemma paperFT_halfLaplace (tau : ℝ) :
    Zeta23.paperFT halfLaplace (tau : ℂ) =
      1 / ((1 / 4 : ℂ) + (tau : ℂ) ^ 2) := by
  have h := paperFT_halfLaplace_neg (-tau)
  convert h using 1 <;> push_cast <;> ring

set_option maxHeartbeats 800000 in
-- The Fourier-notation dictionary triggers a costly elaboration unification.
private lemma fourier_halfLaplace_formula (w : ℝ) :
    (𝓕 halfLaplace) w =
      1 / ((1 / 4 : ℂ) + ((2 * Real.pi * w : ℝ) : ℂ) ^ 2) := by
  calc
    (𝓕 halfLaplace) w =
        (𝓕 halfLaplace) (-(-(2 * Real.pi * w)) / (2 * Real.pi)) := by
          congr 1
          field_simp [Real.pi_ne_zero]
    _ = Zeta23.paperFT halfLaplace (((-(2 * Real.pi * w) : ℝ) : ℂ)) :=
      (Zeta23.EF.paperFT_ofReal_eq_fourier halfLaplace (-(2 * Real.pi * w))).symm
    _ = 1 / ((1 / 4 : ℂ) + ((2 * Real.pi * w : ℝ) : ℂ) ^ 2) :=
      paperFT_halfLaplace_neg (2 * Real.pi * w)

private lemma fourier_halfLaplace_integrable : Integrable (𝓕 halfLaplace) := by
  have hreal : Integrable (fun w : ℝ ↦ 4 * (1 + (4 * Real.pi * w) ^ 2)⁻¹) :=
    (integrable_inv_one_add_sq.comp_mul_left'
      (mul_ne_zero (by norm_num) Real.pi_ne_zero)).const_mul 4
  refine hreal.ofReal.congr (ae_of_all _ fun w ↦ ?_)
  rw [fourier_halfLaplace_formula]
  push_cast
  field_simp
  ring_nf
  simp

private lemma halfLaplace_inverse (t : ℝ) :
    (1 / (2 * Real.pi) : ℂ) *
        ∫ r : ℝ, (1 / ((1 / 4 : ℂ) + (r : ℂ) ^ 2)) *
          Complex.exp ((t * r : ℝ) * Complex.I) =
      Complex.exp ((-|t| / 2 : ℝ) : ℂ) := by
  have hinv := Zeta23.EF.paper_inversion
    (k := halfLaplace) (by unfold halfLaplace; fun_prop)
    (by unfold halfLaplace; exact Zeta23.EF.integrable_exp_neg_abs_half)
    fourier_halfLaplace_integrable (-t)
  calc
    (1 / (2 * Real.pi) : ℂ) *
        ∫ r : ℝ, (1 / ((1 / 4 : ℂ) + (r : ℂ) ^ 2)) *
          Complex.exp ((t * r : ℝ) * Complex.I) =
        (1 / (2 * Real.pi) : ℂ) *
          ∫ r : ℝ, Zeta23.paperFT halfLaplace r *
            Complex.exp (-Complex.I * r * (-t)) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with r
      rw [paperFT_halfLaplace]
      congr 1
      push_cast
      ring
    _ = halfLaplace (-t) := by
      convert hinv.symm using 1 <;> push_cast <;> ring
    _ = Complex.exp ((-|t| / 2 : ℝ) : ℂ) := by
      unfold halfLaplace
      rw [abs_neg]
      exact Complex.ofReal_exp _

/-- The half-scale Cauchy characteristic function. -/
lemma charFun_halfCauchyMeasure (t : ℝ) :
    charFun halfCauchyMeasure t = Complex.exp ((-|t| / 2 : ℝ) : ℂ) := by
  rw [charFun_apply_real, halfCauchyMeasure,
    cauchyMeasure_of_scale_ne_zero 0 (by norm_num)]
  rw [integral_withDensity_eq_integral_toReal_smul
    (measurable_cauchyPDF 0 (1 / 2))
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  calc
    (∫ x : ℝ, (cauchyPDF 0 (1 / 2) x).toReal •
        Complex.exp (t * x * Complex.I)) =
        (1 / (2 * Real.pi) : ℂ) *
          ∫ x : ℝ, (1 / ((1 / 4 : ℂ) + (x : ℂ) ^ 2)) *
            Complex.exp ((t * x : ℝ) * Complex.I) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      rw [cauchyPDF, ENNReal.toReal_ofReal
        (cauchyPDF_pos 0 (by norm_num) x).le]
      simp only [cauchyPDFReal_def, Complex.real_smul]
      push_cast
      field_simp [Real.pi_ne_zero]
      ring
    _ = Complex.exp ((-|t| / 2 : ℝ) : ℂ) := halfLaplace_inverse t

/-- The half-plane Poisson kernel at nonnegative height `y`, represented as
the dilation by `2y` of a Cauchy law of scale one half. -/
def poissonKernel (y : ℝ≥0) : Measure ℝ :=
  halfCauchyMeasure.map (fun x : ℝ ↦ (2 * (y : ℝ)) * x)

instance (y : ℝ≥0) : IsProbabilityMeasure (poissonKernel y) := by
  unfold poissonKernel
  exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- The concrete Poisson kernel has Fourier multiplier `exp (-y |t|)`. -/
lemma charFun_poissonKernel (y : ℝ≥0) (t : ℝ) :
    charFun (poissonKernel y) t = Complex.exp ((-(y : ℝ) * |t| : ℝ) : ℂ) := by
  rw [poissonKernel, charFun_map_mul, charFun_halfCauchyMeasure]
  congr 1
  rw [abs_mul, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num),
    abs_of_nonneg y.coe_nonneg]
  ring_nf

/-- The actual Cauchy/Poisson kernels form the additive convolution semigroup,
including height zero. -/
lemma poissonKernel_convolution (y z : ℝ≥0) :
    poissonKernel y ∗ poissonKernel z = poissonKernel (y + z) := by
  apply Measure.ext_of_charFun
  ext t
  rw [charFun_conv, charFun_poissonKernel, charFun_poissonKernel,
    charFun_poissonKernel, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- At height zero the concrete kernel is the convolution identity. -/
@[simp]
lemma poissonKernel_zero : poissonKernel 0 = Measure.dirac 0 := by
  unfold poissonKernel halfCauchyMeasure
  simp

/-- A positive-height Poisson kernel is not the identity measure. This is the
noncollapse probe for the concrete flow carrier. -/
lemma poissonKernel_one_ne_dirac : poissonKernel 1 ≠ Measure.dirac 0 := by
  intro h
  have hchar := congrArg (fun mu : Measure ℝ ↦ charFun mu 1) h
  rw [charFun_poissonKernel] at hchar
  simp only [charFun_dirac] at hchar
  norm_num at hchar
  have hnorm := congrArg norm hchar
  rw [Complex.norm_exp] at hnorm
  norm_num at hnorm

/-- The source width `omega + delta_rho`, totalized as a nonnegative real for
the measure constructor. The theorem's strip and lower-bound hypotheses prove
that this totalization is exact on every selected zero. -/
def shiftedScale (omega : ℝ) (rho : ℂ) : ℝ≥0 :=
  Real.toNNReal (omega + (rho.re - 1 / 2))

/-- The translated Poisson contribution of one xi zero. -/
def shiftedPoissonAtom (omega : ℝ) (rho : ℂ) : Measure ℝ :=
  Measure.dirac (-rho.im) ∗ poissonKernel (shiftedScale omega rho)

instance (omega : ℝ) (rho : ℂ) :
    IsProbabilityMeasure (shiftedPoissonAtom omega rho) := by
  unfold shiftedPoissonAtom
  infer_instance

/-- The source's positive-ordinate zero multiset, obtained by repeating each
distinct zero according to the analytic order of the canonical xi reading. -/
def shiftedZeroMultiset {T : ℝ} (window : ShiftedZeroWindow T) : Multiset ℂ :=
  window.points.1.bind fun rho =>
    Multiset.replicate (analyticOrderNatAt xiReading rho) rho

lemma shiftedZeroMultiset_real_pos {T : ℝ} (window : ShiftedZeroWindow T) :
    ∀ rho ∈ shiftedZeroMultiset window, 0 < rho.re := by
  intro rho hrho
  rw [shiftedZeroMultiset, Multiset.mem_bind] at hrho
  obtain ⟨sigma, hsigma, hrho⟩ := hrho
  have hrho_eq : rho = sigma := (Multiset.mem_replicate.mp hrho).2
  subst rho
  exact window.real_pos sigma hsigma

/-- Formula (347.4), with the canonical analytic order carrying zero
multiplicity. -/
def shiftedPhaseDensity {T : ℝ} (window : ShiftedZeroWindow T) (omega : ℝ) : Measure ℝ :=
  ((shiftedZeroMultiset window).map (shiftedPoissonAtom omega)).sum

lemma shiftedScale_add {omega eta : ℝ} (homega : 1 / 2 ≤ omega)
    (heta : 0 ≤ eta) {rho : ℂ} (hrho : 0 < rho.re) :
    shiftedScale (omega + eta) rho =
      shiftedScale omega rho + Real.toNNReal eta := by
  apply NNReal.eq
  simp only [shiftedScale, NNReal.coe_add]
  rw [Real.coe_toNNReal _ (by linarith),
    Real.coe_toNNReal _ (by linarith),
    Real.coe_toNNReal _ heta]
  ring

lemma shiftedPoissonAtom_flow {omega eta : ℝ} (homega : 1 / 2 ≤ omega)
    (heta : 0 ≤ eta) {rho : ℂ} (hrho : 0 < rho.re) :
    poissonKernel (Real.toNNReal eta) ∗ shiftedPoissonAtom omega rho =
      shiftedPoissonAtom (omega + eta) rho := by
  unfold shiftedPoissonAtom
  rw [← Measure.conv_assoc,
    Measure.conv_comm (poissonKernel (Real.toNNReal eta)) (Measure.dirac (-rho.im)),
    Measure.conv_assoc, poissonKernel_convolution,
    add_comm (Real.toNNReal eta) (shiftedScale omega rho),
    ← shiftedScale_add homega heta hrho]

private lemma finite_sum_shiftedPoissonAtoms (omega : ℝ) (points : Multiset ℂ) :
    IsFiniteMeasure ((points.map (shiftedPoissonAtom omega)).sum) := by
  induction points using Multiset.induction_on with
  | empty =>
      simp
      infer_instance
  | @cons rho points ih =>
      rw [Multiset.map_cons, Multiset.sum_cons]
      letI : IsFiniteMeasure ((points.map (shiftedPoissonAtom omega)).sum) := ih
      infer_instance

private lemma shiftedPhaseDensity_flow_of_multiset {omega eta : ℝ}
    (points : Multiset ℂ) (hreal : ∀ rho ∈ points, 0 < rho.re)
    (homega : 1 / 2 ≤ omega) (heta : 0 ≤ eta) :
    poissonKernel (Real.toNNReal eta) ∗
        (points.map (shiftedPoissonAtom omega)).sum =
      (points.map (shiftedPoissonAtom (omega + eta))).sum := by
  induction points using Multiset.induction_on with
  | empty => simp
  | @cons rho points ih =>
      letI : IsFiniteMeasure ((points.map (shiftedPoissonAtom omega)).sum) :=
        finite_sum_shiftedPoissonAtoms omega points
      simp only [Multiset.map_cons, Multiset.sum_cons]
      rw [Measure.conv_add]
      rw [shiftedPoissonAtom_flow homega heta (hreal rho (by simp))]
      rw [ih (fun sigma hsigma ↦ hreal sigma (by simp [hsigma]))]

lemma shiftedPhaseDensity_flow {T omega eta : ℝ} (window : ShiftedZeroWindow T)
    (homega : 1 / 2 ≤ omega) (heta : 0 ≤ eta) :
    poissonKernel (Real.toNNReal eta) ∗ shiftedPhaseDensity window omega =
      shiftedPhaseDensity window (omega + eta) := by
  unfold shiftedPhaseDensity
  exact shiftedPhaseDensity_flow_of_multiset (shiftedZeroMultiset window)
    (shiftedZeroMultiset_real_pos window) homega heta

/-- Theorem 347.1: at every unconditional inner scale, increasing `omega` by
`eta` is exactly convolution with the concrete Poisson kernel. The second leaf
records the source's separately boxed prose conclusion. -/
theorem shifted_poisson_semigroup {T omega eta : ℝ} (window : ShiftedZeroWindow T)
    (homega : 1 / 2 ≤ omega) (heta : 0 ≤ eta) :
    shiftedPhaseDensity window (omega + eta) =
        poissonKernel (Real.toNNReal eta) ∗ shiftedPhaseDensity window omega ∧
      shiftedPhaseDensity window (omega + eta) =
        poissonKernel (Real.toNNReal eta) ∗ shiftedPhaseDensity window omega := by
  have hflow := shiftedPhaseDensity_flow window homega heta
  exact ⟨hflow.symm, hflow.symm⟩

/-- Reverse probe: each boxed CAS assertion projects to the same concrete
measure identity in the public theorem type. -/
example {T omega eta : ℝ} (window : ShiftedZeroWindow T)
    (homega : 1 / 2 ≤ omega) (heta : 0 ≤ eta) :
    shiftedPhaseDensity window (omega + eta) =
        poissonKernel (Real.toNNReal eta) ∗ shiftedPhaseDensity window omega ∧
      shiftedPhaseDensity window (omega + eta) =
        poissonKernel (Real.toNNReal eta) ∗ shiftedPhaseDensity window omega := by
  exact shifted_poisson_semigroup window homega heta

/-- Trivial-scale probe: `eta = 0` reduces to the genuine Dirac convolution
identity rather than exposing a constant or empty family. -/
example {T omega : ℝ} (window : ShiftedZeroWindow T) (homega : 1 / 2 ≤ omega) :
    shiftedPhaseDensity window (omega + 0) =
      Measure.dirac 0 ∗ shiftedPhaseDensity window omega := by
  simpa using (shifted_poisson_semigroup window homega (le_refl 0)).1

/-- Deleting the lower bound on `omega` makes the scale-addition law false. -/
example :
    shiftedScale ((-2 : ℝ) + 1) (1 : ℂ) ≠
      shiftedScale (-2 : ℝ) (1 : ℂ) + Real.toNNReal 1 := by
  norm_num [shiftedScale, Real.toNNReal_of_nonpos,
    Real.toNNReal_of_nonneg]

/-- Deleting nonnegativity of `eta` likewise makes scale addition false. -/
example :
    shiftedScale ((1 / 2 : ℝ) + (-1)) (1 : ℂ) ≠
      shiftedScale (1 / 2 : ℝ) (1 : ℂ) + Real.toNNReal (-1) := by
  norm_num [shiftedScale, Real.toNNReal_of_nonpos,
    Real.toNNReal_of_nonneg]

#print axioms charFun_halfCauchyMeasure
#print axioms poissonKernel_convolution
#print axioms shifted_poisson_semigroup
#print axioms poissonKernel_one_ne_dirac

end D5.S3.Analytic.ShiftedXiPoisson.ShiftedPoissonSemigroup
