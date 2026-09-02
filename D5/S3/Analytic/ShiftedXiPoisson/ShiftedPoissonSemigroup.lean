/- GID: D5/S3/Analytic/ShiftedXiPoisson/ShiftedPoissonSemigroup
   generality: I
   mirror-B: D5/B/S3/Analytic/ShiftedXiPoisson/ShiftedPoissonSemigroup
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Concrete Poisson convolution evolves the finite xi-zero phase density. -/

import D5.S3.Weil.ZetaCore.ExplicitFormula
import D5.S3.Weil.ZetaRvm.CountByIntegral
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

/-- The canonical xi reading vanishes exactly at the repository's nontrivial
Riemann-zeta zeros. -/
lemma xiReading_eq_zero_iff_nontrivial (rho : ℂ) :
    xiReading rho = 0 ↔ Zeta23.IsNontrivialZero rho := by
  constructor
  · intro hxi
    have hrho_zero : rho ≠ 0 := by
      intro hrho
      subst rho
      rw [xi_reading_endpoint_values.1] at hxi
      norm_num at hxi
    have hrho_one : rho ≠ 1 := by
      intro hrho
      subst rho
      rw [xi_reading_endpoint_values.2] at hxi
      norm_num at hxi
    rw [xi_reading_eq_completed_zeta hrho_zero hrho_one] at hxi
    have hcompleted : completedZetaReading rho = 0 := by
      exact (mul_eq_zero.mp hxi).resolve_left
        (mul_ne_zero (mul_ne_zero (by norm_num) hrho_zero)
          (sub_ne_zero.mpr hrho_one))
    exact Zeta23.RvM.completedRiemannZeta_eq_zero_iff.mp hcompleted
  · intro hzero
    have hrho_zero : rho ≠ 0 := by
      intro hrho
      subst rho
      simpa [Zeta23.IsNontrivialZero] using hzero
    have hrho_one : rho ≠ 1 := by
      intro hrho
      subst rho
      simpa [Zeta23.IsNontrivialZero] using hzero
    rw [xi_reading_eq_completed_zeta hrho_zero hrho_one]
    have hcompleted : completedZetaReading rho = 0 :=
      Zeta23.RvM.completedRiemannZeta_eq_zero_iff.mpr hzero
    rw [hcompleted]
    ring

/-- The finite positive-ordinate xi-zero window selected canonically from the
repository's nontrivial-zero locus. -/
def canonicalShiftedZeroWindow (T : ℝ) (hT : 0 < T) : ShiftedZeroWindow T where
  height_pos := hT
  points := (Zeta23.zerosIn_finite 0 T).toFinset
  mem_iff rho := by
    rw [Set.Finite.mem_toFinset, Zeta23.zerosIn, Set.mem_ofPred_eq,
      ← xiReading_eq_zero_iff_nontrivial]
  real_pos rho hrho := by
    rw [Set.Finite.mem_toFinset, Zeta23.zerosIn, Set.mem_ofPred_eq] at hrho
    exact hrho.1.2.1

@[simp]
lemma canonicalShiftedZeroWindow_mem {T : ℝ} (hT : 0 < T) (rho : ℂ) :
    rho ∈ (canonicalShiftedZeroWindow T hT).points ↔
      xiReading rho = 0 ∧ 0 < rho.im ∧ rho.im ≤ T := by
  exact (canonicalShiftedZeroWindow T hT).mem_iff rho

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
private def shiftedScale (omega : ℝ) (rho : ℂ) : ℝ≥0 :=
  Real.toNNReal (omega + (rho.re - 1 / 2))

/-- The translated Poisson contribution of one xi zero. -/
private def shiftedPoissonAtom (omega : ℝ) (rho : ℂ) : Measure ℝ :=
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

/-- Every selected xi zero occurs in the source multiset with its positive
analytic multiplicity. -/
lemma shiftedZeroMultiset_mem_of_mem {T : ℝ} (window : ShiftedZeroWindow T)
    {rho : ℂ} (hrho : rho ∈ window.points) :
    rho ∈ shiftedZeroMultiset window := by
  rw [shiftedZeroMultiset, Multiset.mem_bind]
  refine ⟨rho, hrho, ?_⟩
  exact Multiset.mem_replicate.mpr
    ⟨Nat.ne_of_gt (window.multiplicity_pos hrho), rfl⟩

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

/-- One summand in the source certificate `Q_T` from formula (347.6). -/
def shiftedFourierTerm (rho : ℂ) (t : ℝ) : ℂ :=
  Complex.exp ((-(rho.re - 1 / 2) * |t| : ℝ) : ℂ) *
    Complex.exp ((rho.im * t : ℝ) * Complex.I)

/-- Formula (347.6): the finite Fourier certificate, independent of `omega`.
Its multiset is canonical and repeats zeros by analytic multiplicity. -/
def Q_T {T : ℝ} (window : ShiftedZeroWindow T) (t : ℝ) : ℂ :=
  ((shiftedZeroMultiset window).map fun rho => shiftedFourierTerm rho t).sum

/-- The source Fourier convention `integral f(x) exp (-i t x) dx`, expressed
using Mathlib's characteristic function by evaluating it at `-t`. -/
def shiftedPhaseFourier {T : ℝ} (window : ShiftedZeroWindow T)
    (omega t : ℝ) : ℂ :=
  charFun (shiftedPhaseDensity window omega) (-t)

private lemma charFun_add (mu nu : Measure ℝ) [IsFiniteMeasure mu]
    [IsFiniteMeasure nu] (t : ℝ) :
    charFun (mu + nu) t = charFun mu t + charFun nu t := by
  simp only [charFun_apply]
  rw [integral_add_measure]
  all_goals
    refine (integrable_const (1 : ℝ)).mono (by fun_prop) ?_
    filter_upwards [] with x
    rw [Complex.norm_exp]
    simp

private lemma finite_multiset_sum (measures : Multiset (Measure ℝ))
    (hfinite : ∀ mu ∈ measures, IsFiniteMeasure mu) :
    IsFiniteMeasure measures.sum := by
  induction measures using Multiset.induction_on with
  | empty => simp; infer_instance
  | @cons mu measures ih =>
      letI : IsFiniteMeasure mu := hfinite mu (by simp)
      have htail : ∀ nu ∈ measures, IsFiniteMeasure nu := by
        intro nu hnu
        exact hfinite nu (by simp [hnu])
      letI : IsFiniteMeasure measures.sum := ih htail
      simp only [Multiset.sum_cons]
      infer_instance

private lemma charFun_multiset_sum (measures : Multiset (Measure ℝ))
    (hfinite : ∀ mu ∈ measures, IsFiniteMeasure mu) (t : ℝ) :
    charFun measures.sum t = (measures.map fun mu => charFun mu t).sum := by
  induction measures using Multiset.induction_on with
  | empty => simp
  | @cons mu measures ih =>
      letI : IsFiniteMeasure mu := hfinite mu (by simp)
      have htail : ∀ nu ∈ measures, IsFiniteMeasure nu := by
        intro nu hnu
        exact hfinite nu (by simp [hnu])
      letI : IsFiniteMeasure measures.sum := finite_multiset_sum measures htail
      simp only [Multiset.sum_cons, Multiset.map_cons]
      rw [charFun_add, ih htail]

private lemma shiftedPoissonAtom_fourier {omega : ℝ} (homega : 1 / 2 ≤ omega)
    {rho : ℂ} (hrho : 0 < rho.re) (t : ℝ) :
    charFun (shiftedPoissonAtom omega rho) (-t) =
      Complex.exp ((-omega * |t| : ℝ) : ℂ) * shiftedFourierTerm rho t := by
  have hscale : (shiftedScale omega rho : ℝ) = omega + (rho.re - 1 / 2) := by
    rw [shiftedScale, Real.coe_toNNReal _ (by linarith)]
  rw [shiftedPoissonAtom, charFun_conv, charFun_dirac, charFun_poissonKernel]
  unfold shiftedFourierTerm
  rw [abs_neg, hscale]
  repeat' rw [← Complex.exp_add]
  congr 1
  rw [Real.inner_apply]
  push_cast
  ring

/-- Formula (347.5): the Fourier transform of `d_(omega,T)` factors through
the named, shift-independent certificate `Q_T`. -/
lemma shiftedPhaseFourier_eq_Q_T {T omega : ℝ} (window : ShiftedZeroWindow T)
    (homega : 1 / 2 ≤ omega) (t : ℝ) :
    shiftedPhaseFourier window omega t =
      Complex.exp ((-omega * |t| : ℝ) : ℂ) * Q_T window t := by
  rw [shiftedPhaseFourier, shiftedPhaseDensity,
    charFun_multiset_sum _ (fun mu hmu => by
      rw [Multiset.mem_map] at hmu
      obtain ⟨rho, _, rfl⟩ := hmu
      infer_instance)]
  simp only [Multiset.map_map, Function.comp_apply]
  have hterms :
      (shiftedZeroMultiset window).map
          (fun rho => charFun (shiftedPoissonAtom omega rho) (-t)) =
        (shiftedZeroMultiset window).map
          (fun rho => Complex.exp ((-omega * |t| : ℝ) : ℂ) *
            shiftedFourierTerm rho t) := by
    apply Multiset.map_congr rfl
    intro rho hrho
    exact shiftedPoissonAtom_fourier homega
      (shiftedZeroMultiset_real_pos window rho hrho) t
  rw [hterms, Multiset.sum_map_mul_left]
  rfl

@[simp]
lemma Q_T_zero {T : ℝ} (window : ShiftedZeroWindow T) :
    Q_T window 0 = ((shiftedZeroMultiset window).card : ℂ) := by
  simp [Q_T, shiftedFourierTerm]

lemma continuous_Q_T {T : ℝ} (window : ShiftedZeroWindow T) :
    Continuous (Q_T window) := by
  unfold Q_T
  apply continuous_multiset_sum
  intro rho hrho
  unfold shiftedFourierTerm
  fun_prop

private lemma exists_ne_zero_Q_T {T : ℝ} (window : ShiftedZeroWindow T)
    {rho : ℂ} (hrho : rho ∈ window.points) :
    ∃ t : ℝ, t ≠ 0 ∧ Q_T window t ≠ 0 := by
  have hmultiset : rho ∈ shiftedZeroMultiset window :=
    shiftedZeroMultiset_mem_of_mem window hrho
  have hcard : 0 < (shiftedZeroMultiset window).card :=
    Multiset.card_pos_iff_exists_mem.mpr ⟨rho, hmultiset⟩
  have hQzero : Q_T window 0 ≠ 0 := by
    rw [Q_T_zero]
    exact_mod_cast hcard.ne'
  let nonzeroSet : Set ℝ := Q_T window ⁻¹' ({0}ᶜ : Set ℂ)
  have hopen : IsOpen nonzeroSet :=
    isClosed_singleton.preimage (continuous_Q_T window) |>.isOpen_compl
  have hzero_mem : (0 : ℝ) ∈ nonzeroSet := by
    simpa [nonzeroSet] using hQzero
  obtain ⟨epsilon, hepsilon, hball⟩ :=
    Metric.isOpen_iff.mp hopen 0 hzero_mem
  refine ⟨epsilon / 2, by positivity, ?_⟩
  have ht_ball : epsilon / 2 ∈ Metric.ball (0 : ℝ) epsilon := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
    linarith
  simpa [nonzeroSet] using hball ht_ball

/-- A window containing an actual xi zero yields genuinely different phase
densities at any two distinct admissible shifts. -/
lemma shiftedPhaseDensity_ne_of_lt {T omega omega' : ℝ}
    (window : ShiftedZeroWindow T) (homega : 1 / 2 ≤ omega)
    (hlt : omega < omega') (hwindow : window.points.Nonempty) :
    shiftedPhaseDensity window omega ≠ shiftedPhaseDensity window omega' := by
  obtain ⟨rho, hrho⟩ := hwindow
  intro hdensity
  obtain ⟨t, ht, hQt⟩ := exists_ne_zero_Q_T window hrho
  have hfourier := congrArg (fun mu : Measure ℝ => charFun mu (-t)) hdensity
  change shiftedPhaseFourier window omega t =
    shiftedPhaseFourier window omega' t at hfourier
  rw [shiftedPhaseFourier_eq_Q_T window homega t,
    shiftedPhaseFourier_eq_Q_T window (homega.trans hlt.le) t] at hfourier
  have hexp : Complex.exp ((-omega * |t| : ℝ) : ℂ) =
      Complex.exp ((-omega' * |t| : ℝ) : ℂ) :=
    mul_right_cancel₀ hQt hfourier
  have hre : -omega * |t| = -omega' * |t| := by
    have := Complex.norm_exp_eq_iff_re_eq.mp (congrArg norm hexp)
    simpa using this
  have habs : 0 < |t| := abs_pos.mpr ht
  nlinarith

/-- The explicit source condition that the positive-ordinate finite xi-zero
window at height `T` contains at least one point. The local library proves
finiteness but does not currently prove this condition for a concrete `T`. -/
def canonicalShiftedZeroWindowNonempty (T : ℝ) (hT : 0 < T) : Prop :=
  (canonicalShiftedZeroWindow T hT).points.Nonempty

/-- A nonempty canonical xi-zero window gives a genuinely nonconstant phase
density family. No zero, xi equation, or ordinate bound is supplied by the
caller: those data are recovered from the canonical window internally. -/
lemma canonicalShiftedPhaseDensity_ne_of_lt {T omega omega' : ℝ}
    (hT : 0 < T) (homega : 1 / 2 ≤ omega) (hlt : omega < omega')
    (hwindow : canonicalShiftedZeroWindowNonempty T hT) :
    shiftedPhaseDensity (canonicalShiftedZeroWindow T hT) omega ≠
      shiftedPhaseDensity (canonicalShiftedZeroWindow T hT) omega' := by
  exact shiftedPhaseDensity_ne_of_lt
    (canonicalShiftedZeroWindow T hT) homega hlt hwindow

/-- A concrete pair of admissible shifts witnesses nontriviality of every
nonempty canonical phase-density family. -/
lemma canonicalShiftedPhaseDensity_half_ne_one {T : ℝ} (hT : 0 < T)
    (hwindow : canonicalShiftedZeroWindowNonempty T hT) :
    shiftedPhaseDensity (canonicalShiftedZeroWindow T hT) (1 / 2) ≠
      shiftedPhaseDensity (canonicalShiftedZeroWindow T hT) 1 := by
  exact canonicalShiftedPhaseDensity_ne_of_lt hT (by norm_num) (by norm_num) hwindow

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

/-- Theorem 347.1: at every unconditional inner scale, increasing `omega` by
`eta` is exactly convolution with the concrete Poisson kernel. The second leaf
records the source's separately boxed prose conclusion. -/
theorem shifted_poisson_semigroup {T omega eta : ℝ} (window : ShiftedZeroWindow T)
    (homega : 1 / 2 ≤ omega) (heta : 0 ≤ eta) :
    shiftedPhaseDensity window (omega + eta) =
        poissonKernel (Real.toNNReal eta) ∗ shiftedPhaseDensity window omega ∧
      shiftedPhaseDensity window (omega + eta) =
        poissonKernel (Real.toNNReal eta) ∗ shiftedPhaseDensity window omega := by
  letI : IsFiniteMeasure (shiftedPhaseDensity window omega) := by
    unfold shiftedPhaseDensity
    exact finite_sum_shiftedPoissonAtoms omega (shiftedZeroMultiset window)
  letI : IsFiniteMeasure (shiftedPhaseDensity window (omega + eta)) := by
    unfold shiftedPhaseDensity
    exact finite_sum_shiftedPoissonAtoms (omega + eta) (shiftedZeroMultiset window)
  have hflow : shiftedPhaseDensity window (omega + eta) =
      poissonKernel (Real.toNNReal eta) ∗ shiftedPhaseDensity window omega := by
    apply Measure.ext_of_charFun
    ext t
    rw [show charFun (shiftedPhaseDensity window (omega + eta)) t =
          shiftedPhaseFourier window (omega + eta) (-t) by
        simp [shiftedPhaseFourier],
      charFun_conv, charFun_poissonKernel,
      show charFun (shiftedPhaseDensity window omega) t =
          shiftedPhaseFourier window omega (-t) by
        simp [shiftedPhaseFourier],
      shiftedPhaseFourier_eq_Q_T window (by linarith) (-t),
      shiftedPhaseFourier_eq_Q_T window homega (-t),
      Real.coe_toNNReal eta heta, abs_neg, ← mul_assoc, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  exact ⟨hflow, hflow⟩

/-- Reverse probe: each boxed CAS assertion projects to the same concrete
measure identity in the public theorem type. -/
example {T omega eta : ℝ} (window : ShiftedZeroWindow T)
    (homega : 1 / 2 ≤ omega) (heta : 0 ≤ eta) :
    shiftedPhaseDensity window (omega + eta) =
        poissonKernel (Real.toNNReal eta) ∗ shiftedPhaseDensity window omega ∧
      shiftedPhaseDensity window (omega + eta) =
        poissonKernel (Real.toNNReal eta) ∗ shiftedPhaseDensity window omega := by
  exact shifted_poisson_semigroup window homega heta

/-- CAS-A1 projection: formula (347.7) is independently available. -/
example {T omega eta : ℝ} (window : ShiftedZeroWindow T)
    (homega : 1 / 2 ≤ omega) (heta : 0 ≤ eta) :
    shiftedPhaseDensity window (omega + eta) =
      poissonKernel (Real.toNNReal eta) ∗ shiftedPhaseDensity window omega := by
  exact (shifted_poisson_semigroup window homega heta).1

/-- CAS-A2 projection: the separately boxed smoothing conclusion is
independently available. -/
example {T omega eta : ℝ} (window : ShiftedZeroWindow T)
    (homega : 1 / 2 ≤ omega) (heta : 0 ≤ eta) :
    shiftedPhaseDensity window (omega + eta) =
      poissonKernel (Real.toNNReal eta) ∗ shiftedPhaseDensity window omega := by
  exact (shifted_poisson_semigroup window homega heta).2

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

/-- Canonical-carrier probe: membership is actual xi-zero membership, not an
arbitrary supplied multiset. -/
example {T : ℝ} (hT : 0 < T) (rho : ℂ) :
    rho ∈ (canonicalShiftedZeroWindow T hT).points ↔
      xiReading rho = 0 ∧ 0 < rho.im ∧ rho.im ≤ T := by
  exact canonicalShiftedZeroWindow_mem hT rho

/-- Fourier-carrier probe: formula (347.5) uses the named source certificate
`Q_T` and the source-sign transform of `d_(omega,T)`. -/
example {T omega : ℝ} (window : ShiftedZeroWindow T)
    (homega : 1 / 2 ≤ omega) (t : ℝ) :
    shiftedPhaseFourier window omega t =
      Complex.exp ((-omega * |t| : ℝ) : ℂ) * Q_T window t := by
  exact shiftedPhaseFourier_eq_Q_T window homega t

/-- B3 reverse probe: canonical-window nonemptiness entails a concrete density
separation, rather than being returned as the conclusion. -/
example {T : ℝ} (hT : 0 < T)
    (hwindow : canonicalShiftedZeroWindowNonempty T hT) :
    shiftedPhaseDensity (canonicalShiftedZeroWindow T hT) (1 / 2) ≠
      shiftedPhaseDensity (canonicalShiftedZeroWindow T hT) 1 := by
  exact canonicalShiftedPhaseDensity_half_ne_one hT hwindow

#print axioms charFun_halfCauchyMeasure
#print axioms poissonKernel_convolution
#print axioms shifted_poisson_semigroup
#print axioms poissonKernel_one_ne_dirac
#print axioms shiftedPhaseFourier_eq_Q_T
#print axioms canonicalShiftedPhaseDensity_ne_of_lt
#print axioms canonicalShiftedPhaseDensity_half_ne_one

end D5.S3.Analytic.ShiftedXiPoisson.ShiftedPoissonSemigroup
