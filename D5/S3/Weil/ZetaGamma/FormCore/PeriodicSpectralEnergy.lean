/- GID: D5/S3/Weil/ZetaGamma/FormCore/PeriodicSpectralEnergy
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaGamma/FormCore/PeriodicSpectralEnergy
   mirror-E: none(waiver:analytic-Gamma-form-core)
   anchors: []
   utility: none
   digest: Periodic Parseval and the actual digamma multiplier. -/


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
open AddCircle

namespace D5.S3.Weil.ZetaGamma.FormCore.PeriodicSpectralEnergy

variable {d : ℝ} [hd : Fact (0 < d)]

private abbrev circleHaar : Measure (AddCircle d) :=
  AddCircle.haarAddCircle

private def circleShift (f : AddCircle d → ℂ) (s : ℝ) : AddCircle d → ℂ :=
  fun x => f (x - (s : AddCircle d))

def phaseGap (n : ℤ) (s : ℝ) : ℝ :=
  ‖(1 : ℂ) - (@fourier d n) (-(s : AddCircle d))‖ ^ 2

def angularFrequency (n : ℤ) : ℝ :=
  2 * Real.pi * (n : ℝ) / d

private def circleGapMass (f : AddCircle d → ℂ) (s : ℝ) : ℝ :=
  ∫ x : AddCircle d, ‖f x - circleShift f s x‖ ^ 2 ∂circleHaar

def physicalCoeff (f : AddCircle d → ℂ) (n : ℤ) : ℂ :=
  (Real.sqrt d : ℂ) * fourierCoeff f n

private theorem normSq_physicalCoeff (f : AddCircle d → ℂ) (n : ℤ) :
    ‖physicalCoeff f n‖ ^ 2 = d * ‖fourierCoeff f n‖ ^ 2 := by
  simp only [physicalCoeff, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg d), mul_pow,
    Real.sq_sqrt hd.out.le]

omit hd in

private theorem fourier_phase_eq_exp (n : ℤ) (s : ℝ) :
    (@fourier d n) (-(s : AddCircle d)) =
      Complex.exp (((-(angularFrequency (d := d) n * s) : ℝ) : ℂ) * Complex.I) := by
  rw [← AddCircle.coe_neg, fourier_coe_apply]
  congr 1
  simp only [angularFrequency, Complex.ofReal_neg, Complex.ofReal_mul,
    Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_intCast]
  ring

omit hd in
private theorem phaseGap_eq_two_one_sub_cos (n : ℤ) (s : ℝ) :
    phaseGap (d := d) n s =
      2 * (1 - Real.cos (angularFrequency (d := d) n * s)) := by
  have hnorm : Complex.normSq ((@fourier d n) (-(s : AddCircle d))) = 1 := by
    rw [Complex.normSq_eq_norm_sq]
    simp only [fourier_apply, Circle.norm_coe, one_pow]
  have hre : ((@fourier d n) (-(s : AddCircle d))).re =
      Real.cos (angularFrequency (d := d) n * s) := by
    rw [fourier_phase_eq_exp, Complex.exp_ofReal_mul_I_re, Real.cos_neg]
  rw [phaseGap, Complex.sq_norm, Complex.normSq_sub, Complex.normSq_one, hnorm]
  simp only [one_mul, Complex.conj_re]
  rw [hre]
  ring

omit hd in

private theorem fourier_spatial_add (n : ℤ) (x y : AddCircle d) :
    fourier n (x + y) = fourier n x * fourier n y := by
  simp only [fourier_apply, zsmul_add, AddCircle.toCircle_add, Circle.coe_mul]

omit hd in
private theorem fourier_neg_index_at_point (n : ℤ) (x : AddCircle d) :
    fourier (-n) x = fourier n (-x) := by
  simp only [fourier_apply, neg_zsmul, zsmul_neg]

private theorem fourierCoeff_circleShift (f : AddCircle d → ℂ) (s : ℝ) (n : ℤ) :
    fourierCoeff (circleShift f s) n =
      fourier n (-(s : AddCircle d)) * fourierCoeff f n := by
  simp only [fourierCoeff, smul_eq_mul, circleShift]
  calc
    (∫ x : AddCircle d, fourier (-n) x * f (x - (s : AddCircle d))
        ∂circleHaar) =
        ∫ x : AddCircle d, fourier (-n) (x + (s : AddCircle d)) * f x
          ∂circleHaar := by
      simpa only [add_sub_cancel_right] using
        (integral_add_right_eq_self (μ := circleHaar)
          (fun x : AddCircle d => fourier (-n) x * f (x - (s : AddCircle d)))
          (s : AddCircle d)).symm
    _ = ∫ x : AddCircle d,
        fourier (-n) (s : AddCircle d) * (fourier (-n) x * f x)
          ∂circleHaar := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        dsimp only
        rw [fourier_spatial_add]
        ring
    _ = fourier n (-(s : AddCircle d)) *
        ∫ x : AddCircle d, fourier (-n) x * f x ∂circleHaar := by
      rw [integral_const_mul, fourier_neg_index_at_point]

private theorem circleShift_memLp (f : AddCircle d → ℂ)
    (hf : MemLp f 2 circleHaar) (s : ℝ) :
    MemLp (circleShift f s) 2 circleHaar := by
  exact hf.comp_measurePreserving
    (measurePreserving_sub_right circleHaar (s : AddCircle d))

private theorem fourierCoeff_sub_circleShift (f : AddCircle d → ℂ)
    (hf : MemLp f 2 circleHaar) (s : ℝ) (n : ℤ) :
    fourierCoeff (fun x => f x - circleShift f s x) n =
      (1 - fourier n (-(s : AddCircle d))) * fourierCoeff f n := by
  have hf1 : Integrable f circleHaar := MemLp.integrable (by norm_num) hf
  have hs1 : Integrable (circleShift f s) circleHaar :=
    MemLp.integrable (by norm_num) (circleShift_memLp f hf s)
  calc
    _ = fourierCoeff f n - fourierCoeff (circleShift f s) n := by
      simp only [fourierCoeff, smul_eq_mul, mul_sub]
      exact integral_sub (hf1.fourier_smul (-n)) (hs1.fourier_smul (-n))
    _ = _ := by rw [fourierCoeff_circleShift]; ring

private theorem hasSum_phaseGap_coeff (f : AddCircle d → ℂ)
    (hf : MemLp f 2 circleHaar) (s : ℝ) :
    HasSum (fun n : ℤ => phaseGap (d := d) n s * ‖fourierCoeff f n‖ ^ 2)
      (circleGapMass f s) := by
  let g : AddCircle d → ℂ := fun x => f x - circleShift f s x
  have hg : MemLp g 2 circleHaar := hf.sub (circleShift_memLp f hf s)
  let gLp : Lp ℂ 2 circleHaar := MemLp.toLp g hg
  have hcoef : fourierCoeff gLp = fourierCoeff g :=
    fourierCoeff_congr_ae hg.coeFn_toLp
  have hmass : (∫ x : AddCircle d, ‖gLp x‖ ^ 2 ∂circleHaar) =
      circleGapMass f s := by
    apply integral_congr_ae
    filter_upwards [hg.coeFn_toLp] with x hx
    rw [hx]
  have h := hasSum_sq_fourierCoeff gLp
  rw [hcoef, hmass] at h
  simpa only [g, fourierCoeff_sub_circleShift f hf s,
    norm_mul, mul_pow, phaseGap] using h

private theorem physicalGapMass_eq_tsum (f : AddCircle d → ℂ)
    (hf : MemLp f 2 circleHaar) (s : ℝ) :
    ENNReal.ofReal (d * circleGapMass f s) =
      ∑' n : ℤ, ENNReal.ofReal (phaseGap (d := d) n s) *
        ENNReal.ofReal (‖physicalCoeff f n‖ ^ 2) := by
  have h := (hasSum_phaseGap_coeff f hf s).mul_left d
  calc
    _ = ENNReal.ofReal (∑' n : ℤ,
        d * (phaseGap (d := d) n s * ‖fourierCoeff f n‖ ^ 2)) :=
      congrArg ENNReal.ofReal h.tsum_eq.symm
    _ = ∑' n : ℤ,
        ENNReal.ofReal (d * (phaseGap (d := d) n s * ‖fourierCoeff f n‖ ^ 2)) :=
      ENNReal.ofReal_tsum_of_nonneg
        (fun n => mul_nonneg hd.out.le
          (mul_nonneg (sq_nonneg _) (sq_nonneg _))) h.summable
    _ = _ := by
      apply tsum_congr
      intro n
      rw [normSq_physicalCoeff]
      have hp : 0 ≤ phaseGap (d := d) n s := sq_nonneg _
      rw [← ENNReal.ofReal_mul hp]
      congr 1
      ring

omit hd in
private theorem measurable_phaseGap (n : ℤ) : Measurable (phaseGap (d := d) n) := by
  have h : Continuous (fun s : ℝ =>
      (1 : ℂ) - (@fourier d n) (-(s : AddCircle d))) :=
    continuous_const.sub
      ((fourier n).continuous.comp (AddCircle.continuous_mk' d).neg)
  exact (h.norm.pow 2).measurable

private theorem extended_circle_energy_eq_tsum
    (k : ℝ → ℝ) (hk : Measurable k) (f : AddCircle d → ℂ)
    (hf : MemLp f 2 circleHaar) :
    (∫⁻ s : ℝ in Ioi 0,
      ENNReal.ofReal (k s) * ENNReal.ofReal (d * circleGapMass f s)) =
      ∑' n : ℤ,
        (∫⁻ s : ℝ in Ioi 0,
          ENNReal.ofReal (k s) * ENNReal.ofReal (phaseGap (d := d) n s)) *
        ENNReal.ofReal (‖physicalCoeff f n‖ ^ 2) := by
  have hmeas (n : ℤ) : Measurable (fun s : ℝ =>
      ENNReal.ofReal (k s) * ENNReal.ofReal (phaseGap (d := d) n s)) :=
    (ENNReal.measurable_ofReal.comp hk).mul
      (ENNReal.measurable_ofReal.comp (measurable_phaseGap n))
  calc
    _ = ∫⁻ s : ℝ in Ioi 0, ∑' n : ℤ,
        (ENNReal.ofReal (k s) * ENNReal.ofReal (phaseGap (d := d) n s)) *
          ENNReal.ofReal (‖physicalCoeff f n‖ ^ 2) := by
      apply lintegral_congr_ae
      exact Filter.Eventually.of_forall fun s => by
        dsimp only
        rw [physicalGapMass_eq_tsum f hf s, ← ENNReal.tsum_mul_left]
        apply tsum_congr
        intro n
        exact (mul_assoc _ _ _).symm
    _ = ∑' n : ℤ, ∫⁻ s : ℝ in Ioi 0,
        (ENNReal.ofReal (k s) * ENNReal.ofReal (phaseGap (d := d) n s)) *
          ENNReal.ofReal (‖physicalCoeff f n‖ ^ 2) :=
      lintegral_tsum fun n => ((hmeas n).mul_const _).aemeasurable
    _ = _ := by
      apply tsum_congr
      intro n
      exact lintegral_mul_const'' _ (hmeas n).aemeasurable

def windowGapMass (t : ℝ) (u : ℝ → ℂ) (s : ℝ) : ℝ :=
  ∫ x : ℝ in Ioc t (t + d),
    ‖u x - AddCircle.liftIoc d t u ((x - s : ℝ) : AddCircle d)‖ ^ 2

private theorem windowGapMass_eq_physicalCircleGap
    (t : ℝ) (u : ℝ → ℂ) (s : ℝ) :
    windowGapMass (d := d) t u s =
      d * circleGapMass (AddCircle.liftIoc d t u) s := by
  calc
    _ = ∫ c : AddCircle d,
        ‖AddCircle.liftIoc d t u c -
          AddCircle.liftIoc d t u (c - (s : AddCircle d))‖ ^ 2 := by
      rw [← AddCircle.integral_preimage d t]
      apply integral_congr_ae
      filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with x hx
      rw [AddCircle.liftIoc_coe_apply (p := d) (a := t) (f := u) hx]
      simp only [AddCircle.coe_sub]
    _ = _ := by
      rw [AddCircle.volume_eq_smul_haarAddCircle, integral_smul_measure,
        ENNReal.toReal_ofReal hd.out.le]
      rfl

theorem extended_window_energy_eq_tsum
    (k : ℝ → ℝ) (hk : Measurable k) (t : ℝ) (u : ℝ → ℂ)
    (hu : MemLp u 2 (volume.restrict (Ioc t (t + d)))) :
    (∫⁻ s : ℝ in Ioi 0,
      ENNReal.ofReal (k s) * ENNReal.ofReal (windowGapMass (d := d) t u s)) =
      ∑' n : ℤ,
        (∫⁻ s : ℝ in Ioi 0,
          ENNReal.ofReal (k s) * ENNReal.ofReal (phaseGap (d := d) n s)) *
        ENNReal.ofReal (‖physicalCoeff (AddCircle.liftIoc d t u) n‖ ^ 2) := by
  simp_rw [windowGapMass_eq_physicalCircleGap]
  exact extended_circle_energy_eq_tsum k hk _ hu.memLp_liftIoc.haarAddCircle

abbrev gammaDensity : ℝ → ℝ :=
  D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.archimedeanJumpDensity

def gammaIncrement (z : ℝ) : ℝ :=
  (Complex.digamma ((1 / 4 : ℂ) + Complex.I * ((z / 2 : ℝ) : ℂ))).re -
    (Complex.digamma (1 / 4)).re

/-- Actual digamma increments are nonnegative before ENNReal clipping. -/
theorem gammaIncrement_nonneg (z : ℝ) : 0 ≤ gammaIncrement z := by
  unfold gammaIncrement
  rw [← D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.levy_integral_eq_digamma z]
  apply integral_nonneg_of_ae
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
  exact mul_nonneg (mul_nonneg (by norm_num)
    (D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.archimedeanJumpDensity_nonneg hs))
    (sub_nonneg.mpr (Real.cos_le_one _))

private theorem measurable_gammaDensity : Measurable gammaDensity := by
  unfold gammaDensity
    D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.archimedeanJumpDensity
  fun_prop

theorem actual_gamma_spectralWeight (n : ℤ) :
    (∫⁻ s : ℝ in Ioi 0,
      ENNReal.ofReal (gammaDensity s) * ENNReal.ofReal (phaseGap (d := d) n s)) =
      ENNReal.ofReal (gammaIncrement (angularFrequency (d := d) n)) := by
  let z : ℝ := angularFrequency (d := d) n
  have hInt : IntegrableOn
      (fun s : ℝ => 2 * gammaDensity s * (1 - Real.cos (z * s))) (Ioi 0) :=
    D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.levy_integrableOn z
  have hnn : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
      0 ≤ 2 * gammaDensity s * (1 - Real.cos (z * s)) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
    exact mul_nonneg (mul_nonneg (by norm_num)
      (D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.archimedeanJumpDensity_nonneg hs))
      (sub_nonneg.mpr (Real.cos_le_one _))
  calc
    _ = ∫⁻ s : ℝ in Ioi 0,
        ENNReal.ofReal (2 * gammaDensity s * (1 - Real.cos (z * s))) := by
      apply lintegral_congr_ae
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
      rw [phaseGap_eq_two_one_sub_cos,
        ← ENNReal.ofReal_mul
          (D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.archimedeanJumpDensity_nonneg hs)]
      congr 1
      dsimp only [z]
      ring
    _ = ENNReal.ofReal
        (∫ s : ℝ in Ioi 0, 2 * gammaDensity s * (1 - Real.cos (z * s))) :=
      (ofReal_integral_eq_lintegral_ofReal hInt hnn).symm
    _ = ENNReal.ofReal (gammaIncrement (angularFrequency (d := d) n)) :=
      congrArg ENNReal.ofReal
        (D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.levy_integral_eq_digamma z)

theorem actual_gamma_periodic_energy_eq_tsum
    (t : ℝ) (u : ℝ → ℂ)
    (hu : MemLp u 2 (volume.restrict (Ioc t (t + d)))) :
    (∫⁻ s : ℝ in Ioi 0,
      ENNReal.ofReal (gammaDensity s) *
        ENNReal.ofReal (windowGapMass (d := d) t u s)) =
      ∑' n : ℤ,
        ENNReal.ofReal (gammaIncrement (angularFrequency (d := d) n)) *
          ENNReal.ofReal (‖physicalCoeff (AddCircle.liftIoc d t u) n‖ ^ 2) := by
  rw [extended_window_energy_eq_tsum gammaDensity measurable_gammaDensity t u hu]
  apply tsum_congr
  intro n
  rw [actual_gamma_spectralWeight]

end D5.S3.Weil.ZetaGamma.FormCore.PeriodicSpectralEnergy
