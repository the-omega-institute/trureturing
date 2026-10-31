/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/ActualLinearPeak
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/ActualLinearPeak
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual integrated arithmetic kernel exceeds its linear envelope if RH fails. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.WholeFormula
import D5.S3.Analytic.Laplace.NonnegativeBoundary
import D5.S3.Analytic.ShiftedXiPoisson.ShiftedPoissonSemigroup
import D5.S3.Weil.Probability.AnalyticLogarithmicContinuation
import D5.S3.Weil.ZetaBridge.RightHalfStripRiemannReduction
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Topology
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-! Positive-tail transforms of the literal complete arithmetic kernel. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory
open D5.S3.Zeros.CompletedZeta
open D5.S3.Zeros.Endpoints.FirstLiCoefficientNormalization
open D5.S3.Zeros.Endpoints.XiEndpointValues
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open D5.S3.Analytic.ShiftedXiPoisson.ShiftedPoissonSemigroup
open scoped Topology ENNReal

namespace D5.S3.Weil.Mertens.IntegratedExplicit

private def linearCutoff : ℝ := Real.log 10000
private def linearKernel (t : ℝ) : ℝ := Real.exp (-t / 2) * (actualH t).re
private def linearDensity (t : ℝ) : ℝ := 4 * t + 9 - linearKernel t
private def linearTail : Measure ℝ :=
  (volume.restrict (Ioi linearCutoff)).withDensity (fun t => ENNReal.ofReal (linearDensity t))
private def shiftedXi (z : ℂ) : ℂ := xiReading (z + 1 / 2)
private def linearNumerator (z : ℂ) : ℂ :=
  (firstLiMass : ℂ) * z - deriv shiftedXi z / shiftedXi z
private def linearQuotient (z : ℂ) : ℂ :=
  dslope linearNumerator (1 / 2) z / (z + 1 / 2)
private def linearU : Set ℂ := {z | 0 < z.re ∧ shiftedXi z ≠ 0}

private theorem linearCutoff_pos : 0 < linearCutoff :=
  Real.log_pos (by norm_num)

private theorem linearKernel_continuous : Continuous linearKernel := by
  exact (show Continuous (fun t : ℝ => Real.exp (-t / 2)) by fun_prop).mul
    (Complex.continuous_re.comp actualH_continuous)

private theorem linearDensity_continuous : Continuous linearDensity := by
  exact (show Continuous (fun t : ℝ => 4 * t + 9) by fun_prop).sub
    linearKernel_continuous

private theorem linearKernel_arithmetic {t : ℝ} (ht : 0 < t) :
    linearKernel t = Real.exp (-t / 2) *
      (D5.S3.Arith.Robin.CompleteMertensPeak.U (Real.exp t) -
        Real.log (2 * Real.pi) + trivialT t) := by
  rw [linearKernel, actual_integrated_explicit_formula ht, Complex.ofReal_re]

private theorem shiftedXi_differentiable : Differentiable ℂ shiftedXi :=
  xi_reading_differentiable.comp (differentiable_id.add_const _)

private theorem shiftedXi_deriv (z : ℂ) : deriv shiftedXi z = deriv xiReading (z + 1 / 2) := by
  exact deriv_comp_add_const xiReading (1 / 2 : ℂ) z

private theorem shiftedXi_half : shiftedXi (1 / 2) = (1 / 2 : ℂ) := by
  norm_num [shiftedXi, xi_reading_endpoint_values.2]

private theorem linearNumerator_half : linearNumerator (1 / 2) = 0 := by
  rw [linearNumerator, shiftedXi_deriv]
  rw [show (1 / 2 : ℂ) + 1 / 2 = 1 by norm_num]
  rw [show shiftedXi (1 / 2) = xiReading 1 by
    change xiReading ((1 / 2 : ℂ) + 1 / 2) = xiReading 1
    congr 1; norm_num]
  rw [first_li_coefficient_normalization.1]
  dsimp [firstLiMass]
  push_cast
  ring

private theorem linearU_open : IsOpen linearU := by
  exact (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_ne_fun shiftedXi_differentiable.continuous continuous_const)

private theorem linearU_real (t : ℝ) (ht : 0 < t) : (t : ℂ) ∈ linearU := by
  refine ⟨by simpa using ht, ?_⟩
  intro hzero
  have hz := (xiReading_eq_zero_iff_nontrivial ((t : ℂ) + 1 / 2)).mp hzero
  have hh := actual_height_gt_ten ((t : ℂ) + 1 / 2) (by
    simpa only [Zeta23.IsNontrivialZero, D5.S3.Weil.ZeroSum.IsNontrivialZero,
      D5.S3.Weil.Convention.classicalZeta] using hz)
  norm_num at hh

private theorem linearNumerator_differentiable : DifferentiableOn ℂ linearNumerator linearU := by
  intro z hz
  exact ((differentiableAt_const _).mul differentiableAt_id).sub
    (((shiftedXi_differentiable.analyticAt z).deriv.differentiableAt).div
      (shiftedXi_differentiable z) hz.2) |>.differentiableWithinAt

private theorem linearQuotient_differentiable : DifferentiableOn ℂ linearQuotient linearU := by
  have hc : (1 / 2 : ℂ) ∈ linearU := by
    convert linearU_real (1 / 2) (by norm_num) using 1; norm_num
  have hd := (Complex.differentiableOn_dslope (c := (1 / 2 : ℂ))
    (linearU_open.mem_nhds hc)).mpr linearNumerator_differentiable
  intro z hz
  exact (hd z hz).div
    (show DifferentiableAt ℂ (fun w : ℂ => w + 1 / 2) z by fun_prop).differentiableWithinAt
    (by
      intro h
      have he := congrArg Complex.re h
      norm_num at he
      linarith [hz.1])

private theorem linearQuotient_identity {z : ℂ} (hz : 0 < z.re) :
    (z ^ 2 - 1 / 4) * linearQuotient z = linearNumerator z := by
  have hn : z + 1 / 2 ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    norm_num at he
    linarith
  have he := sub_smul_dslope_of_zero linearNumerator_half z
  rw [smul_eq_mul] at he
  dsimp only [linearQuotient]
  calc
    (z ^ 2 - 1 / 4) * (dslope linearNumerator (1 / 2) z / (z + 1 / 2)) =
        (z - 1 / 2) * dslope linearNumerator (1 / 2) z := by
          rw [show z ^ 2 - 1 / 4 = (z - 1 / 2) * (z + 1 / 2) by ring,
            mul_assoc, mul_div_cancel₀ _ hn]
    _ = _ := he

private theorem linearTail_nonnegative : ∀ᵐ t ∂linearTail, 0 ≤ t := by
  apply (ae_withDensity_iff linearDensity_continuous.measurable.ennreal_ofReal).2
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht _
  exact linearCutoff_pos.le.trans ht.le

private theorem linearVolume_moment {b : ℝ} (hb : b < 0) :
    Integrable (fun t : ℝ => Real.exp (b * t)) (volume.restrict (Ioi linearCutoff)) :=
  integrableOn_exp_mul_Ioi hb linearCutoff

private theorem linearVolume_interior {b : ℝ} (hb : b < 0) :
    b ∈ interior (integrableExpSet id (volume.restrict (Ioi linearCutoff))) := by
  apply mem_interior.mpr
  exact ⟨Iio 0, fun _ hc => linearVolume_moment hc, isOpen_Iio, hb⟩

private theorem linearPolynomial_moment {b : ℝ} (hb : b < 0) :
    Integrable (fun t : ℝ => (4 * t + 9) * Real.exp (b * t))
      (volume.restrict (Ioi linearCutoff)) := by
  have h1 := integrable_pow_mul_exp_of_mem_interior_integrableExpSet
    (linearVolume_interior hb) 1
  convert (h1.const_mul 4).add ((linearVolume_moment hb).const_mul 9) using 1
  funext t
  simp only [Pi.add_apply, pow_one, id_eq]
  ring

private theorem linearKernel_bound {t : ℝ} (ht : 0 ≤ t) :
    |linearKernel t| ≤ ((101 / 100 : ℝ) * firstLiMass) * Real.exp (t / 2) := by
  calc
    |linearKernel t| = Real.exp (-t / 2) * |(actualH t).re| := by
      rw [linearKernel, abs_mul, Real.abs_exp]
    _ ≤ Real.exp (-t / 2) * ‖actualH t‖ :=
      mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (Real.exp_nonneg _)
    _ ≤ Real.exp (-t / 2) * (((101 / 100 : ℝ) * firstLiMass) * Real.exp t) :=
      mul_le_mul_of_nonneg_left (by simpa only [max_eq_left ht] using actualH_bound t)
        (Real.exp_nonneg _)
    _ = _ := by rw [mul_left_comm, ← Real.exp_add]; congr 2; ring

private theorem linearKernel_moment {b : ℝ} (hb : b < -(1 / 2 : ℝ)) :
    Integrable (fun t : ℝ => linearKernel t * Real.exp (b * t))
      (volume.restrict (Ioi linearCutoff)) := by
  have hi := (linearVolume_moment (b := b + 1 / 2) (by linarith)).const_mul
    ((101 / 100 : ℝ) * firstLiMass)
  refine hi.mono' ((linearKernel_continuous.mul
    (by fun_prop : Continuous (fun t : ℝ => Real.exp (b * t)))).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.norm_eq_abs, abs_mul, Real.abs_exp]
  calc
    |linearKernel t| * Real.exp (b * t) ≤
        (((101 / 100 : ℝ) * firstLiMass) * Real.exp (t / 2)) * Real.exp (b * t) :=
      mul_le_mul_of_nonneg_right (linearKernel_bound (linearCutoff_pos.le.trans ht.le))
        (Real.exp_nonneg _)
    _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring

private theorem linearTail_moment
    (hdeny : ∀ t : ℝ, linearCutoff ≤ t → linearKernel t ≤ 4 * t + 9)
    {b : ℝ} (hb : b < -(1 / 2 : ℝ)) :
    Integrable (fun t : ℝ => Real.exp (b * t)) linearTail := by
  apply (integrable_withDensity_iff_integrable_smul'
    linearDensity_continuous.measurable.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)).2
  apply ((linearPolynomial_moment (by linarith : b < 0)).sub
    (linearKernel_moment hb)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  dsimp only [linearDensity, Pi.sub_apply]
  rw [ENNReal.toReal_ofReal (sub_nonneg.mpr (hdeny t ht.le)), smul_eq_mul]
  ring

private theorem linearKernel_complex (t : ℝ) :
    (linearKernel t : ℂ) = Complex.exp (-(t : ℂ) / 2) * actualH t := by
  have hi : (actualH t).im = 0 :=
    (actual_complete_H_package.2.choose_spec.2.1 t).2.1
  have he : ((actualH t).re : ℂ) = actualH t := by
    apply Complex.ext <;> simp [hi]
  rw [linearKernel, Complex.ofReal_mul, Complex.ofReal_exp, he]
  congr 2
  push_cast
  ring

private theorem linearKernel_laplace_integrable {z : ℂ} (hz : 1 / 2 < z.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-z * t) * (linearKernel t : ℂ)) (Ioi 0) := by
  have h := actualH_laplace_integrable (s := z + 1 / 2) (by
    simp only [Complex.add_re]; norm_num; linarith)
  apply h.congr
  exact ae_of_all _ fun t => by
    dsimp only
    rw [linearKernel_complex, ← mul_assoc, ← Complex.exp_add]
    congr 2
    ring

private theorem linearKernel_laplace {z : ℂ} (hz : 1 / 2 < z.re) :
    (∫ t : ℝ in Ioi 0, Complex.exp (-z * t) * (linearKernel t : ℂ)) =
      ((firstLiMass : ℂ) * z - deriv shiftedXi z / shiftedXi z) / (z ^ 2 - 1 / 4) := by
  have he : (fun t : ℝ => Complex.exp (-z * t) * (linearKernel t : ℂ)) =
      (fun t : ℝ => Complex.exp (-(z + 1 / 2) * t) * actualH t) := by
    funext t
    rw [linearKernel_complex, ← mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  rw [he, actualH_laplace (by simp only [Complex.add_re]; norm_num; linarith),
    logDeriv_apply, shiftedXi_deriv]
  change _ = ((firstLiMass : ℂ) * z - deriv xiReading (z + 1 / 2) /
    xiReading (z + 1 / 2)) / _
  congr 1 <;> ring

private def linearP (z : ℂ) : ℂ := complexMGF id linearTail (-z)
private def linearB (z : ℂ) : ℂ :=
  Complex.exp (-z * (linearCutoff : ℂ)) *
    (((4 * linearCutoff + 9 : ℝ) : ℂ) / z + 4 / z ^ 2)
private def linearC (z : ℂ) : ℂ :=
  ∫ t : ℝ in Ioc 0 linearCutoff, Complex.exp (-z * t) * (linearKernel t : ℂ)
private def linearA (z : ℂ) : ℂ := linearB z + linearC z
private def linearS : Set ℂ :=
  {z | 0 < z.re ∧ -z.re ∈ interior (integrableExpSet id linearTail)}

private theorem linearPolynomial_laplace_integrable {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun t : ℝ => ((4 * t + 9 : ℝ) : ℂ) * Complex.exp (-z * t))
      (Ioi linearCutoff) := by
  have h0 := integrable_cexp_mul_of_re_mem_interior_integrableExpSet
    (X := id) (μ := volume.restrict (Ioi linearCutoff)) (z := -z)
    (linearVolume_interior (by simpa using neg_neg_of_pos hz))
  have h1 := integrable_pow_mul_cexp_of_re_mem_interior_integrableExpSet
    (X := id) (μ := volume.restrict (Ioi linearCutoff)) (z := -z)
    (linearVolume_interior (by simpa using neg_neg_of_pos hz)) 1
  change Integrable _ (volume.restrict (Ioi linearCutoff))
  convert (h1.const_mul (4 : ℂ)).add (h0.const_mul (9 : ℂ)) using 1
  funext t
  simp only [Pi.add_apply, pow_one, id_eq]
  push_cast
  ring

private theorem linearTail_interior
    (hdeny : ∀ t : ℝ, linearCutoff ≤ t → linearKernel t ≤ 4 * t + 9)
    {b : ℝ} (hb : b < -(1 / 2 : ℝ)) :
    b ∈ interior (integrableExpSet id linearTail) := by
  apply mem_interior.mpr
  exact ⟨Iio (-(1 / 2 : ℝ)), fun _ hc => linearTail_moment hdeny hc, isOpen_Iio, hb⟩

private theorem linearVolume_laplace {z : ℂ} (hz : 0 < z.re) :
    complexMGF id (volume.restrict (Ioi linearCutoff)) (-z) =
      Complex.exp (-z * (linearCutoff : ℂ)) / z := by
  change (∫ t : ℝ in Ioi linearCutoff, Complex.exp (-z * t)) = _
  rw [integral_exp_mul_complex_Ioi (by simpa using neg_neg_of_pos hz)]
  simp only [div_neg, neg_div, neg_neg]

private theorem linearVolume_first_moment {z : ℂ} (hz : 0 < z.re) :
    (∫ t : ℝ in Ioi linearCutoff, (t : ℂ) * Complex.exp (-z * t)) =
      Complex.exp (-z * (linearCutoff : ℂ)) * ((linearCutoff : ℂ) / z + 1 / z ^ 2) := by
  have hz0 : z ≠ 0 := by intro h; subst z; simp at hz
  have hi := hasDerivAt_complexMGF (X := id) (μ := volume.restrict (Ioi linearCutoff))
    (z := -z) (linearVolume_interior (by simpa using neg_neg_of_pos hz))
  have hj : HasDerivAt
      (fun w : ℂ => complexMGF id (volume.restrict (Ioi linearCutoff)) (-w))
      (-(∫ t : ℝ in Ioi linearCutoff, (t : ℂ) * Complex.exp (-z * t))) z := by
    convert! hi.comp z (hasDerivAt_id z).neg using 1; simp
  have hnear : (fun w : ℂ => complexMGF id (volume.restrict (Ioi linearCutoff)) (-w))
      =ᶠ[𝓝 z] (fun w : ℂ => Complex.exp (-w * (linearCutoff : ℂ)) / w) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz] with w hw
    exact linearVolume_laplace hw
  have he := (hj.congr_of_eventuallyEq hnear.symm).unique
    (((hasDerivAt_id z).neg.mul_const (linearCutoff : ℂ)).cexp.div (hasDerivAt_id z) hz0)
  apply neg_injective
  rw [he]
  simp only [Pi.neg_apply, id_eq]
  field_simp [hz0]
  ring

private theorem linearPolynomial_laplace {z : ℂ} (hz : 0 < z.re) :
    (∫ t : ℝ in Ioi linearCutoff,
      ((4 * t + 9 : ℝ) : ℂ) * Complex.exp (-z * t)) = linearB z := by
  have hi := linearVolume_interior (b := -z.re) (by linarith)
  have h0 := integrable_cexp_mul_of_re_mem_interior_integrableExpSet
    (X := id) (μ := volume.restrict (Ioi linearCutoff)) (z := -z) (by simpa using hi)
  have h1 := integrable_pow_mul_cexp_of_re_mem_interior_integrableExpSet
    (X := id) (μ := volume.restrict (Ioi linearCutoff)) (z := -z) (by simpa using hi) 1
  have h1' : IntegrableOn (fun t : ℝ => (t : ℂ) * Complex.exp (-z * t)) (Ioi linearCutoff) := by
    change Integrable _ (volume.restrict (Ioi linearCutoff))
    simpa only [id_eq, pow_one] using h1
  have he : (fun t : ℝ => ((4 * t + 9 : ℝ) : ℂ) * Complex.exp (-z * t)) =
      (fun t : ℝ => (4 : ℂ) * ((t : ℂ) * Complex.exp (-z * t)) +
        9 * Complex.exp (-z * t)) := by
    funext t; push_cast; ring
  have h0' : IntegrableOn (fun t : ℝ => Complex.exp (-z * t)) (Ioi linearCutoff) := h0
  rw [he, integral_add (h1'.const_mul (4 : ℂ)) (h0'.const_mul (9 : ℂ)),
    integral_const_mul, integral_const_mul, linearVolume_first_moment hz]
  change 4 * _ + 9 * complexMGF id (volume.restrict (Ioi linearCutoff)) (-z) = _
  rw [linearVolume_laplace hz]
  dsimp only [linearB]
  push_cast
  ring

private theorem linearC_differentiable : Differentiable ℂ linearC := by
  intro z₀
  let F : ℂ → ℝ → ℂ := fun z t => Complex.exp (-z * t) * (linearKernel t : ℂ)
  let F' : ℂ → ℝ → ℂ := fun z t =>
    (-(t : ℂ) * Complex.exp (-z * t)) * (linearKernel t : ℂ)
  let bound : ℝ → ℝ := fun t =>
    linearCutoff * Real.exp ((‖z₀‖ + 1) * linearCutoff) * |linearKernel t|
  have hFc (z : ℂ) : Continuous (F z) := by
    exact (show Continuous (fun t : ℝ => Complex.exp (-z * t)) by fun_prop).mul
      (Complex.continuous_ofReal.comp linearKernel_continuous)
  have hF'c : Continuous (F' z₀) := by
    exact ((show Continuous (fun t : ℝ => -(t : ℂ)) by fun_prop).mul
      (show Continuous (fun t : ℝ => Complex.exp (-z₀ * t)) by fun_prop)).mul
      (Complex.continuous_ofReal.comp linearKernel_continuous)
  have hbound : IntegrableOn bound (Ioc 0 linearCutoff) := by
    exact ((linearKernel_continuous.abs.integrableOn_Icc).mono_set Ioc_subset_Icc_self).const_mul _
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioc 0 linearCutoff)) (F := F) (F' := F')
    (bound := bound) (Metric.ball_mem_nhds z₀ (by norm_num : (0 : ℝ) < 1))
    (Filter.Eventually.of_forall (fun z => (hFc z).aestronglyMeasurable))
    (((hFc z₀).integrableOn_Icc).mono_set Ioc_subset_Icc_self)
    hF'c.aestronglyMeasurable (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht z hz
      have hzle : ‖z‖ ≤ ‖z₀‖ + 1 :=
        norm_le_norm_add_const_of_dist_le (le_of_lt (show dist z z₀ < 1 from hz))
      have ht0 : 0 ≤ t := ht.1.le
      have he : ‖Complex.exp (-z * t)‖ ≤ Real.exp ((‖z₀‖ + 1) * linearCutoff) := by
        apply (Complex.norm_exp_le_exp_norm _).trans
        apply Real.exp_le_exp.mpr
        calc
          ‖-z * (t : ℂ)‖ = ‖z‖ * t := by simp [Complex.norm_real, abs_of_nonneg ht0]
          _ ≤ (‖z₀‖ + 1) * linearCutoff :=
            mul_le_mul hzle ht.2 ht0 (by positivity)
      dsimp only [F', bound]
      simp only [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul ht.2 he (norm_nonneg _) linearCutoff_pos.le) (abs_nonneg _)) hbound (by
      exact ae_of_all _ fun t z _ => by
        simpa only [F, F', Pi.neg_apply, id_eq, neg_mul, mul_neg, neg_one_mul,
          one_mul, mul_comm, mul_left_comm, mul_assoc] using
          (((hasDerivAt_id z).neg.mul_const (t : ℂ)).cexp.mul_const (linearKernel t : ℂ)))
  exact hd.2.differentiableAt

private theorem linearB_differentiable : DifferentiableOn ℂ linearB {z | 0 < z.re} := by
  intro z hz
  have hz0 : z ≠ 0 := by intro h; subst z; simp at hz
  have he : DifferentiableAt ℂ (fun w : ℂ => Complex.exp (-w * (linearCutoff : ℂ))) z := by
    fun_prop
  exact (he.mul (((differentiableAt_const _).div differentiableAt_id hz0).add
    ((differentiableAt_const _).div (differentiableAt_id.pow 2)
      (pow_ne_zero _ hz0)))).differentiableWithinAt

private theorem linearA_differentiable : DifferentiableOn ℂ linearA {z | 0 < z.re} :=
  linearB_differentiable.add linearC_differentiable.differentiableOn

private theorem linearTail_laplace
    (hdeny : ∀ t : ℝ, linearCutoff ≤ t → linearKernel t ≤ 4 * t + 9)
    {z : ℂ} (hz : 1 / 2 < z.re) :
    linearP z = linearA z - linearNumerator z / (z ^ 2 - 1 / 4) := by
  have hzpos : 0 < z.re := by linarith
  have hk := linearKernel_laplace_integrable hz
  have hkt : IntegrableOn (fun t : ℝ => Complex.exp (-z * t) * (linearKernel t : ℂ))
      (Ioi linearCutoff) := hk.mono_set (Ioi_subset_Ioi linearCutoff_pos.le)
  have hsplit := setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
    (hk.mono_set Ioc_subset_Ioi_self) hkt
  rw [Ioc_union_Ioi_eq_Ioi linearCutoff_pos.le, linearKernel_laplace hz] at hsplit
  have hp : linearP z = linearB z -
      ∫ t : ℝ in Ioi linearCutoff, Complex.exp (-z * t) * (linearKernel t : ℂ) := by
    change (∫ t : ℝ, Complex.exp (-z * t)
      ∂(volume.restrict (Ioi linearCutoff)).withDensity
        (fun t => ENNReal.ofReal (linearDensity t))) = _
    rw [integral_withDensity_eq_integral_toReal_smul
      linearDensity_continuous.measurable.ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    have he : (fun t : ℝ => (ENNReal.ofReal (linearDensity t)).toReal •
        Complex.exp (-z * t)) =ᵐ[volume.restrict (Ioi linearCutoff)]
        (fun t : ℝ => ((4 * t + 9 : ℝ) : ℂ) * Complex.exp (-z * t) -
          Complex.exp (-z * t) * (linearKernel t : ℂ)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      dsimp only [linearDensity]
      rw [ENNReal.toReal_ofReal (sub_nonneg.mpr (hdeny t ht.le)), Complex.real_smul]
      push_cast
      ring
    rw [integral_congr_ae he, integral_sub (linearPolynomial_laplace_integrable hzpos) hkt,
      linearPolynomial_laplace hzpos]
  rw [hp]
  dsimp only [linearA, linearC, linearNumerator]
  linear_combination hsplit

private theorem linearS_open : IsOpen linearS :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_interior.preimage Complex.continuous_re.neg)

private theorem linearS_convex : Convex ℝ linearS :=
  (convex_halfSpace_re_gt 0).inter
    ((convex_integrableExpSet (X := id) (μ := linearTail)).interior.linear_preimage
      (-Complex.reCLM.toLinearMap))

private theorem linearS_initial
    (hdeny : ∀ t : ℝ, linearCutoff ≤ t → linearKernel t ≤ 4 * t + 9)
    {z : ℂ} (hz : 1 / 2 < z.re) : z ∈ linearS :=
  ⟨by linarith, linearTail_interior hdeny (by linarith)⟩

private theorem linearP_analytic : AnalyticOnNhd ℂ linearP linearS := by
  intro z hz
  exact (analyticAt_complexMGF (X := id) (μ := linearTail) (z := -z)
    (by simpa using hz.2)).comp (analyticAt_id.neg)

private theorem linearD_ne {z : ℂ} (hz : 0 < z.re) (hc : z ≠ 1 / 2) :
    z ^ 2 - 1 / 4 ≠ 0 := by
  rw [show z ^ 2 - 1 / 4 = (z - 1 / 2) * (z + 1 / 2) by ring]
  refine mul_ne_zero (sub_ne_zero.mpr hc) ?_
  intro h
  have he := congrArg Complex.re h
  norm_num at he
  linarith

private theorem linear_cross_identity
    (hdeny : ∀ t : ℝ, linearCutoff ≤ t → linearKernel t ≤ 4 * t + 9)
    {z : ℂ} (hz : z ∈ linearS) :
    (z ^ 2 - 1 / 4) * shiftedXi z * linearP z =
      ((z ^ 2 - 1 / 4) * linearA z - (firstLiMass : ℂ) * z) * shiftedXi z +
        deriv shiftedXi z := by
  let D : ℂ → ℂ := fun z => z ^ 2 - 1 / 4
  let f : ℂ → ℂ := fun z => D z * shiftedXi z * linearP z
  let g : ℂ → ℂ := fun z =>
    (D z * linearA z - (firstLiMass : ℂ) * z) * shiftedXi z + deriv shiftedXi z
  have hD : Differentiable ℂ D := by fun_prop
  have hA := linearA_differentiable.analyticOnNhd
    (isOpen_lt continuous_const Complex.continuous_re)
  have hf : AnalyticOnNhd ℂ f linearS := fun z hz =>
    ((hD.analyticAt z).mul (shiftedXi_differentiable.analyticAt z)).mul (linearP_analytic z hz)
  have hg : AnalyticOnNhd ℂ g linearS := fun z hz =>
    ((((hD.analyticAt z).mul (hA z hz.1)).sub (analyticAt_const.mul analyticAt_id)).mul
      (shiftedXi_differentiable.analyticAt z)).add (shiftedXi_differentiable.analyticAt z).deriv
  have hnear : f =ᶠ[𝓝 (1 : ℂ)] g := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (1 / 2 : ℝ) < (1 : ℂ).re by norm_num)] with w hw
    have hwpos : 0 < w.re := by linarith
    have hwc : w ≠ 1 / 2 := by intro h; rw [h] at hw; norm_num at hw
    have hD0 := linearD_ne hwpos hwc
    have hX0 : shiftedXi w ≠ 0 := xiReading_ne_zero_right (by
      change 1 < (w + 1 / 2).re
      norm_num
      linarith)
    dsimp only [f, g, D]
    calc
      (w ^ 2 - 1 / 4) * shiftedXi w * linearP w =
          shiftedXi w * ((w ^ 2 - 1 / 4) * linearP w) := by ring
      _ = shiftedXi w * ((w ^ 2 - 1 / 4) * linearA w - linearNumerator w) := by
        rw [linearTail_laplace hdeny hw, mul_sub, mul_div_cancel₀ _ hD0]
      _ = _ := by
        dsimp only [linearNumerator]
        rw [mul_sub, mul_sub, mul_div_cancel₀ _ hX0]
        ring
  exact analytic_continuation_unique hf hg linearS_convex.isPreconnected
    (linearS_initial hdeny (z := 1) (by norm_num)) hnear hz

private theorem linear_germ
    (hdeny : ∀ t : ℝ, linearCutoff ≤ t → linearKernel t ≤ 4 * t + 9)
    {z : ℂ} (hz : z ∈ linearS ∩ linearU) :
    linearP =ᶠ[𝓝 z] (fun w => linearA w - linearQuotient w) := by
  have hU : IsOpen (linearS ∩ linearU) := linearS_open.inter linearU_open
  have hA := linearA_differentiable.analyticOnNhd
    (isOpen_lt continuous_const Complex.continuous_re)
  have hQ := linearQuotient_differentiable.analyticOnNhd linearU_open
  have heq : ∀ w ∈ linearS ∩ linearU, w ≠ 1 / 2 →
      linearP w = linearA w - linearQuotient w := by
    intro w hw hwc
    have hc := linear_cross_identity hdeny hw.1
    have hq := linearQuotient_identity hw.1.1
    have hD0 := linearD_ne hw.1.1 hwc
    have hX0 := hw.2.2
    have hn : (linearNumerator w) * shiftedXi w =
        (firstLiMass : ℂ) * w * shiftedXi w - deriv shiftedXi w := by
      dsimp only [linearNumerator]
      rw [sub_mul, div_mul_cancel₀ _ hX0]
    apply mul_left_cancel₀ hD0
    apply mul_left_cancel₀ hX0
    rw [mul_sub, mul_sub]
    calc
      shiftedXi w * ((w ^ 2 - 1 / 4) * linearP w) =
          ((w ^ 2 - 1 / 4) * linearA w - (firstLiMass : ℂ) * w) * shiftedXi w +
            deriv shiftedXi w := by linear_combination hc
      _ = shiftedXi w * ((w ^ 2 - 1 / 4) * linearA w) -
          shiftedXi w * ((w ^ 2 - 1 / 4) * linearQuotient w) := by
        rw [hq]
        linear_combination hn
  have hevery : ∀ w ∈ linearS ∩ linearU, linearP w = linearA w - linearQuotient w := by
    intro w hw
    by_cases hwc : w = 1 / 2
    · subst w
      have hloc : linearP =ᶠ[𝓝 (1 / 2 : ℂ)] (fun v => linearA v - linearQuotient v) := by
        apply ((linearP_analytic _ hw.1).frequently_eq_iff_eventually_eq
          ((hA _ hw.1.1).sub (hQ _ hw.2))).mp
        apply Filter.Eventually.frequently
        have hdom : ∀ᶠ v in 𝓝 (1 / 2 : ℂ), v ∈ linearS ∩ linearU := hU.mem_nhds hw
        filter_upwards [hdom.filter_mono nhdsWithin_le_nhds,
          self_mem_nhdsWithin] with v hv hvc
        exact heq v hv hvc
      exact hloc.eq_of_nhds
    · exact heq w hw hwc
  filter_upwards [hU.mem_nhds hz] with w hw
  exact hevery w hw

private theorem linear_tail_denial_implies_rh
    (hdeny : ∀ t : ℝ, linearCutoff ≤ t → linearKernel t ≤ 4 * t + 9) :
    RiemannHypothesis := by
  let Uminus : Set ℂ := {w | -w ∈ linearU}
  let E : ℂ → ℂ := fun w => linearA (-w) - linearQuotient (-w)
  have hopen : IsOpen Uminus := linearU_open.preimage continuous_neg
  have hreal (t : ℝ) (ht : t < 0) : (t : ℂ) ∈ Uminus := by
    change -(t : ℂ) ∈ linearU
    have h := linearU_real (-t) (by linarith)
    simpa only [Complex.ofReal_neg] using h
  have hE : DifferentiableOn ℂ E Uminus := by
    intro w hw
    have ha := linearA_differentiable.differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hw.1)
    have hq := linearQuotient_differentiable.differentiableAt (linearU_open.mem_nhds hw)
    exact ((ha.sub hq).comp w differentiableAt_id.neg).differentiableWithinAt
  have hm : ∀ t : ℝ, t < 0 → Integrable (fun x : ℝ => Real.exp (t * x)) linearTail := by
    apply D5.S3.Analytic.Laplace.NonnegativeBoundary.integrable_exp_on_real_ray
      linearTail_nonnegative hopen hreal hE
      (show (integrableExpSet id linearTail).Nonempty from
        ⟨-1, linearTail_moment hdeny (by norm_num)⟩)
    intro t ht hti
    have hsu : -(t : ℂ) ∈ linearS ∩ linearU := by
      refine ⟨⟨?_, ?_⟩, hreal t ht⟩
      · simp only [Complex.neg_re, Complex.ofReal_re]; linarith
      · simpa only [Complex.neg_re, Complex.ofReal_re, neg_neg] using hti
    have heq := (linear_germ hdeny hsu).comp_tendsto
      ((continuous_neg : Continuous (fun w : ℂ => -w)).tendsto (t : ℂ))
    filter_upwards [heq] with w hw
    dsimp only [Function.comp_def, linearP] at hw
    simpa only [E, neg_neg] using hw.symm
  have hsall {z : ℂ} (hz : 0 < z.re) : z ∈ linearS := by
    refine ⟨hz, mem_interior.mpr ?_⟩
    exact ⟨Iio 0, fun t ht => hm t ht, isOpen_Iio,
      show -z.re < 0 from neg_neg_of_pos hz⟩
  let G : ℂ → ℂ := fun z =>
    (z ^ 2 - 1 / 4) * (linearP z - linearA z) + (firstLiMass : ℂ) * z
  have hP : AnalyticOnNhd ℂ linearP {z | 0 < z.re} := fun z hz =>
    linearP_analytic z (hsall hz)
  have hA := linearA_differentiable.analyticOnNhd
    (isOpen_lt continuous_const Complex.continuous_re)
  have hG : AnalyticOnNhd ℂ G {z | 0 < z.re} := by
    intro z hz
    exact (((analyticAt_id.pow 2).sub analyticAt_const).mul
      ((hP z hz).sub (hA z hz))).add (analyticAt_const.mul analyticAt_id)
  have hode : ∀ z ∈ {z : ℂ | 0 < z.re}, deriv shiftedXi z = G z * shiftedXi z := by
    intro z hz
    have hc := linear_cross_identity hdeny (hsall hz)
    dsimp only [G]
    linear_combination -hc
  have hfree := D5.S3.Weil.Probability.AnalyticLogarithmicContinuation.analytic_linear_ode_zero_free
    (isOpen_lt continuous_const Complex.continuous_re) (convex_halfSpace_re_gt 0).isPreconnected
    (fun z _ => shiftedXi_differentiable.analyticAt z) hG
    (p := (1 / 2 : ℂ)) (by norm_num)
    (by rw [shiftedXi_half]; norm_num) hode
  apply D5.S3.Weil.ZetaBridge.RightHalfStripRiemannReduction.golden_right_half_strip_implies_rh
  intro rho hzero hright hone
  have hw : 0 < (rho - (1 / 2 : ℂ)).re := by
    simp only [Complex.sub_re]; norm_num; linarith
  have hx : xiReading rho = 0 := (xiReading_eq_zero_iff_nontrivial rho).mpr
    ⟨hzero, by linarith, hone⟩
  exact hfree (rho - 1 / 2) hw (by
    simpa only [shiftedXi, sub_add_cancel] using hx)

/-- If RH fails, the literal complete arithmetic kernel exceeds the linear
majorant at some logarithmic argument at least `log 10000`. -/
theorem actual_linear_peak_of_not_rh (hnot : ¬ RiemannHypothesis) :
    ∃ y : ℝ, Real.log 10000 ≤ y ∧ 4 * y + 9 <
      Real.exp (-y / 2) * (D5.S3.Arith.Robin.CompleteMertensPeak.U (Real.exp y) -
        Real.log (2 * Real.pi) + trivialT y) := by
  by_contra hnone
  push Not at hnone
  apply hnot
  apply linear_tail_denial_implies_rh
  intro t ht
  rw [linearKernel_arithmetic (linearCutoff_pos.trans_le ht)]
  exact hnone t ht

#print axioms actual_linear_peak_of_not_rh

end D5.S3.Weil.Mertens.IntegratedExplicit
end
