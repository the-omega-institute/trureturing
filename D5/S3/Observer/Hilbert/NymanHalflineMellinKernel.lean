/- GID: D5/S3/Observer/Hilbert/NymanHalflineMellinKernel
   generality: G
   mirror-B: D5/B/S3/Observer/Hilbert/NymanHalflineMellinKernel
   mirror-E: none(waiver:unbounded-analytic-construction)
   anchors: []
   utility: none
   digest: Conjugated Mellin kernel on the positive half-line. -/

import D5.S3.Observer.Hilbert.NymanBeurlingFiniteGramDistance
import Mathlib.Analysis.InnerProductSpace.LinearMap

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Observer.Hilbert.NymanHalflineMellinKernel

open Set MeasureTheory
open D5.S3.Observer.Hilbert.NymanBeurlingFiniteGramDistance
open D5.S3.Constants.InnerProducts.FractionalReciprocalInnerProduct

/-- Every real source has a reciprocal tail beyond one. -/
theorem realSourceVector_tail (a : ℝ) (ha : 1 ≤ a) {x : ℝ} (hx : 1 < x) :
    Int.fract (1 / (a * x)) = 1 / (a * x) := by
  apply Int.fract_eq_self.mpr
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hx0 : 0 < x := zero_lt_one.trans hx
  constructor
  · positivity
  · have hax : 1 < a * x := lt_of_lt_of_le hx (le_mul_of_one_le_left hx0.le ha)
    exact (div_lt_one (by positivity)).mpr hax

private theorem real_source_memLp (a : ℝ) (ha : 1 ≤ a) :
    MemLp (fun x : ℝ => Int.fract (1 / (a * x))) 2 positiveMeasure := by
  have hm : Measurable (fun x : ℝ => Int.fract (1 / (a * x))) :=
    (measurable_const.div (measurable_const.mul measurable_id)).fract
  apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable.restrict).2
  change IntegrableOn (fun x : ℝ => Int.fract (1 / (a * x)) ^ 2) (Ioi 0)
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num), integrableOn_union]
  constructor
  · apply Measure.integrableOn_of_bounded (M := 1) measure_Ioc_lt_top.ne
      (hm.pow_const 2).aestronglyMeasurable
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [Int.fract_nonneg (1 / (a * x)), Int.fract_lt_one (1 / (a * x))]
  · have hp : IntegrableOn (fun x : ℝ => x ^ (-2 : ℝ)) (Ioi (1 : ℝ)) :=
      integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one
    have hscaled : IntegrableOn (fun x : ℝ => (1 / a ^ 2) * x ^ (-2 : ℝ)) (Ioi 1) :=
      hp.const_mul _
    refine hscaled.congr_fun ?_ measurableSet_Ioi
    intro x hx
    change (1 / a ^ 2) * x ^ (-2 : ℝ) = Int.fract (1 / (a * x)) ^ 2
    rw [realSourceVector_tail a ha hx, Real.rpow_neg (le_of_lt (zero_lt_one.trans hx)),
      Real.rpow_two]
    simp [mul_pow, div_eq_mul_inv, mul_comm]

/-- The real-parameter fractional function as a vector in the existing complex carrier. -/
def realSourceVector (a : ℝ) (ha : 1 ≤ a) : Carrier :=
  (Complex.ofRealCLM.comp_memLp' (real_source_memLp a ha)).toLp
    (fun x : ℝ => ((Int.fract (1 / (a * x)) : ℝ) : ℂ))

/-- The Lp quotient retains the literal fractional-part representative. -/
theorem realSourceVector_coe_ae (a : ℝ) (ha : 1 ≤ a) :
    (realSourceVector a ha : ℝ → ℂ) =ᵐ[positiveMeasure]
      fun x : ℝ => ((Int.fract (1 / (a * x)) : ℝ) : ℂ) :=
  MemLp.coeFn_toLp _

/-- At natural parameters this is the already existing source vector. -/
theorem realSourceVector_nat (n : ℕ) (hn : 1 ≤ n) :
    realSourceVector (n : ℝ) (by exact_mod_cast hn) = sourceVector n hn := by
  apply Lp.ext
  exact (realSourceVector_coe_ae _ _).trans (sourceVector_coe_ae n hn).symm

private def leftFn (rho : ℂ) : ℝ → ℂ :=
  (Ioo (0 : ℝ) 1).indicator (fun x => star ((x : ℂ) ^ (rho - 1)))

private def rightFn (rho : ℂ) : ℝ → ℂ :=
  (Ioi (1 : ℝ)).indicator (fun x => star ((rho - 1)⁻¹) / (x : ℂ))

private theorem left_memLp (rho : ℂ) (hb : 1 / 2 < rho.re) :
    MemLp (leftFn rho) 2 positiveMeasure := by
  rw [leftFn, memLp_indicator_iff_restrict measurableSet_Ioo, positiveMeasure,
    Measure.restrict_restrict measurableSet_Ioo, inter_eq_left.mpr Ioo_subset_Ioi_self]
  have hi : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (rho - 1)) (Ioo 0 1) :=
    ((intervalIntegral.intervalIntegrable_cpow' (by simp; linarith) :
      IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ (rho - 1)) volume 0 1).1).mono_set
        Ioo_subset_Ioc_self
  apply (memLp_two_iff_integrable_sq_norm hi.aestronglyMeasurable.star).2
  have hp : IntegrableOn (fun x : ℝ => x ^ (2 * rho.re - 2)) (Ioo 0 1) :=
    ((intervalIntegral.intervalIntegrable_rpow' (by linarith) :
      IntervalIntegrable (fun x : ℝ => x ^ (2 * rho.re - 2)) volume 0 1).1).mono_set
        Ioo_subset_Ioc_self
  refine hp.congr_fun ?_ measurableSet_Ioo
  intro x hx
  dsimp
  rw [Complex.norm_conj, Complex.norm_cpow_eq_rpow_re_of_pos hx.1,
    ← Real.rpow_mul_natCast hx.1.le]
  congr 1
  simp
  ring

private theorem right_memLp (rho : ℂ) : MemLp (rightFn rho) 2 positiveMeasure := by
  rw [rightFn, memLp_indicator_iff_restrict measurableSet_Ioi, positiveMeasure,
    Measure.restrict_restrict measurableSet_Ioi,
    inter_eq_left.mpr (Ioi_subset_Ioi (show (0 : ℝ) ≤ 1 by norm_num))]
  have hm : Measurable (fun x : ℝ => star ((rho - 1)⁻¹) / (x : ℂ)) := by fun_prop
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).2
  have hp : IntegrableOn (fun x : ℝ => ‖rho - 1‖⁻¹ ^ 2 * x ^ (-2 : ℝ)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one).const_mul _
  refine hp.congr_fun ?_ measurableSet_Ioi
  intro x hx
  dsimp
  rw [norm_div, Complex.norm_conj, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (zero_lt_one.trans hx), Real.rpow_neg (zero_lt_one.trans hx).le,
    Real.rpow_two]
  simp [div_eq_mul_inv, mul_pow]

/-- The two disjoint pieces, conjugated for the first argument of the inner product. -/
def halflineKernel (rho : ℂ) (hb : 1 / 2 < rho.re) (_h1 : rho ≠ 1) : Carrier :=
  ((left_memLp rho hb).sub (right_memLp rho)).toLp (fun x => leftFn rho x - rightFn rho x)

/-- The kernel has the displayed representative on the actual half-line measure. -/
theorem halflineKernel_coe_ae (rho : ℂ) (hb : 1 / 2 < rho.re) (h1 : rho ≠ 1) :
    (halflineKernel rho hb h1 : ℝ → ℂ) =ᵐ[positiveMeasure] fun x =>
      (Ioo (0 : ℝ) 1).indicator (fun x => star ((x : ℂ) ^ (rho - 1))) x -
      (Ioi (1 : ℝ)).indicator (fun x => star ((rho - 1)⁻¹) / (x : ℂ)) x :=
  MemLp.coeFn_toLp _

/-- The complex-linear continuous functional represented by the conjugated kernel. -/
def halflineFunctional (rho : ℂ) (hb : 1 / 2 < rho.re) (h1 : rho ≠ 1) : Carrier →L[ℂ] ℂ :=
  innerSL ℂ (halflineKernel rho hb h1)

private theorem kernel_energy_pointwise (rho : ℂ) (x : ℝ) :
    ‖leftFn rho x - rightFn rho x‖ ^ 2 = ‖leftFn rho x‖ ^ 2 + ‖rightFn rho x‖ ^ 2 := by
  by_cases hl : x ∈ Ioo (0 : ℝ) 1
  · have hr : x ∉ Ioi (1 : ℝ) := by intro hr; exact (lt_asymm hl.2 hr)
    simp [leftFn, rightFn, hl, hr]
  · simp [leftFn, hl]

private theorem norm_sq_integral (f : Carrier) :
    ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂positiveMeasure := by
  rw [@norm_sq_eq_re_inner ℂ, L2.inner_def, ← integral_re (L2.integrable_inner f f)]
  congr 1
  funext x
  exact inner_self_eq_norm_sq (𝕜 := ℂ) (f x)

private theorem left_energy (rho : ℂ) (hb : 1 / 2 < rho.re) :
    (∫ x, ‖leftFn rho x‖ ^ 2 ∂positiveMeasure) = 1 / (2 * rho.re - 1) := by
  have heq : (fun x => ‖leftFn rho x‖ ^ 2) =
      (Ioo (0 : ℝ) 1).indicator (fun x => x ^ (2 * rho.re - 2)) := by
    funext x
    by_cases hx : x ∈ Ioo (0 : ℝ) 1
    · simp only [leftFn, indicator_of_mem hx, norm_star,
        Complex.norm_cpow_eq_rpow_re_of_pos hx.1]
      rw [← Real.rpow_mul_natCast hx.1.le]
      congr 1
      simp
      ring
    · simp [leftFn, hx]
  rw [heq, integral_indicator measurableSet_Ioo, positiveMeasure,
    Measure.restrict_restrict measurableSet_Ioo, inter_eq_left.mpr Ioo_subset_Ioi_self,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    integral_rpow (Or.inl (by linarith))]
  rw [Real.zero_rpow (by linarith : 2 * rho.re - 2 + 1 ≠ 0)]
  simp only [Real.one_rpow, sub_zero]
  congr 1
  ring

private theorem right_energy (rho : ℂ) :
    (∫ x, ‖rightFn rho x‖ ^ 2 ∂positiveMeasure) = 1 / ‖rho - 1‖ ^ 2 := by
  have heq : (fun x => ‖rightFn rho x‖ ^ 2) =
      (Ioi (1 : ℝ)).indicator (fun x => ‖rho - 1‖⁻¹ ^ 2 * x ^ (-2 : ℝ)) := by
    funext x
    by_cases hx : x ∈ Ioi (1 : ℝ)
    · have hx0 : 0 < x := zero_lt_one.trans (show 1 < x from hx)
      simp only [rightFn, indicator_of_mem hx, norm_div, norm_star, norm_inv,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
      rw [Real.rpow_neg hx0.le, Real.rpow_two]
      simp [div_eq_mul_inv, mul_pow]
    · simp [rightFn, hx]
  rw [heq, integral_indicator measurableSet_Ioi, positiveMeasure,
    Measure.restrict_restrict measurableSet_Ioi,
    inter_eq_left.mpr (Ioi_subset_Ioi (show (0 : ℝ) ≤ 1 by norm_num)), integral_const_mul,
    integral_Ioi_rpow_of_lt (by norm_num) zero_lt_one]
  norm_num [inv_pow, one_div]

/-- The exact energy is the sum of the two disjoint-support power integrals. -/
theorem halflineKernel_norm_sq (rho : ℂ) (hb : 1 / 2 < rho.re) (h1 : rho ≠ 1) :
    ‖halflineKernel rho hb h1‖ ^ 2 = 1 / (2 * rho.re - 1) + 1 / ‖rho - 1‖ ^ 2 := by
  rw [norm_sq_integral]
  have heq : (fun x => ‖halflineKernel rho hb h1 x‖ ^ 2) =ᵐ[positiveMeasure]
      fun x => ‖leftFn rho x‖ ^ 2 + ‖rightFn rho x‖ ^ 2 := by
    filter_upwards [halflineKernel_coe_ae rho hb h1] with x hx
    rw [hx]
    exact kernel_energy_pointwise rho x
  rw [integral_congr_ae heq, integral_add
    ((memLp_two_iff_integrable_sq_norm (left_memLp rho hb).1).1 (left_memLp rho hb))
    ((memLp_two_iff_integrable_sq_norm (right_memLp rho).1).1 (right_memLp rho)),
    left_energy rho hb, right_energy rho]

/-- The dual isometry preserves the exact kernel energy. -/
theorem halflineFunctional_norm_sq (rho : ℂ) (hb : 1 / 2 < rho.re) (h1 : rho ≠ 1) :
    ‖halflineFunctional rho hb h1‖ ^ 2 = 1 / (2 * rho.re - 1) + 1 / ‖rho - 1‖ ^ 2 := by
  rw [halflineFunctional, innerSL_apply_norm, halflineKernel_norm_sq]

private theorem pair_integrable (k : ℝ → ℂ) (hk : MemLp k 2 positiveMeasure)
    (f : Carrier) (g : ℝ → ℂ) (hg : g =ᵐ[positiveMeasure] f) :
    Integrable (fun x => inner ℂ (k x) (g x)) positiveMeasure := by
  refine (L2.integrable_inner (𝕜 := ℂ) (hk.toLp k) f).congr ?_
  filter_upwards [hk.coeFn_toLp, hg] with x hx hgx
  rw [hx, hgx]

private theorem left_pair (rho : ℂ) (g : ℝ → ℂ) :
    (fun x => inner ℂ (leftFn rho x) (g x)) =
      (Ioo (0 : ℝ) 1).indicator (fun x => g x * (x : ℂ) ^ (rho - 1)) := by
  funext x
  by_cases hx : x ∈ Ioo (0 : ℝ) 1
  · simp [leftFn, hx, RCLike.inner_apply]
  · simp [leftFn, hx]

private theorem right_pair (rho : ℂ) (g : ℝ → ℂ) :
    (fun x => inner ℂ (rightFn rho x) (g x)) =
      (Ioi (1 : ℝ)).indicator (fun x => (rho - 1)⁻¹ * (g x / (x : ℂ))) := by
  funext x
  by_cases hx : x ∈ Ioi (1 : ℝ)
  · simp [rightFn, hx, RCLike.inner_apply, div_eq_mul_inv, mul_comm, mul_assoc]
  · simp [rightFn, hx]

/-- Every representative of an Lp class gives the same two convergent integrals. -/
theorem halflineFunctional_integral (rho : ℂ) (hb : 1 / 2 < rho.re) (h1 : rho ≠ 1)
    (f : Carrier) (g : ℝ → ℂ) (hg : g =ᵐ[positiveMeasure] f) :
    IntegrableOn (fun x => g x * (x : ℂ) ^ (rho - 1)) (Ioo (0 : ℝ) 1) ∧
    IntegrableOn (fun x => g x / (x : ℂ)) (Ioi (1 : ℝ)) ∧
    halflineFunctional rho hb h1 f =
      (∫ x in Ioo (0 : ℝ) 1, g x * (x : ℂ) ^ (rho - 1)) -
      (rho - 1)⁻¹ * ∫ x in Ioi (1 : ℝ), g x / (x : ℂ) := by
  have hl := pair_integrable _ (left_memLp rho hb) f g hg
  have hr := pair_integrable _ (right_memLp rho) f g hg
  have hl' := hl
  have hr' := hr
  rw [left_pair, integrable_indicator_iff measurableSet_Ioo, IntegrableOn, positiveMeasure,
    Measure.restrict_restrict measurableSet_Ioo, inter_eq_left.mpr Ioo_subset_Ioi_self] at hl'
  rw [right_pair, integrable_indicator_iff measurableSet_Ioi, IntegrableOn, positiveMeasure,
    Measure.restrict_restrict measurableSet_Ioi,
    inter_eq_left.mpr (Ioi_subset_Ioi (show (0 : ℝ) ≤ 1 by norm_num))] at hr'
  have ht : IntegrableOn (fun x => g x / (x : ℂ)) (Ioi (1 : ℝ)) := by
    simpa only [IntegrableOn, ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr h1), one_mul] using
      hr'.const_mul (rho - 1)
  refine ⟨hl', ht, ?_⟩
  change inner ℂ (halflineKernel rho hb h1) f = _
  rw [L2.inner_def]
  have heq : (fun x => inner ℂ (halflineKernel rho hb h1 x) (f x)) =ᵐ[positiveMeasure]
      fun x => inner ℂ (leftFn rho x) (g x) - inner ℂ (rightFn rho x) (g x) := by
    filter_upwards [halflineKernel_coe_ae rho hb h1, hg] with x hx hgx
    rw [hx, ← hgx]
    exact inner_sub_left _ _ _
  rw [integral_congr_ae heq, integral_sub hl hr, left_pair, right_pair,
    integral_indicator measurableSet_Ioo, integral_indicator measurableSet_Ioi, positiveMeasure,
    Measure.restrict_restrict measurableSet_Ioo, inter_eq_left.mpr Ioo_subset_Ioi_self,
    Measure.restrict_restrict measurableSet_Ioi,
    inter_eq_left.mpr (Ioi_subset_Ioi (show (0 : ℝ) ≤ 1 by norm_num)), integral_const_mul]

#print axioms realSourceVector
#print axioms realSourceVector_coe_ae
#print axioms realSourceVector_nat
#print axioms realSourceVector_tail
#print axioms halflineKernel
#print axioms halflineKernel_coe_ae
#print axioms halflineKernel_norm_sq
#print axioms halflineFunctional
#print axioms halflineFunctional_norm_sq
#print axioms halflineFunctional_integral

end D5.S3.Observer.Hilbert.NymanHalflineMellinKernel
