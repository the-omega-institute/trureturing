/- GID: D5/S3/Analytic/Fourier/PositiveDefinite/SecondDifference
   generality: I
   mirror-B: D5/B/S3/Analytic/Fourier/PositiveDefinite/SecondDifference
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Integrals.Basic, mathlib/module/Mathlib.Analysis.Calculus.LHopital, mathlib/module/Mathlib.Analysis.Calculus.IteratedDeriv.Defs, mathlib/module/Mathlib.Data.Matrix.ColumnRowPartitioned, mathlib/module/Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus]
   utility: none
   digest: Second differences and quadratic deficits of smooth even positive definite functions. -/

import D5.S3.Analytic.Fourier.PositiveDefinite.Closure
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Finite difference Gram tests followed by the fundamental theorem of calculus. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open Matrix Filter MeasureTheory Set
open scoped BigOperators Topology ComplexOrder
open D5.S3.Weil.ZetaLinear.FiniteInversePoissonCriterion

namespace D5.S3.Analytic.Fourier.PositiveDefinite.SecondDifference

/-- Translation differences give positive semidefinite kernels. -/
theorem difference {f : ℝ → ℂ} (hf : PositiveDefinite f) (h : ℝ) :
    PositiveDefinite (fun t => 2 * f t - f (t + h) - f (t - h)) := by
  intro m x
  let y : Fin m ⊕ Fin m → ℝ := Sum.elim x (fun i => x i + h)
  let e := Fintype.equivFin (Fin m ⊕ Fin m)
  have H := (hf _ (y ∘ e.symm)).submatrix e
  have he : (fun i j => f (y j - y i)) =
      Matrix.fromBlocks (fun i j => f (x j - x i))
        (fun i j => f (x j - x i + h))
        (fun i j => f (x j - x i - h)) (fun i j => f (x j - x i)) := by
    ext (i | i) (j | j) <;> dsimp [y, Matrix.fromBlocks] <;> congr 1 <;> ring
  have H' : Matrix.PosSemidef (fun i j => f (y j - y i)) := by
    have hM : Matrix.submatrix (fun i j => f (y (e.symm j) - y (e.symm i))) e e =
        (fun i j => f (y j - y i)) := by
      funext i j
      change f (y (e.symm (e j)) - y (e.symm (e i))) = _
      simp only [Equiv.symm_apply_apply]
    change Matrix.PosSemidef
      (Matrix.submatrix (fun i j => f (y (e.symm j) - y (e.symm i))) e e) at H
    rw [hM] at H
    exact H
  rw [he] at H'
  let B : Matrix (Fin m ⊕ Fin m) (Fin m) ℂ := Matrix.fromRows 1 (-1)
  have HB := H'.conjTranspose_mul_mul_same B
  simp only [B, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
    Matrix.conjTranspose_one, Matrix.conjTranspose_neg, Matrix.fromCols_mul_fromBlocks,
    Matrix.fromCols_mul_fromRows, Matrix.one_mul, Matrix.neg_mul, Matrix.mul_one,
    Matrix.mul_neg, neg_neg] at HB
  have hh : (fun i j => 2 * f (x j - x i) - f (x j - x i + h) - f (x j - x i - h)) =
      ((fun i j => f (x j - x i)) + -(fun i j => f (x j - x i - h))) +
      -((fun i j => f (x j - x i + h)) + -(fun i j => f (x j - x i))) := by
    ext i j
    change 2 * f (x j - x i) - f (x j - x i + h) - f (x j - x i - h) =
      (f (x j - x i) + -f (x j - x i - h)) +
        -(f (x j - x i + h) + -f (x j - x i))
    ring
  rw [hh]
  exact HB

private theorem difference_limit {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (t : ℝ) :
    Tendsto (fun h => (2 * g t - g (t + h) - g (t - h)) / h ^ 2)
      (𝓝[≠] 0) (𝓝 (-deriv (deriv g) t)) := by
  have hc := hg.continuous
  have hd := hg.differentiable (by norm_num)
  have hd' := hg.differentiable_deriv_two
  have hc' := hg.continuous_deriv (by norm_num)
  have hc'' : Continuous (deriv (deriv g)) :=
    (hg.deriv' : ContDiff ℝ 1 (deriv g)).continuous_deriv (by norm_num)
  have L : Tendsto (fun h => (-deriv g (t + h) + deriv g (t - h)) / (2 * h))
      (𝓝[≠] 0) (𝓝 (-deriv (deriv g) t)) := by
    apply HasDerivAt.lhopital_zero_nhdsNE
      (f' := fun h => -deriv (deriv g) (t + h) - deriv (deriv g) (t - h))
      (g' := fun _ => 2)
    · exact Eventually.of_forall fun h => by
        convert ((hd' (t + h)).hasDerivAt.comp h ((hasDerivAt_id h).const_add t)).neg.add
          ((hd' (t - h)).hasDerivAt.comp h ((hasDerivAt_id h).const_sub t)) using 1 <;> (try funext z) <;> (try dsimp [Function.comp_def]) <;> ring
    · exact Eventually.of_forall fun h => by simpa using (hasDerivAt_id h).const_mul 2
    · exact Eventually.of_forall fun _ => by norm_num
    · have H : ContinuousAt (fun h => -deriv g (t + h) + deriv g (t - h)) 0 := by fun_prop
      simpa [show 2 * g t - g t - g t = 0 by ring] using H.tendsto.mono_left nhdsWithin_le_nhds
    · have HH : ContinuousAt (fun h : ℝ => 2 * h) 0 := by fun_prop
      simpa only [mul_zero] using HH.tendsto.mono_left nhdsWithin_le_nhds
    · have H : ContinuousAt (fun h =>
          (-deriv (deriv g) (t + h) - deriv (deriv g) (t - h)) / 2) 0 := by fun_prop
      convert H.tendsto.mono_left nhdsWithin_le_nhds using 1 <;> simp <;> ring
  apply HasDerivAt.lhopital_zero_nhdsNE
    (f' := fun h => -deriv g (t + h) + deriv g (t - h)) (g' := fun h => 2 * h)
  · exact Eventually.of_forall fun h => by
      convert ((hasDerivAt_const h (2 * g t)).sub
        ((hd (t + h)).hasDerivAt.comp h ((hasDerivAt_id h).const_add t))).sub
        ((hd (t - h)).hasDerivAt.comp h ((hasDerivAt_id h).const_sub t)) using 1 <;> (try funext z) <;> (try dsimp [Function.comp_def]) <;> ring
  · exact Eventually.of_forall fun h => by convert (hasDerivAt_id h).pow 2 using 1 <;> (try funext z) <;> (try dsimp [Function.comp_def]) <;> ring
  · filter_upwards [self_mem_nhdsWithin] with h hh
    exact mul_ne_zero (by norm_num) (by simpa using hh)
  · have H : ContinuousAt (fun h => 2 * g t - g (t + h) - g (t - h)) 0 := by fun_prop
    simpa [show 2 * g t - g t - g t = 0 by ring] using H.tendsto.mono_left nhdsWithin_le_nhds
  · have HH : ContinuousAt (fun h : ℝ => h ^ 2) 0 := by fun_prop
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
      HH.tendsto.mono_left nhdsWithin_le_nhds
  · exact L

/-- The negative second derivative of a twice continuously differentiable PD function is PD. -/
theorem neg_second_deriv {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    (hp : PositiveDefinite (fun t => (g t : ℂ))) :
    PositiveDefinite (fun t => (-(iteratedDeriv 2 g t) : ℂ)) := by
  apply Closure.limit (l := 𝓝[≠] (0 : ℝ))
    (f := fun h t => ((h ^ 2)⁻¹ : ℂ) * (2 * (g t : ℂ) - g (t + h) - g (t - h)))
  · intro h
    simpa using Closure.smul (difference hp h) (inv_nonneg.mpr (sq_nonneg h))
  · intro t
    have H := Complex.continuous_ofReal.continuousAt.tendsto.comp (difference_limit hg t)
    convert H using 1
    · funext h
      dsimp [Function.comp_def]
      push_cast
      ring
    · simp [iteratedDeriv_succ, iteratedDeriv_zero]

/-- The continuously extended quadratic deficit. -/
def Q (g : ℝ → ℝ) (t : ℝ) : ℝ :=
  if t = 0 then -(iteratedDeriv 2 g 0) / 2 else (g 0 - g t) / t ^ 2

private theorem even_deriv_zero {g : ℝ → ℝ} (he : Function.Even g)
    (hd : DifferentiableAt ℝ g 0) : deriv g 0 = 0 := by
  have H := (by simpa only [neg_zero] using hd.hasDerivAt :
    HasDerivAt g (deriv g 0) (-(0 : ℝ))).comp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))
  have hfun : (fun x => g (-x)) = g := funext he
  have H' : HasDerivAt g (-deriv g 0) 0 := by
    simpa only [neg_zero, Function.comp_def, hfun, mul_neg_one] using H
  linarith [H'.unique hd.hasDerivAt]

/-- The quadratic deficit is a nonnegative weighted average of dilated negative curvature. -/
theorem Q_integral {g : ℝ → ℝ} (he : Function.Even g) (hg : ContDiff ℝ 2 g) (t : ℝ) :
    Q g t = ∫ u in (0 : ℝ)..1, (1 - u) * (-iteratedDeriv 2 g (u * t)) := by
  have hc := hg.continuous
  have hd := hg.differentiable (by norm_num)
  have hd' := hg.differentiable_deriv_two
  have hc'' : Continuous (deriv (deriv g)) :=
    (hg.deriv' : ContDiff ℝ 1 (deriv g)).continuous_deriv (by norm_num)
  have hz := even_deriv_zero he (hd 0)
  by_cases ht : t = 0
  · subst t
    simp only [Q, ite_true, mul_zero, iteratedDeriv_succ, iteratedDeriv_zero]
    have HI : (∫ u in (0 : ℝ)..1, 1 - u) = 1 / 2 := by
      have H := intervalIntegral.integral_sub
        (continuous_const.intervalIntegrable 0 1 : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 1)
        (continuous_id.intervalIntegrable 0 1)
      change (∫ u in (0 : ℝ)..1, 1 - u) = _ at H
      rw [H, intervalIntegral.integral_const]
      simp only [id_eq]
      rw [integral_id]
      norm_num
    rw [intervalIntegral.integral_mul_const, HI]
    ring
  · have H : (∫ u in (0 : ℝ)..1, (1 - u) * t ^ 2 * deriv (deriv g) (u * t)) =
        g t - g 0 := by
      have HH := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (a := (0 : ℝ)) (b := 1)
        (f := fun u => (1 - u) * t * deriv g (u * t) + g (u * t))
        (f' := fun u => (1 - u) * t ^ 2 * deriv (deriv g) (u * t))
        (fun u hu => by
          convert ((((hasDerivAt_const u 1).sub (hasDerivAt_id u)).mul_const t).mul
            ((hd' (u * t)).hasDerivAt.comp u ((hasDerivAt_id u).mul_const t))).add
            ((hd (u * t)).hasDerivAt.comp u ((hasDerivAt_id u).mul_const t)) using 1 <;> (try funext z) <;> (try dsimp [Function.comp_def]) <;> ring)
        (by apply Continuous.intervalIntegrable; fun_prop)
      simpa [hz] using HH
    have HH : t ^ 2 * (∫ u in (0 : ℝ)..1, (1 - u) * (-deriv (deriv g) (u * t))) =
        -(g t - g 0) := by
      rw [← intervalIntegral.integral_const_mul, ← H, ← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr
      intro u hu
      ring
    simp only [Q, if_neg ht, iteratedDeriv_succ, iteratedDeriv_zero]
    apply (div_eq_iff (pow_ne_zero 2 ht)).mpr
    nlinarith [HH]

/-- An even twice continuously differentiable PD function has a PD quadratic deficit. -/
theorem Q_positiveDefinite {g : ℝ → ℝ} (he : Function.Even g) (hg : ContDiff ℝ 2 g)
    (hp : PositiveDefinite (fun t => (g t : ℂ))) :
    PositiveDefinite (fun t => (Q g t : ℂ)) := by
  have hc : Continuous (iteratedDeriv 2 g) := hg.continuous_iteratedDeriv 2 (by norm_num)
  have HI := Closure.integral (μ := volume.restrict (Ioc (0 : ℝ) 1))
    (f := fun u t => Complex.ofReal ((1 - u) * (-iteratedDeriv 2 g (u * t))))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      simpa only [Complex.ofReal_mul, Complex.ofReal_neg] using
        Closure.smul (Closure.dilation (neg_second_deriv hg hp) u)
          (a := 1 - u) (by linarith [hu.2]))
    (fun t => by
      apply Integrable.ofReal
      exact ((continuous_const.sub continuous_id).mul
        ((hc.comp (continuous_id.mul continuous_const)).neg)).integrableOn_Icc.mono_set
          Ioc_subset_Icc_self)
  convert HI using 1
  funext t
  rw [Q_integral he hg, intervalIntegral.integral_of_le (by norm_num)]
  exact (integral_ofReal (𝕜 := ℂ)
    (f := fun u : ℝ => (1 - u) * (-iteratedDeriv 2 g (u * t)))).symm

end D5.S3.Analytic.Fourier.PositiveDefinite.SecondDifference
