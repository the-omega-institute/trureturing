/- GID: D5/S3/Zeros/Jensen/ActualSourceJensenFixedWindow
   generality: I
   mirror-B: D5/B/S3/Zeros/Jensen/ActualSourceJensenFixedWindow
   mirror-E: none(waiver:source-fixed-window-consumer)
   anchors: [mathlib/module/Mathlib.MeasureTheory.Integral.CircleIntegral, mathlib/module/Mathlib.Analysis.Analytic.Order]
   utility: none
   digest: The unchanged all-mode source has a fixed-window signed derivative margin and an arbitrary-multiplicity retained-disk polynomial count. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Zeros.Jensen.JensenHermiteScaling
import D5.S3.Zeros.Jensen.JensenSimpleRealStability
import Mathlib.Topology.DiscreteSubset
import D5.S3.Zeros.Jensen.JensenDiskMultiplicityComparison
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.RingTheory.Polynomial.Hermite.Basic
import Mathlib.Tactic
import D5.S3.Analytic.Fourier.EvenGaussianMomentSeries
import D5.S3.Analytic.Fourier.ThetaDifferentialKernel
import D5.S3.Analytic.Fourier.XiThetaTransform
import D5.S3.Zeros.Jensen.SourceJensenIntegralExtension
import D5.S3.Zeros.Jensen.SourceJensenPositiveExtension
import D5.S3.Zeros.Jensen.SourceThetaMomentBounds
import D5.S3.Zeros.Jensen.PositiveThreeTermRootReality
import D5.S3.Zeros.Jensen.OriginalTailDerivativeVectorSources

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Zeros.Jensen.ActualSourceJensenFixedWindow

open Real Set MeasureTheory Filter Polynomial Metric
open scoped Topology BigOperators
open D5.S3.Analytic.Fourier.EvenGaussianMomentSeries
open D5.S3.Analytic.Fourier.ThetaDifferentialKernel
open D5.S3.Analytic.Fourier.XiThetaTransform
open D5.S3.Zeros.Jensen.NormalizedJensenDegreeLowering
open D5.S3.Zeros.Jensen.SourceJensenIntegralExtension
open D5.S3.Zeros.Jensen.SourceJensenPositiveExtension
open D5.S3.Zeros.Jensen.SourceThetaMomentBounds
open D5.S3.Zeros.Jensen.OriginalPrimalTailResponse
open D5.S3.Zeros.Jensen.OriginalTailDerivativeVector
open private elementary_zero
  correctionCoeff_nonneg
  correctionCoeff_top
  elementary_falling_factorial
  bonferroni_residual_bound
  weighted_residual_bound
  from D5.S3.Zeros.Jensen.JensenFiniteCoefficientRemainder
open private retained_disk_count
  from D5.S3.Zeros.Jensen.JensenDiskMultiplicityComparison
open private finite_moments
  full_G_extraction
  reflection_eval
  reflection_derivative
  reflected_node
  from D5.S3.Zeros.Jensen.OriginalTailDerivativeVectorSources
open private source_map
  source_lowering
  from D5.S3.Zeros.Jensen.SourceJensenIntegralExtension
open private coefficient_derivative_series
  from D5.S3.Zeros.Jensen.JensenAnalyticCoefficientRemainder
open private original_moment_bridge originalCoefficient
  from D5.S3.Zeros.Jensen.OriginalPrimalTailResponse

open private hermite_root_real_simple simple_cofactor coefficient_polynomial_norm_bound
  scaled_polynomial_size account_root_occurrences
  from D5.S3.Zeros.Jensen.JensenSimpleRealStability

/-! The following definitions are the source-side implementation vocabulary.
They deliberately keep every coefficient, every derivative order, and the
original reflected coordinate.  They are consumed below by one theorem. -/

def sourceF (z : ℂ) : ℂ :=
  cosineSquareTransform sourceThetaDensity z

def rawF (z : ℂ) : ℂ := cosineSquareTransform sourceThetaKernel z / 2

def sourcePolynomial (n : ℕ) : ℂ[X] :=
  ((sourceP n).map (algebraMap ℝ ℂ)).comp (C (-1) * X)

def reflectedNode (n : ℕ) (t : ℝ) : ℝ :=
  (n : ℝ) / ((n + 1 : ℕ) : ℝ) / t

def IsolatingDisk (F : ℂ → ℂ) (c : ℝ) (delta : ℝ) : Prop :=
  0 < delta ∧
    (∀ z : ℂ, ‖z - c‖ ≤ delta → z ≠ c → F z ≠ 0) ∧
    AnalyticOnNhd ℂ F (closedBall c delta)

def retainedRootCount (n : ℕ) (c : ℝ) (delta : ℝ) : ℕ :=
  ((sourcePolynomial n).roots.filter (fun z : ℂ => ‖z - (c : ℂ)‖ < delta)).card

def sourceA (j : ℕ) : ℂ := (-1 : ℂ) ^ j * (sourceThetaCoefficient j : ℂ)

def sourceH (z : ℂ) : ℂ := -4 * z * iteratedDeriv 2 sourceF z - 2 * deriv sourceF z

def sourceHA (j : ℕ) : ℂ := -((2 * j + 2 : ℕ) : ℂ) * (2 * j + 1 : ℕ) * sourceA (j + 1)

private theorem source_coefficients :
    (∀ R : ℝ, 0 ≤ R → Summable (fun j => ‖sourceA j‖ * R ^ j)) ∧
    AnalyticOnNhd ℂ sourceF Set.univ ∧
    (∀ n, sourcePolynomial n = coefficientPolynomial sourceA n) ∧
    ∀ z, HasSum (fun j => sourceA j * z ^ j) (sourceF z) := by
  have hz : 0 < fullZ := original_primal_tail_response.1
  have hp : Continuous sourceThetaDensity := source_theta_continuous.div_const fullZ
  have hb (x : ℝ) : |sourceThetaDensity x| ≤
      ((∑' j, thetaMajorant j) / fullZ) * Real.exp (-x ^ 2) := by
    change |sourceThetaKernel x / fullZ| ≤ _
    rw [abs_div, abs_of_pos hz,
      abs_of_pos (source_theta_gaussian_bound x).1]
    calc
      _ ≤ ((∑' j, thetaMajorant j) * Real.exp (-x ^ 2)) / fullZ :=
        div_le_div_of_nonneg_right (source_theta_gaussian_bound x).2 hz.le
      _ = _ := by ring
  have hseries := gaussian_even_moment_series hp hb
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro R hR
    simpa [sourceA, sourceThetaCoefficient, sourceThetaMoment, evenMomentCoefficient,
      norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_div,
      Nat.abs_cast] using (hseries.1 R hR).1
  · intro z _
    exact hseries.2.1.analyticAt_of_mem (by simp)
  · intro n
    rw [sourcePolynomial, source_map]
    simp only [sourceJensenPolynomial, Polynomial.sum_comp, mul_comp, C_comp,
      pow_comp, X_comp, coefficientPolynomial, sourceA]
    apply Finset.sum_congr rfl
    intro j _
    simp only [mul_pow, ← C_pow, ← mul_assoc, ← C_mul]
    congr 1
    push_cast
    ring
  · intro z
    simpa only [sourceF, evenMomentSeries, FormalMultilinearSeries.ofScalars_apply_eq,
      sourceA, sourceThetaCoefficient, sourceThetaMoment, evenMomentCoefficient, sub_zero, smul_eq_mul, mul_comm] using
        hseries.2.1.hasSum_sub (y := z) (by simp)

private theorem source_weighted_summable (L : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    Summable (fun j => ‖sourceA j‖ * (j : ℝ) ^ L * R ^ j) := by
  have hs := (source_coefficients.1 (Real.exp 1 * R) (by positivity)).mul_left (L.factorial : ℝ)
  apply hs.of_nonneg_of_le (fun j => by positivity)
  intro j
  have hp := Real.pow_div_factorial_le_exp (j : ℝ) (Nat.cast_nonneg j) L
  have hf : (0 : ℝ) < L.factorial := by exact_mod_cast Nat.factorial_pos L
  have hpoly : (j : ℝ) ^ L ≤ (L.factorial : ℝ) * Real.exp j := by
    exact (div_le_iff₀ hf).mp hp |>.trans_eq (mul_comm _ _)
  calc
    _ ≤ ‖sourceA j‖ * ((L.factorial : ℝ) * Real.exp j) * R ^ j :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpoly (norm_nonneg _))
        (pow_nonneg hR j)
    _ = _ := by rw [mul_pow, ← Real.exp_nat_mul]; push_cast; ring

private theorem source_eval (n : ℕ) (t : ℝ) :
    (sourcePolynomial n).eval (t : ℂ) = (originalJ n t : ℂ) := by
  rw [sourcePolynomial, eval_comp]
  simp only [eval_mul, eval_C, eval_X, neg_one_mul]
  rw [← Complex.ofReal_neg]
  change ((sourceP n).map (algebraMap ℝ ℂ)).eval ((algebraMap ℝ ℂ) (-t)) = _
  rw [eval_map_apply, ← (original_moment_bridge n t).2.1]
  rfl

private theorem source_response_derivative (n : ℕ) (t : ℝ) :
    HasDerivAt (originalJ n) (fullD n t) t ∧
    fullD n t = -(sourceP n).derivative.eval (-t) := by
  have hm (k : ℕ) : Integrable (fun x : ℝ => x ^ (2 * k) * sourceThetaDensity x) := by
    simpa only [sourceThetaDensity, fullZ, mul_div_assoc] using
      (source_theta_raw_moments k).1.div_const fullZ
  have hd : HasDerivAt (originalJ n) (fullD n t) t :=
    (finite_moments n t sourceThetaDensity volume hm).2.2.2.2.2.2
  have hp := ((sourceP n).hasDerivAt (-t)).comp t (hasDerivAt_id t).neg
  have he : originalJ n = fun u : ℝ => (sourceP n).eval (-u) :=
    funext (fun u => (original_moment_bridge n u).2.1)
  refine ⟨hd, ?_⟩
  rw [he] at hd
  simpa only [Function.comp_def, id_eq, mul_neg, mul_one] using hd.unique hp

private theorem source_derivative_real (k : ℕ) (t : ℝ) :
    (iteratedDeriv k sourceF (t : ℂ)).im = 0 := by
  have hs := Complex.imCLM.hasSum
    (coefficient_derivative_series sourceA sourceF source_coefficients.2.2.2
      source_weighted_summable k t)
  have hterm (j : ℕ) : sourceA j * (j.descFactorial k : ℂ) * (t : ℂ) ^ (j - k) =
      (((-1 : ℝ) ^ j * sourceThetaCoefficient j *
        (j.descFactorial k : ℝ) * t ^ (j - k) : ℝ) : ℂ) := by
    simp only [sourceA]
    push_cast
    rfl
  have heq : (fun j => Complex.imCLM (sourceA j * (j.descFactorial k : ℂ) *
      (t : ℂ) ^ (j - k))) = (fun _j : ℕ => (0 : ℝ)) := by
    funext j
    change (sourceA j * (j.descFactorial k : ℂ) * (t : ℂ) ^ (j - k)).im = 0
    rw [hterm, Complex.ofReal_im]
  have hz : HasSum (fun _j : ℕ => (0 : ℝ)) (iteratedDeriv k sourceF (t : ℂ)).im := by
    rw [heq] at hs
    exact hs
  exact hz.unique hasSum_zero

private theorem source_polynomial_derivative (n : ℕ) (t : ℝ) :
    (sourcePolynomial n).derivative.eval (t : ℂ) = (fullD n t : ℂ) := by
  rw [sourcePolynomial, derivative_comp]
  simp only [derivative_mul, derivative_C, derivative_X, zero_mul, mul_one,
    zero_add, eval_mul, eval_comp, eval_C, eval_X, neg_one_mul]
  rw [derivative_map, ← Complex.ofReal_neg]
  change -((sourceP n).derivative.map (algebraMap ℝ ℂ)).eval ((algebraMap ℝ ℂ) (-t)) = _
  rw [eval_map_apply,
    (source_response_derivative n t).2]
  push_cast
  rfl

private theorem sourceHA_moment (j : ℕ) :
    sourceHA j = (((-1 : ℝ) ^ j * sourceThetaMoment (j + 1) /
      ((2 * j).factorial : ℝ) : ℝ) : ℂ) := by
  have hf : (2 * (j + 1)).factorial = (2 * j + 2) * (2 * j + 1) * (2 * j).factorial := by
    rw [show 2 * (j + 1) = (2 * j + 1) + 1 by omega,
      Nat.factorial_succ, Nat.factorial_succ]
    ring
  have hf0 : ((2 * j).factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (2 * j)
  have h1 : (2 * j + 1 : ℂ) ≠ 0 := by
    exact_mod_cast (show (2 * j + 1 : ℕ) ≠ 0 by omega)
  have h2 : (2 * j + 2 : ℂ) ≠ 0 := by
    exact_mod_cast (show (2 * j + 2 : ℕ) ≠ 0 by omega)
  simp only [sourceHA, sourceA, sourceThetaCoefficient, hf, pow_succ]
  push_cast
  field_simp [hf0, h1, h2]
  <;> ring

private theorem source_second_moment_polynomial (n : ℕ) (t : ℝ) :
    (coefficientPolynomial sourceHA n).eval (t : ℂ) = (fullM2 n t : ℂ) := by
  have hm (k : ℕ) : Integrable (fun x : ℝ => x ^ (2 * k) * sourceThetaDensity x) := by
    simpa only [sourceThetaDensity, fullZ, mul_div_assoc] using
      (source_theta_raw_moments k).1.div_const fullZ
  have hM := (finite_moments n t sourceThetaDensity volume hm).2.2.2.2.2.1
  change fullM2 n t = _ at hM
  rw [hM]
  simp only [coefficientPolynomial, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X,
    map_sum, Complex.ofReal_sum, Complex.ofReal_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [sourceHA_moment]
  simp only [originalCoefficient, sourceThetaMoment, one_pow, mul_one]
  push_cast
  ring

/-- Every field is evaluated at the actual node t. -/
def NodeResponse (n : ℕ) (t : ℝ) : Prop :=
  originalJ n t = 0 ∧ fullD n t ≠ 0 ∧ fullG n t ≠ 0 ∧
  fullD n t = -(sourceP n).derivative.eval (-t) ∧
  (2 * (n : ℝ) + 1) * fullG n t = 2 * (n : ℝ) * fullD n t - fullM2 n t / 2 ∧
  HasDerivAt (originalJ (n + 1)) (fullG n t) (((n + 1 : ℕ) : ℝ) / n * t) ∧
  originalJ (n + 1) (((n + 1 : ℕ) : ℝ) / n * t) = (t / n) * fullG n t ∧
  originalJ (n + 1) (((n + 1 : ℕ) : ℝ) / n * t) ≠ 0 ∧
  (sourceQ n).eval t⁻¹ = 0 ∧ (sourceQ n).derivative.eval t⁻¹ ≠ 0 ∧
  (∃ Q : ℝ[X], sourceQ n = (X - C t⁻¹) * Q ∧ Q.eval t⁻¹ ≠ 0) ∧
  (let xi := reflectedNode n t
   0 < xi ∧ (sourceQ (n + 1)).derivative.eval xi = 0 ∧
   ((n + 1 : ℕ) : ℝ) * (sourceQ (n + 1)).eval xi = xi ^ n * fullG n t ∧
   xi ^ 2 * (sourceQ (n + 1)).derivative.derivative.eval xi = -(n : ℝ) * xi ^ n * fullD n t ∧
   (sourceQ (n + 1)).eval xi * (sourceQ (n + 1)).derivative.derivative.eval xi =
     -((n : ℝ) / ((n + 1 : ℕ) : ℝ)) * xi ^ (2 * n - 2) * fullD n t * fullG n t ∧
   (sourceQ (n + 1)).eval xi ≠ 0 ∧ (sourceQ (n + 1)).derivative.derivative.eval xi ≠ 0 ∧
   sourceCoupling (n + 1) xi * fullD n t ^ 2 = xi ^ 2 / (n : ℝ) * (fullD n t * fullG n t) ∧
   0 < sourceCoupling (n + 1) xi)

private theorem actual_source_response_telescope (n : ℕ) (hn : 1 ≤ n) (t : ℝ)
    (ht : 0 < t) (hnode : originalJ n t = 0) (hDG : 0 < fullD n t * fullG n t) :
    NodeResponse n t := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hd : fullD n t ≠ 0 := fun h => by simpa [h] using hDG
  have hg : fullG n t ≠ 0 := fun h => by simpa [h] using hDG
  have hD := (source_response_derivative n t).2
  have hG := (full_G_extraction hn t).2
  have hrel : (2 * (n : ℝ) + 1) * fullG n t = 2 * (n : ℝ) * fullD n t - fullM2 n t / 2 := by
    rw [fullG, mul_div_cancel₀ _ (by positivity)]
  let ell : ℝ := ((n + 1 : ℕ) : ℝ) / n
  have hnextD : -(sourceP (n + 1)).derivative.eval (-(ell * t)) = fullG n t := by
    have he : originalJ (n + 1) = fun u : ℝ => (sourceP (n + 1)).eval (-u) :=
      funext (fun u => (original_moment_bridge (n + 1) u).2.1)
    have hp := ((sourceP (n + 1)).hasDerivAt (-(ell * t))).comp (ell * t)
      (hasDerivAt_id (ell * t)).neg
    rw [he] at hG
    simpa only [Function.comp_def, id_eq, mul_neg, mul_one] using (hG.unique hp).symm
  have hav : originalJ (n + 1) (ell * t) = (t / n) * fullG n t := by
    have hlow := congrArg (fun p : ℝ[X] => p.eval (-(ell * t)))
      (source_lowering (n + 1) (by omega))
    have hscale : scale (n + 1) * (-(ell * t)) = -t := by
      simp only [scale, Nat.add_sub_cancel, ell]
      field_simp [hn0]
      <;> ring
    simp only [eval_sub, eval_mul, eval_C, eval_X, eval_comp, Nat.add_sub_cancel] at hlow
    rw [hscale, ← (original_moment_bridge n t).2.1, hnode] at hlow
    rw [← neg_neg ((sourceP (n + 1)).derivative.eval (-(ell * t))), hnextD,
      ← (original_moment_bridge (n + 1) (ell * t)).2.1] at hlow
    dsimp [ell] at hlow ⊢
    field_simp [hn0] at hlow ⊢
    nlinarith
  have hav0 : originalJ (n + 1) (ell * t) ≠ 0 := by
    rw [hav]; exact mul_ne_zero (div_ne_zero ht.ne' hn0) hg
  have hr : (sourceQ n).eval t⁻¹ = 0 := by
    rw [reflection_eval n (inv_ne_zero ht.ne'), inv_inv, hnode, mul_zero]
  have hrd : (sourceQ n).derivative.eval t⁻¹ ≠ 0 := by
    have he := reflection_derivative hn (inv_ne_zero ht.ne')
    rw [inv_inv, hnode, mul_zero, zero_sub] at he
    intro hzero
    rw [hzero, mul_zero] at he
    exact (mul_ne_zero (pow_ne_zero _ (inv_ne_zero ht.ne')) hd) (neg_eq_zero.mp he.symm)
  let Q := (sourceQ n) /ₘ (X - C t⁻¹)
  have hfac : sourceQ n = (X - C t⁻¹) * Q :=
    (Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hr).symm
  have hQ : Q.eval t⁻¹ ≠ 0 := by
    have he : (sourceQ n).derivative.eval t⁻¹ = Q.eval t⁻¹ := by
      rw [hfac, derivative_mul]; simp
    exact he ▸ hrd
  have href := reflected_node hn ht hnode
  change 0 < reflectedNode n t ∧ _ at href
  obtain ⟨hxi, hqp, hqv, hq2, hprod, hiff, hcouple⟩ := href
  change _ = _ at hqp
  change ((n + 1 : ℕ) : ℝ) * (sourceQ (n + 1)).eval (reflectedNode n t) =
    (reflectedNode n t) ^ n * fullG n t at hqv
  have hq20 := hiff.mp hd
  have hq0 : (sourceQ (n + 1)).eval (reflectedNode n t) ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hqv
    exact (mul_ne_zero (pow_ne_zero _ hxi.ne') hg) hqv.symm
  have hc : sourceCoupling (n + 1) (reflectedNode n t) =
      (reflectedNode n t) ^ 2 / n * (fullG n t / fullD n t) := (hcouple hd).1
  have hcf : sourceCoupling (n + 1) (reflectedNode n t) * fullD n t ^ 2 =
      (reflectedNode n t) ^ 2 / n * (fullD n t * fullG n t) := by
    rw [hc]; field_simp [hd] <;> ring
  have hcpos : 0 < sourceCoupling (n + 1) (reflectedNode n t) := by
    have hright : 0 < (reflectedNode n t) ^ 2 / (n : ℝ) * (fullD n t * fullG n t) := by
      apply mul_pos (div_pos (sq_pos_of_pos hxi) (by exact_mod_cast (show 0 < n by omega))) hDG
    exact pos_of_mul_pos_left (hcf.symm ▸ hright) (sq_nonneg _)
  exact ⟨hnode, hd, hg, hD, hrel, (full_G_extraction hn t).2, hav, hav0, hr, hrd,
    ⟨Q, hfac, hQ⟩, hxi, hqp, hqv, hq2, hprod, hq0, hq20, hcf, hcpos⟩

private theorem source_normalization : 0 < fullZ ∧ 0 < 2 / fullZ ∧
    ∀ z, sourceF z = (2 / (fullZ : ℂ)) * rawF z := by
  have hz : 0 < fullZ := original_primal_tail_response.1
  refine ⟨hz, div_pos (by norm_num) hz, ?_⟩
  intro z
  change (∫ x : ℝ, ((sourceThetaKernel x / fullZ : ℝ) : ℂ) *
      Complex.cos (Complex.sqrt z * (x : ℂ))) = _
  simp_rw [Complex.ofReal_div, div_mul_eq_mul_div]
  rw [integral_div]
  unfold rawF cosineSquareTransform
  field_simp [Complex.ofReal_ne_zero.mpr hz.ne']
  <;> ring

private theorem signed_product_of_M_margin (n : ℕ) (hn : 1 ≤ n) (t : ℝ)
    (hd : fullD n t ≠ 0) (hM : |fullM2 n t| ≤ (n : ℝ) * |fullD n t|) :
    fullD n t * fullG n t ≥ fullD n t ^ 2 / 2 ∧ fullD n t ^ 2 / 2 > 0 := by
  have hrel : (2 * (n : ℝ) + 1) * fullG n t =
      2 * (n : ℝ) * fullD n t - fullM2 n t / 2 := by
    rw [fullG, mul_div_cancel₀ _ (by positivity)]
  have hprod : fullD n t * fullM2 n t ≤ (n : ℝ) * fullD n t ^ 2 := by
    calc
      _ ≤ |fullD n t * fullM2 n t| := le_abs_self _
      _ = |fullD n t| * |fullM2 n t| := abs_mul _ _
      _ ≤ |fullD n t| * ((n : ℝ) * |fullD n t|) :=
        mul_le_mul_of_nonneg_left hM (abs_nonneg _)
      _ = _ := by rw [mul_left_comm, ← sq, sq_abs]
  have he := congrArg (fun y : ℝ => fullD n t * y) hrel
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsq := sq_pos_of_ne_zero hd
  constructor
  · have hnsq : fullD n t ^ 2 ≤ (n : ℝ) * fullD n t ^ 2 :=
      le_mul_of_one_le_left hsq.le hnR
    have hden : 0 < 2 * (n : ℝ) + 1 := by positivity
    have hscaled : 0 ≤ (2 * (n : ℝ) + 1) *
        (fullD n t * fullG n t - fullD n t ^ 2 / 2) := by nlinarith [he]
    exact sub_nonneg.mp (nonneg_of_mul_nonneg_right hscaled hden)
  · positivity

private theorem sourceH_coefficients :
    (∀ z, HasSum (fun j => sourceHA j * z ^ j) (sourceH z)) ∧
    (∀ L R, 0 ≤ R → Summable (fun j => ‖sourceHA j‖ * (j : ℝ) ^ L * R ^ j)) := by
  constructor
  · intro z
    simpa only [sourceHA, sourceH, loweredCoefficients] using
      lowered_series sourceA sourceF source_coefficients.2.2.2 source_weighted_summable z
  · intro L R hR
    simpa only [sourceHA, loweredCoefficients] using
      (lowered_weighted_data sourceA source_weighted_summable L R hR).1

private theorem source_scaled_estimates (t0 sigma : ℝ) (ht0 : 0 < t0)
    (hs : 0 < sigma) (v : ℕ) :
    (IsExactRealOrder sourceF t0 v → ScaledFunctionEstimate sourceF sourceA t0 sigma v) ∧
    (IsExactRealOrder sourceH t0 v → ScaledFunctionEstimate sourceH sourceHA t0 sigma v) := by
  constructor
  · exact hermite_scaled_estimate sourceA sourceF source_coefficients.2.2.2
      source_weighted_summable t0 sigma ht0 hs v
  · exact hermite_scaled_estimate sourceHA sourceH sourceH_coefficients.1
      sourceH_coefficients.2 t0 sigma ht0 hs v

private theorem sourceH_iterated (r : ℕ) (z : ℂ) :
    iteratedDeriv r sourceH z = -4 * z * iteratedDeriv (r + 2) sourceF z -
      ((4 * r + 2 : ℕ) : ℂ) * iteratedDeriv (r + 1) sourceF z := by
  induction r generalizing z with
  | zero => simp [sourceH, iteratedDeriv_succ]
  | succ r ih =>
    have he : iteratedDeriv r sourceH = fun w => -4 * w * iteratedDeriv (r + 2) sourceF w -
        ((4 * r + 2 : ℕ) : ℂ) * iteratedDeriv (r + 1) sourceF w := funext ih
    have hF := source_coefficients.2.1 z (Set.mem_univ z)
    have h1 := (hF.iterated_deriv (r + 2)).differentiableAt.hasDerivAt
    have h2 := (hF.iterated_deriv (r + 1)).differentiableAt.hasDerivAt
    simp only [← iteratedDeriv_eq_iterate] at h1 h2
    have hd := (((hasDerivAt_id z).const_mul (-4)).mul h1).sub
      (h2.const_mul ((4 * r + 2 : ℕ) : ℂ))
    simp only [Pi.mul_def, Pi.sub_def, id_eq] at hd
    rw [iteratedDeriv_succ, he, hd.deriv]
    simp only [← iteratedDeriv_succ, id_eq]
    simp only [show r + 1 + 2 = r + 3 by omega,
      show r + 1 + 1 = r + 2 by omega]
    push_cast
    ring

private theorem sourceH_order (t0 : ℝ) (ht0 : 0 < t0) (m : ℕ) (hm : 2 ≤ m)
    (ho : IsExactRealOrder sourceF t0 m) : IsExactRealOrder sourceH t0 (m - 2) := by
  constructor
  · rw [sourceH_iterated, show m - 2 + 2 = m by omega,
      ho.2 (m - 2 + 1) (by omega), mul_zero, sub_zero]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr ht0.ne')) ho.1
  · intro k hk
    rw [sourceH_iterated, ho.2 (k + 2) (by omega), ho.2 (k + 1) (by omega)]
    ring

private theorem source_uniform_approximation (n : ℕ) (hn : 1 ≤ n) (R : ℝ) (hR : 1 ≤ R)
    (z : ℂ) (hz : ‖z‖ ≤ R) :
    ‖(sourcePolynomial n).eval z - sourceF z‖ ≤ 2 / (n : ℝ) * weightedNorm sourceA 2 R := by
  classical
  let w : ℕ → ℂ := fun j => (n.descFactorial j : ℂ) / (n : ℂ) ^ j * sourceA j * z ^ j
  have hw : HasSum w ((sourcePolynomial n).eval z) := by
    rw [source_coefficients.2.2.1 n]
    simp only [coefficientPolynomial, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
    apply hasSum_sum_of_ne_finset_zero
    intro j hj
    have hnj : n < j := by have := Finset.mem_range.not.mp hj; omega
    simp [w, Nat.descFactorial_of_lt hnj]
  have hs := hw.sub (source_coefficients.2.2.2 z)
  have hmajor := (source_weighted_summable 2 R (by linarith)).mul_left (2 / (n : ℝ))
  apply hs.norm_le_of_bounded (by simpa [weightedNorm, tsum_mul_left] using hmajor.hasSum)
  intro j
  have he : w j - sourceA j * z ^ j =
      (bonferroniResidual n 0 j : ℂ) * sourceA j * z ^ j := by
    simp [w, bonferroniResidual, elementary_zero]
    push_cast
    ring
  rw [he, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow]
  have hp := pow_le_pow_left₀ (norm_nonneg z) hz j
  have hb := bonferroni_residual_bound n 0 j hn
  simp only [zero_add, pow_one, zero_mul] at hb
  calc
    _ ≤ (2 / (n : ℝ) * (j : ℝ) ^ 2) * ‖sourceA j‖ * R ^ j :=
      mul_le_mul (mul_le_mul_of_nonneg_right hb (norm_nonneg _)) hp
        (pow_nonneg (norm_nonneg _) _) (by positivity)
    _ = _ := by ring

private theorem scaled_local_certificate (t0 delta : ℝ) (m : ℕ)
    (ht0 : 0 < t0) (hm : 1 ≤ m) (ho : IsExactRealOrder sourceF t0 m)
    (hi : IsolatingDisk sourceF t0 delta) :
    ∃ C d : ℝ, 0 < C ∧ 0 < d ∧ ∃ N : ℕ, ∀ n ≥ N, 1 ≤ n ∧
      ∃ nodes : Fin m → ℝ, Function.Injective nodes ∧
        (∀ i, 0 < nodes i ∧ |nodes i - t0| < delta) ∧
        (∀ i, originalJ n (nodes i) = 0 ∧
          (sourcePolynomial n).derivative.eval (nodes i : ℂ) ≠ 0) ∧
        (∀ i, |nodes i - t0| ≤ C / Real.sqrt n) ∧
        (∀ i, d / (Real.sqrt n) ^ (m - 1) ≤ |fullD n (nodes i)|) ∧
        (∀ i, |fullM2 n (nodes i)| ≤ (n : ℝ) * |fullD n (nodes i)|) ∧
        (∀ z ∈ sphere (t0 : ℂ) delta,
          ‖(sourcePolynomial n).eval z - sourceF z‖ < ‖sourceF z‖) := by
  classical
  let sigma : ℝ := min (delta / 2) (min (t0 / 2) 1)
  let Rdisk : ℝ := max 1 (t0 + delta)
  have hdelta : 0 < delta := hi.1
  have hsigma : 0 < sigma := by dsimp [sigma]; positivity
  have hscaled := (source_scaled_estimates t0 sigma ht0 hsigma m).1 ho
  let A : ℂ := (t0 : ℂ) ^ m * iteratedDeriv m sourceF t0 / (m.factorial : ℂ)
  have hA : A ≠ 0 := div_ne_zero
    (mul_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr ht0.ne')) ho.1)
    (by exact_mod_cast Nat.factorial_ne_zero m)
  let a : ℝ := t0 ^ m * (iteratedDeriv m sourceF t0).re / (m.factorial : ℝ)
  have hdercast : iteratedDeriv m sourceF t0 =
      ((iteratedDeriv m sourceF t0).re : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using source_derivative_real m t0
  have hAcast : A = (a : ℂ) := by
    dsimp [A, a]
    rw [hdercast]
    push_cast
    rfl
  have ha : a ≠ 0 := by intro h; apply hA; rw [hAcast, h, Complex.ofReal_zero]
  let Q (n : ℕ) : ℂ[X] :=
    C ((A / (Real.sqrt n : ℂ) ^ m)⁻¹) *
      (sourcePolynomial n).comp
        (C (t0 : ℂ) * (1 + C ((Real.sqrt n : ℂ)⁻¹) * X))
  have hQeval (n : ℕ) (u : ℂ) : (Q n).eval u =
      (sourcePolynomial n).eval ((t0 : ℂ) * (1 + u / (Real.sqrt n : ℂ))) /
        (A / (Real.sqrt n : ℂ) ^ m) := by
    simp only [Q, eval_mul, eval_C, eval_comp, eval_add, eval_one, eval_X]
    have harg : (t0 : ℂ) * (1 + (Real.sqrt n : ℂ)⁻¹ * u) =
        (t0 : ℂ) * (1 + u / (Real.sqrt n : ℂ)) := by ring
    rw [harg]
    ring
  have hQreal (n : ℕ) (u : ℝ) : ((Q n).eval (u : ℂ)).im = 0 := by
    rw [hQeval, hAcast]
    have he : (t0 : ℂ) * (1 + (u : ℂ) / (Real.sqrt n : ℂ)) =
        ((t0 * (1 + u / Real.sqrt n) : ℝ) : ℂ) := by push_cast; rfl
    rw [he, source_eval]
    have hd : (a : ℂ) / (Real.sqrt n : ℂ) ^ m =
        ((a / Real.sqrt n ^ m : ℝ) : ℂ) := by push_cast; rfl
    rw [hd, ← Complex.ofReal_div, Complex.ofReal_im]
  let p : ℝ[X] := (Polynomial.hermite m).map (algebraMap ℤ ℝ)
  have hmap (P : ℤ[X]) (z : ℂ) :
      aeval z (P.map (algebraMap ℤ ℝ)) = aeval z P :=
    (Polynomial.aeval_eq_aeval_map (φ := algebraMap ℤ ℝ) (Subsingleton.elim _ _) P z).symm
  have hpmonic : p.Monic := (Polynomial.hermite_monic m).map _
  have hpdegree : p.natDegree = m :=
    ((Polynomial.hermite_monic m).natDegree_map _).trans (Polynomial.natDegree_hermite (n := m))
  have hpreal (z : ℂ) (hz : aeval z p = 0) : z.im = 0 := by
    rw [hmap] at hz
    exact (hermite_root_real_simple m hm z hz).1
  have hpsimple (z : ℂ) (hz : aeval z p = 0) : aeval z p.derivative ≠ 0 := by
    rw [hmap] at hz
    rw [show p.derivative = (Polynomial.hermite m).derivative.map (algebraMap ℤ ℝ) by
      dsimp [p]; rw [derivative_map], hmap]
    exact (hermite_root_real_simple m hm z hz).2
  have happrox : ∀ q : ℝ, 2 ≤ q → ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ,
      ∀ n ≥ N, 1 ≤ n ∧ ∀ z : ℂ, ‖z‖ ≤ q →
        ‖(Q n).eval z - aeval z p‖ ≤ C / Real.sqrt n := by
    intro q hq
    obtain ⟨C, hC, N, hN⟩ := hscaled q hq
    refine ⟨C, hC, N, ?_⟩
    intro n hn
    obtain ⟨hn1, herr⟩ := hN n hn
    refine ⟨hn1, ?_⟩
    intro z hz
    rw [hQeval, hmap, source_coefficients.2.2.1]
    exact herr z hz
  obtain ⟨R, chi, hR, hchi, Nroots, hroots⟩ :=
    JensenSimpleRealStability.simple_real_polynomial_stability p m hpmonic hpdegree
      hpreal hpsimple Q hQreal happrox
  let C0 : ℝ := t0 * R
  let d : ℝ := chi * |a| / t0
  have hC0 : 0 < C0 := mul_pos ht0 (lt_of_lt_of_le zero_lt_one hR)
  have hd : 0 < d := div_pos (mul_pos hchi (abs_pos.mpr ha)) ht0
  have hrootlim : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hlocEv : ∀ᶠ n : ℕ in atTop,
      1 ≤ n ∧ 1 ≤ Real.sqrt n ∧ C0 / Real.sqrt n < min delta (t0 / 2) := by
    filter_upwards [eventually_ge_atTop 1,
      (tendsto_const_nhds.div_atTop hrootlim).eventually
        (eventually_lt_nhds (by positivity : (0 : ℝ) < min delta (t0 / 2)))] with n hn hsmall
    refine ⟨hn, ?_, hsmall⟩
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (by exact_mod_cast hn : (1 : ℝ) ≤ n)
  obtain ⟨Nloc, hloc⟩ := Filter.eventually_atTop.mp hlocEv
  have hgeometry (n : ℕ) (hn : Nloc ≤ n) (u : ℝ) (hu : |u| ≤ R) :
      0 < t0 * (1 + u / Real.sqrt n) ∧
      |t0 * (1 + u / Real.sqrt n) - t0| < delta ∧
      |t0 * (1 + u / Real.sqrt n) - t0| ≤ C0 / Real.sqrt n ∧
      ‖((t0 * (1 + u / Real.sqrt n) : ℝ) : ℂ)‖ ≤ Rdisk := by
    have hnl := hloc n hn
    have hs : 0 < Real.sqrt n := lt_of_lt_of_le zero_lt_one hnl.2.1
    have hdist : |t0 * (1 + u / Real.sqrt n) - t0| ≤ C0 / Real.sqrt n := by
      rw [show t0 * (1 + u / Real.sqrt n) - t0 = t0 * u / Real.sqrt n by ring,
        abs_div, abs_mul, abs_of_pos ht0, abs_of_pos hs]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hu ht0.le) hs.le
    have hdelta' := hdist.trans_lt (hnl.2.2.trans_le (min_le_left _ _))
    have hhalf := hdist.trans_lt (hnl.2.2.trans_le (min_le_right _ _))
    have hpos : 0 < t0 * (1 + u / Real.sqrt n) := by
      have := (abs_lt.mp hhalf).1
      linarith
    refine ⟨hpos, hdelta', hdist, ?_⟩
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
    exact (by linarith [(abs_lt.mp hdelta').2] : t0 * (1 + u / Real.sqrt n) ≤ t0 + delta).trans
      (le_max_right _ _)
  have hMB : ∃ B : ℝ, 0 < B ∧ ∃ NM : ℕ, ∀ n ≥ NM, ∀ u : ℝ, |u| ≤ R →
      |fullM2 n (t0 * (1 + u / Real.sqrt n))| ≤ B / Real.sqrt n ^ (m - 2) := by
    by_cases hm2 : 2 ≤ m
    · have hoH := sourceH_order t0 ht0 m hm2 ho
      have hsH := (source_scaled_estimates t0 sigma ht0 hsigma (m - 2)).2 hoH
      obtain ⟨B, hB, NM, hNM⟩ := scaled_polynomial_size sourceH sourceHA t0 sigma ht0
        (m - 2) hoH hsH R
      refine ⟨B, hB, NM, ?_⟩
      intro n hn u hu
      have hh := (hNM n hn).2 (u : ℂ) (by simpa using hu)
      have he : (t0 : ℂ) * (1 + (u : ℂ) / (Real.sqrt n : ℂ)) =
          ((t0 * (1 + u / Real.sqrt n) : ℝ) : ℂ) := by push_cast; rfl
      rw [he, source_second_moment_polynomial, Complex.norm_real, Real.norm_eq_abs] at hh
      exact hh
    · have hm1 : m = 1 := by omega
      let W := weightedNorm sourceHA 0 Rdisk
      have hW : 0 ≤ W := tsum_nonneg (fun j => by positivity)
      refine ⟨W + 1, by positivity, Nloc, ?_⟩
      intro n hn u hu
      have hnl := hloc n hn
      have hh := coefficient_polynomial_norm_bound sourceHA n hnl.1 Rdisk
        (by dsimp [Rdisk]; positivity)
        (by simpa using sourceH_coefficients.2 0 Rdisk (by dsimp [Rdisk]; positivity))
        ((t0 * (1 + u / Real.sqrt n) : ℝ) : ℂ) (hgeometry n hn u hu).2.2.2
      rw [source_second_moment_polynomial, Complex.norm_real, Real.norm_eq_abs] at hh
      simpa only [hm1, Nat.sub_eq_zero_of_le (by omega : 1 ≤ 2), pow_zero, div_one] using
        hh.trans (le_add_of_nonneg_right zero_le_one)
  obtain ⟨B, hB, NM, hNM⟩ := hMB
  obtain ⟨Nsize, hsize⟩ := Filter.eventually_atTop.mp
    (hrootlim.eventually (eventually_ge_atTop (B / d)))
  have hFn (z : ℂ) (hz : z ∈ sphere (t0 : ℂ) delta) : sourceF z ≠ 0 := by
    apply hi.2.1 z (le_of_eq (mem_sphere_iff_norm.mp hz))
    intro he
    have hh := mem_sphere_iff_norm.mp hz
    rw [he, sub_self, norm_zero] at hh
    linarith
  obtain ⟨bdelta, hbdelta, hmin⟩ := (isCompact_sphere (t0 : ℂ) delta).exists_forall_le'
    (source_coefficients.2.1.continuousOn.norm.mono (Set.subset_univ _))
    (fun z hz => norm_pos_iff.mpr (hFn z hz))
  obtain ⟨Nboundary, hNboundary⟩ := exists_nat_gt (2 * weightedNorm sourceA 2 Rdisk / bdelta)
  refine ⟨C0, d, hC0, hd, max Nroots (max Nloc (max NM (max Nsize (max 1 Nboundary)))), ?_⟩
  intro n hn
  have hnroots : Nroots ≤ n := (le_max_left _ _).trans hn
  have hnloc : Nloc ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hnM : NM ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hn))
  have hnsize : Nsize ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hn)))
  have hnbound : max 1 Nboundary ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hn)))
  obtain ⟨hn1, u, huinj, huR, huroot, huchi⟩ := hroots n hnroots
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < n by omega))
  have hsc : (Real.sqrt n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  have hs1 := (hloc n hnloc).2.1
  have hsq : Real.sqrt n ^ 2 = (n : ℝ) := Real.sq_sqrt (by positivity)
  let nodes : Fin m → ℝ := fun i => t0 * (1 + u i / Real.sqrt n)
  have hQD (i : Fin m) : (Q n).derivative.eval (u i : ℂ) =
      (sourcePolynomial n).derivative.eval (nodes i : ℂ) * (t0 : ℂ) *
        (Real.sqrt n : ℂ) ^ (m - 1) / A := by
    have he : (fun z : ℂ => (Q n).eval z) = fun z =>
        (sourcePolynomial n).eval ((t0 : ℂ) * (1 + z / (Real.sqrt n : ℂ))) /
          (A / (Real.sqrt n : ℂ) ^ m) := funext (hQeval n)
    have hp := (((sourcePolynomial n).hasDerivAt
      ((t0 : ℂ) * (1 + (u i : ℂ) / (Real.sqrt n : ℂ)))).comp (u i : ℂ)
        ((((hasDerivAt_id (u i : ℂ)).div_const (Real.sqrt n : ℂ)).const_add 1).const_mul (t0 : ℂ))).div_const
          (A / (Real.sqrt n : ℂ) ^ m)
    have hdQ := (Q n).hasDerivAt (u i : ℂ)
    rw [he] at hdQ
    have hd := hdQ.unique hp
    have hcoord : (t0 : ℂ) * (1 + (u i : ℂ) / (Real.sqrt n : ℂ)) = (nodes i : ℂ) := by
      dsimp [nodes]; push_cast; rfl
    rw [hcoord] at hd
    have hpow : (Real.sqrt n : ℂ) ^ m =
        (Real.sqrt n : ℂ) ^ (m - 1) * (Real.sqrt n : ℂ) := by
      rw [← pow_succ, Nat.sub_add_cancel hm]
    rw [hd, hpow]
    field_simp [hA, hsc]
    <;> ring
  have hmargin (i : Fin m) : d / Real.sqrt n ^ (m - 1) ≤ |fullD n (nodes i)| := by
    have hnorm : ‖(Q n).derivative.eval (u i : ℂ)‖ =
        |fullD n (nodes i)| * t0 * Real.sqrt n ^ (m - 1) / |a| := by
      rw [hQD, source_polynomial_derivative, hAcast]
      simp only [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos ht0, abs_of_pos hs]
    have hc : chi ≤ |fullD n (nodes i)| * t0 * Real.sqrt n ^ (m - 1) / |a| := by
      simpa only [hnorm] using huchi i
    dsimp only [d]
    apply (div_le_iff₀ (pow_pos hs _)).mpr
    apply (div_le_iff₀ ht0).mpr
    simpa only [mul_assoc, mul_comm, mul_left_comm] using
      (le_div_iff₀ (abs_pos.mpr ha)).mp hc
  have hsimple (i : Fin m) : (sourcePolynomial n).derivative.eval (nodes i : ℂ) ≠ 0 := by
    rw [source_polynomial_derivative]
    exact Complex.ofReal_ne_zero.mpr (abs_pos.mp
      (lt_of_lt_of_le (div_pos hd (pow_pos hs _)) (hmargin i)))
  refine ⟨hn1, nodes, ?_, ?_, ?_, ?_, hmargin, ?_, ?_⟩
  · intro i j he
    apply huinj
    have h := mul_left_cancel₀ ht0.ne' he
    change 1 + u i / Real.sqrt n = 1 + u j / Real.sqrt n at h
    exact (div_left_inj' hs.ne').mp (add_left_cancel h)
  · intro i
    exact ⟨(hgeometry n hnloc _ (huR i)).1, (hgeometry n hnloc _ (huR i)).2.1⟩
  · intro i
    refine ⟨?_, hsimple i⟩
    have hh := huroot i
    rw [hQeval] at hh
    have hcoord : (t0 : ℂ) * (1 + (u i : ℂ) / (Real.sqrt n : ℂ)) = (nodes i : ℂ) := by
      dsimp [nodes]; push_cast; rfl
    rw [hcoord] at hh
    have hp : (sourcePolynomial n).eval (nodes i : ℂ) = 0 :=
      (div_eq_zero_iff).mp hh |>.resolve_right (div_ne_zero hA (pow_ne_zero _ hsc))
    rw [source_eval] at hp
    exact Complex.ofReal_injective (by simpa using hp)
  · intro i
    exact (hgeometry n hnloc _ (huR i)).2.2.1
  · intro i
    have hMb := hNM n hnM _ (huR i)
    have hBs : B ≤ Real.sqrt n * d := by
      have hh := (div_le_iff₀ hd).mp (hsize n hnsize)
      nlinarith
    by_cases hm2 : 2 ≤ m
    · have hpow : Real.sqrt n ^ (m - 1) = Real.sqrt n ^ (m - 2) * Real.sqrt n := by
        rw [← pow_succ]; congr 1; omega
      calc
        _ ≤ B / Real.sqrt n ^ (m - 2) := hMb
        _ ≤ (Real.sqrt n * d) / Real.sqrt n ^ (m - 2) :=
          div_le_div_of_nonneg_right hBs (pow_nonneg hs.le _)
        _ = Real.sqrt n ^ 2 * (d / Real.sqrt n ^ (m - 1)) := by
          rw [hpow]
          field_simp [hs.ne']
          <;> ring
        _ = (n : ℝ) * (d / Real.sqrt n ^ (m - 1)) := by rw [hsq]
        _ ≤ _ := mul_le_mul_of_nonneg_left (hmargin i) (Nat.cast_nonneg _)
    · have hm1 : m = 1 := by omega
      simp only [hm1, Nat.sub_eq_zero_of_le (by omega : 1 ≤ 2), pow_zero, div_one] at hMb
      have hnlarge : Real.sqrt n ≤ (n : ℝ) := by nlinarith
      have hh := mul_le_mul_of_nonneg_right hnlarge hd.le
      have hmarg := hmargin i
      simp only [hm1, Nat.sub_self, pow_zero, div_one] at hmarg
      nlinarith
  · intro z hz
    have hzR : ‖z‖ ≤ Rdisk := by
      have htri := norm_add_le (z - (t0 : ℂ)) (t0 : ℂ)
      rw [sub_add_cancel, mem_sphere_iff_norm.mp hz, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos ht0] at htri
      exact htri.trans (by dsimp [Rdisk]; linarith [le_max_right 1 (t0 + delta)])
    have he := source_uniform_approximation n hn1 Rdisk (le_max_left _ _) z hzR
    have hcrit : 2 / (n : ℝ) * weightedNorm sourceA 2 Rdisk < bdelta := by
      have hkn : (Nboundary : ℝ) ≤ n := by exact_mod_cast (le_max_right 1 Nboundary).trans hnbound
      have hh := (div_lt_iff₀ hbdelta).mp (hNboundary.trans_le hkn)
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by exact_mod_cast (show 0 < n by omega) : (0 : ℝ) < n)]
      nlinarith
    exact (he.trans_lt hcrit).trans_le (hmin z hz)

/-- The disk is the caller's original disk; the multiset equality records occurrences. -/
def LocalConclusion (t0 delta : ℝ) (m : ℕ) : Prop :=
  ∃ C0 d : ℝ, 0 < C0 ∧ 0 < d ∧ ∃ N : ℕ, ∀ n ≥ N, 1 ≤ n ∧
    retainedRootCount n t0 delta = m ∧
    (∀ z ∈ sphere (t0 : ℂ) delta, (sourcePolynomial n).eval z ≠ 0) ∧
    ∃ nodes : Fin m → ℝ, Function.Injective nodes ∧
      (∀ i, 0 < nodes i ∧ |nodes i - t0| < delta) ∧
      (∀ i, originalJ n (nodes i) = 0 ∧
        (sourcePolynomial n).eval (nodes i : ℂ) = 0 ∧
        (sourcePolynomial n).derivative.eval (nodes i : ℂ) ≠ 0) ∧
      (∀ i, |nodes i - t0| ≤ C0 / Real.sqrt n) ∧
      (∀ i, d / (Real.sqrt n) ^ (m - 1) ≤ |fullD n (nodes i)|) ∧
      (∀ i, |fullM2 n (nodes i)| ≤ (n : ℝ) * |fullD n (nodes i)|) ∧
      ((sourcePolynomial n).roots.filter (fun z : ℂ => ‖z - (t0 : ℂ)‖ < delta) =
        (Finset.univ : Finset (Fin m)).val.map (fun i => (nodes i : ℂ))) ∧
      (∀ i, ((sourcePolynomial n).roots.filter
        (fun z : ℂ => ‖z - (t0 : ℂ)‖ < delta)).count (nodes i : ℂ) = 1) ∧
      (∀ i, ∃ Q : ℂ[X], sourcePolynomial n = (X - C (nodes i : ℂ)) * Q ∧ Q.eval (nodes i : ℂ) ≠ 0) ∧
      (∀ i, fullD n (nodes i) * fullG n (nodes i) ≥ fullD n (nodes i) ^ 2 / 2 ∧
        fullD n (nodes i) ^ 2 / 2 > 0 ∧ NodeResponse n (nodes i))

private theorem local_complete (t0 delta : ℝ) (m : ℕ) (ht0 : 0 < t0)
    (hm : 1 ≤ m) (ho : IsExactRealOrder sourceF t0 m) (hi : IsolatingDisk sourceF t0 delta) :
    LocalConclusion t0 delta m := by
  classical
  obtain ⟨C0, d, hC, hd, N, hN⟩ := scaled_local_certificate t0 delta m ht0 hm ho hi
  refine ⟨C0, d, hC, hd, N, ?_⟩
  intro n hn
  obtain ⟨hn1, nodes, hinj, hpos, hroot, herr, hmargin, hM, hboundary⟩ := hN n hn
  have horder : analyticOrderAt sourceF (t0 : ℂ) = m :=
    (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero (source_coefficients.2.1 _ (by trivial))).mpr
      ⟨ho.2, ho.1⟩
  have hc := retained_disk_count sourceF (sourcePolynomial n) t0 delta m hi.1 hm hi.2.2
    horder (fun z hz hne => hi.2.1 z (mem_closedBall_iff_norm.mp hz) hne) hboundary
  have hcomplex (i : Fin m) : (sourcePolynomial n).eval (nodes i : ℂ) = 0 := by
    rw [source_eval, (hroot i).1, Complex.ofReal_zero]
  have hinside (i : Fin m) : ‖(nodes i : ℂ) - (t0 : ℂ)‖ < delta := by
    simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using (hpos i).2
  have hocc := account_root_occurrences (sourcePolynomial n) t0 delta m hc.1 nodes hinj
    hcomplex hinside hc.2.2
  refine ⟨hn1, hc.2.2, hc.2.1, nodes, hinj, hpos,
    (fun i => ⟨(hroot i).1, hcomplex i, (hroot i).2⟩), herr, hmargin, hM, hocc, ?_, ?_, ?_⟩
  · intro i
    rw [hocc]
    have hnodup := Multiset.Nodup.map (Complex.ofReal_injective.comp hinj) Finset.univ.nodup
    apply (Multiset.count_eq_one_of_mem hnodup)
    exact Multiset.mem_map.mpr ⟨i, by simp, rfl⟩
  · intro i
    exact simple_cofactor _ _ (hcomplex i) (hroot i).2
  · intro i
    have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hDn : fullD n (nodes i) ≠ 0 := abs_pos.mp
      (lt_of_lt_of_le (div_pos hd (pow_pos (Real.sqrt_pos.mpr hnR) _)) (hmargin i))
    have hs := signed_product_of_M_margin n hn1 (nodes i) hDn (hM i)
    have hDG : 0 < fullD n (nodes i) * fullG n (nodes i) := hs.2.trans_le hs.1
    exact ⟨hs.1, hs.2, actual_source_response_telescope n hn1 (nodes i)
      (hpos i).1 (hroot i).1 hDG⟩

private theorem compact_exclusion (K : Set ℝ) (hK : IsCompact K)
    (hzero : ∀ t ∈ K, sourceF t ≠ 0) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ K, originalJ n t ≠ 0 := by
  classical
  by_cases hKe : K.Nonempty
  · have hcont : ContinuousOn (fun t : ℝ => ‖sourceF (t : ℂ)‖) K :=
      ((source_coefficients.2.1.continuousOn).comp Complex.continuous_ofReal.continuousOn
        (fun _ _ => Set.mem_univ _)).norm
    obtain ⟨b0, hb0, hmin⟩ := hK.exists_forall_le' hcont
      (fun t ht => norm_pos_iff.mpr (hzero t ht))
    obtain ⟨r, hr, hmax⟩ := hK.exists_isMaxOn hKe continuous_abs.continuousOn
    let R : ℝ := max 1 |r|
    have hR : 1 ≤ R := le_max_left _ _
    obtain ⟨k, hk⟩ := exists_nat_gt (2 * weightedNorm sourceA 2 R / b0)
    refine ⟨max 1 k, ?_⟩
    intro n hn t ht hnode
    have hn1 : 1 ≤ n := (le_max_left _ _).trans hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hkn : (k : ℝ) ≤ n := by exact_mod_cast ((le_max_right 1 k).trans hn)
    have hcrit : 2 * weightedNorm sourceA 2 R < (n : ℝ) * b0 :=
      (div_lt_iff₀ hb0).mp (hk.trans_le hkn)
    have herr : 2 / (n : ℝ) * weightedNorm sourceA 2 R < b0 := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ hnR]
      nlinarith
    have htR : ‖(t : ℂ)‖ ≤ R := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact (hmax ht).trans (le_max_right _ _)
    have ha := source_uniform_approximation n hn1 R hR t htR
    rw [source_eval, hnode, Complex.ofReal_zero, zero_sub, norm_neg] at ha
    exact (not_lt_of_ge (hmin t ht)) (ha.trans_lt herr)
  · refine ⟨0, ?_⟩
    intro n hn t ht
    exact False.elim (hKe ⟨t, ht⟩)

private theorem source_at_zero : sourceF (0 : ℂ) = 1 := by
  have h := source_coefficients.2.2.2 (0 : ℂ)
  have hs : HasSum (fun j => sourceA j * (0 : ℂ) ^ j) (sourceA 0) := by
    simpa only [smul_eq_mul, mul_comm] using
      (HasSum.hasSum_at_zero (𝕜 := ℂ) sourceA)
  simpa [sourceA, source_theta_coefficient_zero] using h.unique hs

private theorem source_polynomial_at_zero (n : ℕ) :
    (sourcePolynomial n).eval (0 : ℂ) = 1 := by
  classical
  rw [source_coefficients.2.2.1]
  simp only [coefficientPolynomial, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
  rw [Finset.sum_eq_single 0]
  · simp [sourceA, source_theta_coefficient_zero]
  · intro j hj hj0
    simp [zero_pow hj0]
  · simp

private theorem source_order_finite (c : ℂ) : analyticOrderAt sourceF c ≠ ⊤ := by
  apply source_coefficients.2.1.analyticOrderAt_ne_top_of_isPreconnected
    isPreconnected_univ (Set.mem_univ (0 : ℂ)) (Set.mem_univ c)
  rw [(source_coefficients.2.1 0 (Set.mem_univ _)).analyticOrderAt_eq_zero.mpr
    (by rw [source_at_zero]; norm_num)]
  exact ENat.zero_ne_top

private theorem source_zero_preparation (c : ℝ) (hc : 0 < c)
    (hz : sourceF (c : ℂ) = 0) :
    ∃ m : ℕ, 1 ≤ m ∧ IsExactRealOrder sourceF c m ∧
      ∃ delta : ℝ, IsolatingDisk sourceF c delta := by
  let m := analyticOrderNatAt sourceF (c : ℂ)
  have hmcast : analyticOrderAt sourceF (c : ℂ) = (m : ℕ∞) :=
    (Nat.cast_analyticOrderNatAt (source_order_finite c)).symm
  have hm : 1 ≤ m := by
    by_contra h
    have hm0 : m = 0 := by omega
    rw [hm0, Nat.cast_zero] at hmcast
    exact ((source_coefficients.2.1 c (Set.mem_univ _)).analyticOrderAt_eq_zero.mp hmcast) hz
  have ho := (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero
    (source_coefficients.2.1 c (Set.mem_univ _))).mp hmcast
  have hpunct : ∀ᶠ z in 𝓝[≠] (c : ℂ), sourceF z ≠ 0 := by
    apply (source_coefficients.2.1 c (Set.mem_univ _)).eventually_eq_zero_or_eventually_ne_zero.resolve_left
    intro h
    exact source_order_finite c (analyticOrderAt_eq_top.mpr h)
  rw [eventually_nhdsWithin_iff] at hpunct
  obtain ⟨eps, heps, hball⟩ := Metric.eventually_nhds_iff.mp hpunct
  refine ⟨m, hm, ⟨ho.2, ho.1⟩, eps / 2, by positivity, ?_, ?_⟩
  · intro z hz hne
    exact hball (by rw [dist_eq_norm]; linarith) hne
  · exact source_coefficients.2.1.mono (Set.subset_univ _)

private theorem source_finite_real_zeros (T : ℝ) :
    Set.Finite {t : ℝ | t ∈ Icc (0 : ℝ) T ∧ sourceF (t : ℂ) = 0} := by
  let K : Set ℂ := Complex.ofReal '' Icc (0 : ℝ) T
  have hK : IsCompact K := isCompact_Icc.image Complex.continuous_ofReal
  have hcod := source_coefficients.2.1.preimage_zero_mem_codiscrete
    (by rw [source_at_zero]; norm_num : sourceF (0 : ℂ) ≠ 0)
  have hfinite : (K \ sourceF ⁻¹' ({0}ᶜ : Set ℂ)).Finite :=
    hK.finite_sdiff_of_mem_codiscreteWithin
      ((Filter.codiscreteWithin_mono (Set.subset_univ K)) hcod)
  have hpre := Set.Finite.preimage Complex.ofReal_injective.injOn hfinite
  apply hpre.subset
  intro t ht
  exact ⟨⟨t, ht.1, rfl⟩, by simpa using ht.2⟩

/-- Complete public target with its original quantifier order and source node premise. -/
def FixedWindowConclusion : Prop :=
  (0 < fullZ ∧ 0 < 2 / fullZ ∧ ∀ z, sourceF z = (2 / (fullZ : ℂ)) * rawF z) ∧
  (∀ T : ℝ, 0 < T → ∃ n0 : ℕ, ∀ n ≥ n0, 1 ≤ n ∧ ∀ t : ℝ,
    0 < t → t ≤ T → originalJ n t = 0 →
      fullD n t * fullG n t ≥ fullD n t ^ 2 / 2 ∧
      fullD n t ^ 2 / 2 > 0 ∧ NodeResponse n t) ∧
  (∀ t0 : ℝ, 0 < t0 → sourceF t0 = 0 → ∀ m : ℕ, 1 ≤ m →
    IsExactRealOrder sourceF t0 m → ∀ delta : ℝ, IsolatingDisk sourceF t0 delta →
      LocalConclusion t0 delta m)

theorem actual_source_jensen_fixed_window : FixedWindowConclusion := by
  classical
  refine ⟨source_normalization, ?_, ?_⟩
  · intro T hT
    let Z : Set ℝ := {t ∈ Icc (0 : ℝ) T | sourceF (t : ℂ) = 0}
    have hZfinite : Z.Finite := source_finite_real_zeros T
    letI : Fintype Z := hZfinite.fintype
    have hcpos (c : Z) : 0 < (c : ℝ) := by
      have hnonneg : 0 ≤ (c : ℝ) := c.property.1.1
      have hne : (c : ℝ) ≠ 0 := by
        intro he
        have hz := c.property.2
        rw [he, Complex.ofReal_zero, source_at_zero] at hz
        exact one_ne_zero hz
      exact lt_of_le_of_ne hnonneg (Ne.symm hne)
    have hprep (c : Z) := source_zero_preparation c (hcpos c) c.property.2
    choose m hm ho delta hi using hprep
    have hlocal (c : Z) := local_complete c (delta c) (m c) (hcpos c) (hm c) (ho c) (hi c)
    choose C d hC hd N hN using hlocal
    let U : Set ℝ := ⋃ c : Z, ball (c : ℝ) (delta c)
    let K : Set ℝ := Icc (0 : ℝ) T \ U
    have hUopen : IsOpen U := isOpen_iUnion (fun _ => isOpen_ball)
    have hK : IsCompact K := isCompact_Icc.diff hUopen
    have hKzero : ∀ t ∈ K, sourceF (t : ℂ) ≠ 0 := by
      intro t ht hz
      let c : Z := ⟨t, ht.1, hz⟩
      apply ht.2
      exact Set.mem_iUnion.mpr ⟨c, mem_ball_self (hi c).1⟩
    obtain ⟨NK, hNK⟩ := compact_exclusion K hK hKzero
    refine ⟨max 1 (max NK (Finset.univ.sup N)), ?_⟩
    intro n hn
    have hn1 : 1 ≤ n := (le_max_left _ _).trans hn
    refine ⟨hn1, ?_⟩
    intro t ht htT hnode
    have htU : t ∈ U := by
      by_contra hnot
      exact hNK n ((le_max_left _ _).trans ((le_max_right _ _).trans hn)) t
        ⟨⟨ht.le, htT⟩, hnot⟩ hnode
    obtain ⟨c, htc⟩ := Set.mem_iUnion.mp htU
    have hNc : N c ≤ n :=
      (Finset.le_sup (f := N) (Finset.mem_univ c)).trans
        ((le_max_right _ _).trans ((le_max_right _ _).trans hn))
    obtain ⟨_, hcount, hboundary, nodes, hinj, hpos, hroot, herr, hmargin, hM,
      hocc, hcount1, hfac, hsigned⟩ := hN c n hNc
    have hP : sourcePolynomial n ≠ 0 := by
      intro he
      have hz := source_polynomial_at_zero n
      rw [he, Polynomial.eval_zero] at hz
      exact zero_ne_one hz
    have hPt : (sourcePolynomial n).eval (t : ℂ) = 0 := by
      rw [source_eval, hnode, Complex.ofReal_zero]
    have hinside : ‖(t : ℂ) - (c : ℝ)‖ < delta c := by
      simpa only [mem_ball, Real.dist_eq, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs] using htc
    have hmem : (t : ℂ) ∈ (sourcePolynomial n).roots.filter
        (fun z : ℂ => ‖z - ((c : ℝ) : ℂ)‖ < delta c) :=
      Multiset.mem_filter.mpr ⟨(Polynomial.mem_roots hP).mpr hPt, hinside⟩
    rw [hocc] at hmem
    obtain ⟨i, _, hei⟩ := Multiset.mem_map.mp hmem
    have he : nodes i = t := Complex.ofReal_injective hei
    simpa only [he] using hsigned i
  · intro t0 ht0 hzero m hm ho delta hi
    exact local_complete t0 delta m ht0 hm ho hi

#print axioms actual_source_jensen_fixed_window

end D5.S3.Zeros.Jensen.ActualSourceJensenFixedWindow
