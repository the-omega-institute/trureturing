/- GID: D5/S3/Zeros/Jensen/ActualSourceJensenFixedWindow
   generality: I
   mirror-B: D5/B/S3/Zeros/Jensen/ActualSourceJensenFixedWindow
   mirror-E: none(waiver:source-fixed-window-consumer)
   anchors: [mathlib/module/Mathlib.MeasureTheory.Integral.CircleIntegral,
     mathlib/module/Mathlib.Analysis.Analytic.Order]
   utility: none
   digest: The unchanged all-mode source has a fixed-window signed derivative
     margin and an arbitrary-multiplicity retained-disk polynomial count. -/

import D5.S3.Zeros.Jensen.JensenHermiteScaling
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
open private original_moment_bridge
  from D5.S3.Zeros.Jensen.OriginalPrimalTailResponse

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
  ((sourcePolynomial n).roots.filter (fun z => ‖z - c‖ < delta)).card

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
    rw [sourceThetaDensity, abs_div, abs_of_pos hz,
      abs_of_pos (source_theta_gaussian_bound x).1, mul_div_right_comm]
    exact div_le_div_of_nonneg_right (source_theta_gaussian_bound x).2 hz.le
  have hseries := gaussian_even_moment_series hp hb
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro R hR
    simpa [sourceA, sourceThetaCoefficient, sourceThetaMoment, evenMomentCoefficient,
      norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs] using (hseries.1 R hR).1
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
      sourceA, sourceThetaCoefficient, sourceThetaMoment, evenMomentCoefficient, mul_comm] using
        hseries.2.1.hasSum (by simp : z ∈ Metric.eball (0 : ℂ) ∞)

private theorem source_weighted_summable (L : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    Summable (fun j => ‖sourceA j‖ * (j : ℝ) ^ L * R ^ j) := by
  have hs := (source_coefficients.1 (Real.exp 1 * R) (by positivity)).mul_left (L.factorial : ℝ)
  apply hs.of_nonneg_of_le (fun j => by positivity)
  intro j
  have hp := Real.pow_div_factorial_le_exp (Nat.cast_nonneg j) L
  have hf : (0 : ℝ) < L.factorial := by exact_mod_cast Nat.factorial_pos L
  have hpoly : (j : ℝ) ^ L ≤ (L.factorial : ℝ) * Real.exp j := by
    exact (div_le_iff₀ hf).mp hp |>.trans_eq (mul_comm _ _)
  calc
    _ ≤ ‖sourceA j‖ * ((L.factorial : ℝ) * Real.exp j) * R ^ j :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpoly (norm_nonneg _))
        (pow_nonneg hR j)
    _ = _ := by rw [mul_pow, ← Real.exp_nat_mul]; push_cast; ring

private theorem hermite_derivative (m : ℕ) :
    (Polynomial.hermite (m + 1)).derivative = C (m + 1 : ℤ) * Polynomial.hermite m := by
  induction m with
  | zero => simp [Polynomial.hermite_one]
  | succ m ih =>
    rw [Polynomial.hermite_succ (m + 1), derivative_sub, derivative_mul,
      derivative_X, one_mul, ih, derivative_C_mul]
    calc
      _ = Polynomial.hermite (m + 1) +
          C (m + 1 : ℤ) * (X * Polynomial.hermite m - (Polynomial.hermite m).derivative) := by ring
      _ = _ := by rw [← Polynomial.hermite_succ]; push_cast; ring

private theorem hermite_recurrence (k : ℕ) :
    Polynomial.hermite (k + 2) = X * Polynomial.hermite (k + 1) -
      C (k + 1 : ℤ) * Polynomial.hermite k := by
  rw [Polynomial.hermite_succ (k + 1), hermite_derivative]

private theorem hermite_no_common_root (m : ℕ) (z : ℂ) :
    ¬ (aeval z (Polynomial.hermite m) = 0 ∧ aeval z (Polynomial.hermite (m + 1)) = 0) := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    cases m with
    | zero => simp
    | succ m =>
      intro ⟨hm, hp⟩
      have he := congrArg (aeval z) (hermite_recurrence m)
      simp only [map_sub, map_mul, aeval_X, aeval_C, hp, hm, mul_zero, zero_sub] at he
      have hc : (m + 1 : ℂ) ≠ 0 := by exact_mod_cast (show (m + 1 : ℕ) ≠ 0 by omega)
      have hprev : aeval z (Polynomial.hermite m) = 0 := by
        exact (mul_eq_zero.mp (neg_eq_zero.mp he.symm)).resolve_left hc
      exact ih m (by omega) ⟨hprev, hm⟩

private theorem hermite_root_real_simple (m : ℕ) (hm : 1 ≤ m) (z : ℂ)
    (hz : aeval z (Polynomial.hermite m) = 0) :
    z.im = 0 ∧ aeval z (Polynomial.hermite m).derivative ≠ 0 := by
  have hreal := PositiveThreeTermRootReality.finite_positive_three_term_zero_has_real_parameter
    m z (fun k => (k + 1 : ℕ)) (fun k => aeval z (Polynomial.hermite k))
    (fun k _ => by positivity) (by simp) (by simp [Polynomial.hermite_one])
    (fun k _ => by
      have h := congrArg (aeval z) (hermite_recurrence k)
      simpa only [map_sub, map_mul, aeval_X, aeval_C, Nat.cast_add, Nat.cast_one] using h) hz
  refine ⟨hreal, ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show m ≠ 0 by omega)
  rw [hermite_derivative, map_mul, aeval_C]
  apply mul_ne_zero (by exact_mod_cast (show (k + 1 : ℕ) ≠ 0 by omega))
  intro hprev
  exact hermite_no_common_root k z ⟨hprev, hz⟩

private theorem simple_cofactor (P : ℂ[X]) (a : ℂ) (ha : P.eval a = 0)
    (hd : P.derivative.eval a ≠ 0) :
    ∃ Q : ℂ[X], P = (X - C a) * Q ∧ Q.eval a ≠ 0 := by
  let Q := P /ₘ (X - C a)
  have he : P = (X - C a) * Q := (Polynomial.mul_divByMonic_eq_iff_isRoot.mpr ha).symm
  refine ⟨Q, he, ?_⟩
  have hder : P.derivative.eval a = Q.eval a := by
    rw [he, derivative_mul]
    simp
  exact hder ▸ hd

private theorem source_eval (n : ℕ) (t : ℝ) :
    (sourcePolynomial n).eval (t : ℂ) = (originalJ n t : ℂ) := by
  rw [sourcePolynomial, eval_comp]
  simp only [eval_mul, eval_C, eval_X, neg_one_mul]
  rw [← Complex.ofReal_neg, eval_map_apply, ← (original_moment_bridge n t).2.1]
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
  have hq20 := hiff.mp hd
  have hq0 : (sourceQ (n + 1)).eval (reflectedNode n t) ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hqv
    exact (mul_ne_zero (pow_ne_zero _ hxi.ne') hg) hqv.symm
  have hc := (hcouple hd).1
  have hcf : sourceCoupling (n + 1) (reflectedNode n t) * fullD n t ^ 2 =
      (reflectedNode n t) ^ 2 / n * (fullD n t * fullG n t) := by
    rw [hc]; field_simp [hd]; <;> ring
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
  rw [integral_div_const]
  unfold rawF cosineSquareTransform
  field_simp [Complex.ofReal_ne_zero.mpr hz.ne']
  <;> ring

private theorem real_interval_node (g : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hg : ContinuousOn g (Icc a b)) (hs : g a * g b < 0) :
    ∃ x ∈ Ioo a b, g x = 0 := by
  have hneA : g a ≠ 0 := fun h => by simpa [h] using hs
  have hneB : g b ≠ 0 := fun h => by simpa [h] using hs
  have hex : ∃ x ∈ Icc a b, g x = 0 := by
    rcases mul_neg_iff.mp hs with h | h
    · exact intermediate_value_Icc hab.le hg ⟨h.1.le, h.2.le⟩
    · exact intermediate_value_Icc' hab.le hg ⟨h.2.le, h.1.le⟩
  obtain ⟨x, hx, hzero⟩ := hex
  have hxa : x ≠ a := fun h => hneA (h ▸ hzero)
  have hxb : x ≠ b := fun h => hneB (h ▸ hzero)
  exact ⟨x, ⟨lt_of_le_of_ne hx.1 (Ne.symm hxa), lt_of_le_of_ne hx.2 hxb⟩, hzero⟩

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
    exact sub_nonneg.mp (nonneg_of_mul_nonneg_left hscaled hden)
  · positivity

private theorem source_operator_error (n K b : ℕ) (hn : 1 ≤ n) (R : ℝ) (hR : 1 ≤ R)
    (z : ℂ) (hz : ‖z‖ ≤ R) :
    ‖iteratedDeriv b (fun w => (sourcePolynomial n).eval w -
        ∑ r ∈ Finset.range (K + 1), ((-1 : ℂ) ^ r / (n : ℂ) ^ r) *
          correctionOperator r sourceF w) z‖ ≤
      2 / (n : ℝ) ^ (K + 1) * weightedNorm sourceA (2 * K + 2 + b) R := by
  simpa only [source_coefficients.2.2.1 n] using
    analytic_coefficient_operator_error sourceA sourceF source_coefficients.2.2.2
      source_weighted_summable n K b hn R hR z hz

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
    have hd := (((hasDerivAt_id z).const_mul (-4)).mul h1).sub
      (h2.const_mul ((4 * r + 2 : ℕ) : ℂ))
    rw [iteratedDeriv_succ, he, hd.deriv]
    simp only [← iteratedDeriv_succ, id_eq]
    convert_to -4 * iteratedDeriv (r + 2) sourceF z +
      (-4 * z) * iteratedDeriv (r + 3) sourceF z -
      ((4 * r + 2 : ℕ) : ℂ) * iteratedDeriv (r + 2) sourceF z = _ using 1
    · ring
    · push_cast; ring

private theorem sourceH_order (t0 : ℝ) (ht0 : 0 < t0) (m : ℕ) (hm : 2 ≤ m)
    (ho : IsExactRealOrder sourceF t0 m) : IsExactRealOrder sourceH t0 (m - 2) := by
  constructor
  · rw [sourceH_iterated, show m - 2 + 2 = m by omega,
      ho.2 (m - 2 + 1) (by omega), mul_zero, sub_zero]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr ht0.ne')) ho.1
  · intro k hk
    rw [sourceH_iterated, ho.2 (k + 2) (by omega), ho.2 (k + 1) (by omega)]
    ring

private theorem scaled_local_certificate (t0 delta : ℝ) (m : ℕ)
    (ht0 : 0 < t0) (hm : 1 ≤ m) (ho : IsExactRealOrder sourceF t0 m)
    (hi : IsolatingDisk sourceF t0 delta) :
    ∃ C d : ℝ, 0 < C ∧ 0 < d ∧ ∃ N : ℕ, ∀ n ≥ N, 1 ≤ n ∧
      ∃ nodes : Fin m → ℝ, Function.Injective nodes ∧
        (∀ i, 0 < nodes i ∧ |nodes i - t0| < delta) ∧
        (∀ i, originalJ n (nodes i) = 0 ∧
          (sourcePolynomial n).derivative.eval (nodes i) ≠ 0) ∧
        (∀ i, |nodes i - t0| ≤ C / Real.sqrt n) ∧
        (∀ i, d / (Real.sqrt n) ^ (m - 1) ≤ |fullD n (nodes i)|) ∧
        (∀ i, |fullM2 n (nodes i)| ≤ (n : ℝ) * |fullD n (nodes i)|) ∧
        (∀ z ∈ sphere (t0 : ℂ) delta,
          ‖(sourcePolynomial n).eval z - sourceF z‖ < ‖sourceF z‖) := by
  classical
  let sigma : ℝ := min (delta / 2) (min (t0 / 2) 1)
  let Rdisk : ℝ := max 1 (t0 + delta)
  have hdelta : 0 < delta := hi.1
  have hs : 0 < sigma := by dsimp [sigma]; positivity
  have hscaled := (source_scaled_estimates t0 sigma ht0 hs m).1 ho
  have hH := hermite_root_real_simple m hm
  have hMestimate : 2 ≤ m → ScaledFunctionEstimate sourceH sourceHA t0 sigma (m - 2) := by
    intro hm2
    exact (source_scaled_estimates t0 sigma ht0 hs (m - 2)).2
      (sourceH_order t0 ht0 m hm2 ho)
  have hIVT := real_interval_node
  -- REMAINING L4: use FTA, hermite_monic and natDegree_hermite to enumerate
  -- m roots. hH and one_lt_rootMultiplicity_iff_isRoot give multiplicity one.
  -- Choose disjoint intervals [r_i-eta,r_i+eta] and chi>0 on all intervals.
  -- Apply the value estimate on |u|≤q and the radius-one Cauchy estimate
  -- to its derivative on |u|≤q-1. The derivative error is ≤C/sqrt(n).
  -- Use hIVT on EACH interval; simplicity and injectivity follow from the
  -- derivative lower bound and disjoint intervals, with no nodes 0 access.
  -- REMAINING L5: sourceH has order m-2 for m≥2; apply its estimate to bound
  -- M by CM/(sqrt n)^(m-2). For m=1 use the direct coefficient norm of H.
  -- With d=|t0^m*f^(m)/m!|*chi/(2*t0), n>(CM/d)^2 pays every-node M/D.
  -- REMAINING L6: minimize |sourceF| on the ORIGINAL sphere radius delta;
  -- its positive minimum bdelta and 2*A_2(sourceA,Rdisk)/n pay the boundary.
  -- sigma controls only the local Taylor segment and never replaces delta.
  done

private theorem account_root_occurrences (P : ℂ[X]) (c : ℂ) (delta : ℝ) (m : ℕ)
    (hP : P ≠ 0) (nodes : Fin m → ℝ) (hinj : Function.Injective nodes)
    (hroot : ∀ i, P.eval (nodes i : ℂ) = 0)
    (hinside : ∀ i, ‖(nodes i : ℂ) - c‖ < delta)
    (hcard : (P.roots.filter (fun z => ‖z - c‖ < delta)).card = m) :
    P.roots.filter (fun z => ‖z - c‖ < delta) =
      (Finset.univ : Finset (Fin m)).val.map (fun i => (nodes i : ℂ)) := by
  classical
  let A := (Finset.univ : Finset (Fin m)).val.map (fun i => (nodes i : ℂ))
  have hAi : Function.Injective (fun i => (nodes i : ℂ)) :=
    Complex.ofReal_injective.comp hinj
  have hAn : A.Nodup := Multiset.Nodup.map hAi Finset.univ.nodup
  have hle : A ≤ P.roots.filter (fun z => ‖z - c‖ < delta) := by
    apply (Multiset.le_iff_subset hAn).mpr
    intro z hz
    obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hz
    exact Multiset.mem_filter.mpr ⟨(Polynomial.mem_roots hP).mpr (hroot i), hinside i⟩
  have hAc : A.card = m := by simp [A]
  exact (Multiset.eq_of_le_of_card_le hle (by rw [hcard, hAc])).symm

/-- The disk is the caller's original disk; the multiset equality records occurrences. -/
def LocalConclusion (t0 delta : ℝ) (m : ℕ) : Prop :=
  ∃ C0 d : ℝ, 0 < C0 ∧ 0 < d ∧ ∃ N : ℕ, ∀ n ≥ N, 1 ≤ n ∧
    retainedRootCount n t0 delta = m ∧
    (∀ z ∈ sphere (t0 : ℂ) delta, (sourcePolynomial n).eval z ≠ 0) ∧
    ∃ nodes : Fin m → ℝ, Function.Injective nodes ∧
      (∀ i, 0 < nodes i ∧ |nodes i - t0| < delta) ∧
      (∀ i, originalJ n (nodes i) = 0 ∧
        (sourcePolynomial n).eval (nodes i) = 0 ∧
        (sourcePolynomial n).derivative.eval (nodes i) ≠ 0) ∧
      (∀ i, |nodes i - t0| ≤ C0 / Real.sqrt n) ∧
      (∀ i, d / (Real.sqrt n) ^ (m - 1) ≤ |fullD n (nodes i)|) ∧
      (∀ i, |fullM2 n (nodes i)| ≤ (n : ℝ) * |fullD n (nodes i)|) ∧
      ((sourcePolynomial n).roots.filter (fun z => ‖z - t0‖ < delta) =
        (Finset.univ : Finset (Fin m)).val.map (fun i => (nodes i : ℂ))) ∧
      (∀ i, ((sourcePolynomial n).roots.filter
        (fun z => ‖z - t0‖ < delta)).count (nodes i) = 1) ∧
      (∀ i, ∃ Q : ℂ[X], sourcePolynomial n = (X - C (nodes i : ℂ)) * Q ∧ Q.eval (nodes i) ≠ 0) ∧
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
    have hZclosed : IsClosed Z := isClosed_Icc.inter
      ((source_coefficients.2.1.continuousOn.continuous_of_univ).comp
        Complex.continuous_ofReal).isClosed_preimage isClosed_singleton
    have hZcompact : IsCompact Z := isCompact_Icc.of_isClosed_subset hZclosed
      (fun t ht => ht.1)
    have hlocal := local_complete
    have hexclude := compact_exclusion
    -- REMAINING W2: sourceF(0)=1 excludes the locally zero branch by the
    -- identity principle. Analytic isolation makes Z a finite discrete set.
    -- For each c∈Z choose an isolating disk; local_complete supplies its
    -- threshold and all occurrences. Take the finite maximum of thresholds.
    -- K=Icc 0 T minus the open real disk interiors is compact and zero-free;
    -- hexclude excludes every other ACTUAL node. For a node inside a disk,
    -- its membership in the filtered root multiset and the occurrence equality
    -- identify the corresponding nodes i; transport its signed NodeResponse.
    -- When Z is empty, hexclude alone gives the same universal statement.
    done
  · intro t0 ht0 hzero m hm ho delta hi
    exact local_complete t0 delta m ht0 hm ho hi

#print axioms actual_source_jensen_fixed_window

end D5.S3.Zeros.Jensen.ActualSourceJensenFixedWindow
