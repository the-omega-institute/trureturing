/- GID: D5/S3/Zeros/Jensen/JensenAnalyticCoefficientRemainder
   generality: G
   mirror-B: D5/B/S3/Zeros/Jensen/JensenAnalyticCoefficientRemainder
   mirror-E: none(waiver:source-fixed-window-consumer)
   anchors: [mathlib/module/Mathlib.Analysis.Complex.LocallyUniformLimit, mathlib/module/Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas]
   utility: none
   digest: Entire coefficient series identify every derivative of the actual finite correction remainder. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Zeros.Jensen.JensenFiniteCoefficientRemainder
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Zeros.Jensen.ActualSourceJensenFixedWindow

open scoped BigOperators Topology
open Polynomial Metric
open private D5.S3.Zeros.Jensen.ActualSourceJensenFixedWindow.elementary_falling_factorial
  D5.S3.Zeros.Jensen.ActualSourceJensenFixedWindow.bonferroni_residual_bound
  D5.S3.Zeros.Jensen.ActualSourceJensenFixedWindow.weighted_residual_bound
  from D5.S3.Zeros.Jensen.JensenFiniteCoefficientRemainder

def correctionOperator (r : ℕ) (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (2 * r + 1),
    (correctionCoeff r k : ℂ) * z ^ k * iteratedDeriv k F z

def weightedNorm (a : ℕ → ℂ) (L : ℕ) (R : ℝ) : ℝ :=
  ∑' j : ℕ, ‖a j‖ * (j : ℝ) ^ L * R ^ j

def coefficientPolynomial (a : ℕ → ℂ) (n : ℕ) : ℂ[X] :=
  ∑ j ∈ Finset.range (n + 1), C ((n.descFactorial j : ℂ) / (n : ℂ) ^ j * a j) * X ^ j

private theorem monomial_iterated (a : ℂ) (j b : ℕ) (z : ℂ) :
    iteratedDeriv b (fun w : ℂ => a * w ^ j) z =
      a * (j.descFactorial b : ℂ) * z ^ (j - b) := by
  simp [iteratedDeriv_const_mul_field, iteratedDeriv_pow, mul_assoc]

private theorem derivative_monomial (a : ℂ) (j b : ℕ) (z : ℂ) :
    deriv (fun w : ℂ => a * (j.descFactorial b : ℂ) * w ^ (j - b)) z =
      a * (j.descFactorial (b + 1) : ℂ) * z ^ (j - (b + 1)) := by
  have he : (fun w : ℂ => a * (j.descFactorial b : ℂ) * w ^ (j - b)) =
      iteratedDeriv b (fun w : ℂ => a * w ^ j) :=
    funext (fun w => (monomial_iterated a j b w).symm)
  rw [he, ← iteratedDeriv_succ, monomial_iterated]

private theorem derivative_term_bound (a : ℂ) (j b : ℕ) (R : ℝ) (hR : 1 ≤ R)
    (z : ℂ) (hz : ‖z‖ ≤ R) :
    ‖a * (j.descFactorial b : ℂ) * z ^ (j - b)‖ ≤
      ‖a‖ * (j : ℝ) ^ b * R ^ j := by
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_natCast]
  have hf : (j.descFactorial b : ℝ) ≤ (j : ℝ) ^ b := by
    exact_mod_cast Nat.descFactorial_le_pow j b
  have hp : ‖z‖ ^ (j - b) ≤ R ^ j :=
    (pow_le_pow_left₀ (norm_nonneg z) hz _).trans
      (pow_le_pow_right₀ hR (Nat.sub_le j b))
  exact mul_le_mul (mul_le_mul_of_nonneg_left hf (norm_nonneg a)) hp
    (by positivity) (by positivity)

private theorem coefficient_derivative_series (a : ℕ → ℂ) (F : ℂ → ℂ)
    (hseries : ∀ z, HasSum (fun j => a j * z ^ j) (F z))
    (hweighted : ∀ L R, 0 ≤ R → Summable (fun j => ‖a j‖ * (j : ℝ) ^ L * R ^ j))
    (b : ℕ) (z : ℂ) :
    HasSum (fun j => a j * (j.descFactorial b : ℂ) * z ^ (j - b))
      (iteratedDeriv b F z) := by
  induction b generalizing z with
  | zero => simpa using hseries z
  | succ b ih =>
    let R : ℝ := max 1 ‖z‖ + 1
    have hR : 1 ≤ R := by dsimp [R]; linarith [le_max_left (1 : ℝ) ‖z‖]
    have hz : z ∈ ball (0 : ℂ) R := by
      rw [mem_ball_zero_iff]
      dsimp [R]
      linarith [le_max_right (1 : ℝ) ‖z‖]
    have he : (fun w : ℂ => ∑' j, a j * (j.descFactorial b : ℂ) * w ^ (j - b)) =
        iteratedDeriv b F := funext (fun w => (ih w).tsum_eq)
    have hd := Complex.hasSum_deriv_of_summable_norm (hweighted b R (by linarith))
      (F := fun j w => a j * (j.descFactorial b : ℂ) * w ^ (j - b))
      (fun j => ((differentiable_const (a j * (j.descFactorial b : ℂ))).mul
        (differentiable_id.pow (j - b))).differentiableOn)
      isOpen_ball
      (fun j w hw => derivative_term_bound (a j) j b R hR w
        (le_of_lt (mem_ball_zero_iff.mp hw))) hz
    simpa only [derivative_monomial, he, ← iteratedDeriv_succ] using hd

private theorem correction_operator_series (a : ℕ → ℂ) (F : ℂ → ℂ)
    (hseries : ∀ z, HasSum (fun j => a j * z ^ j) (F z))
    (hweighted : ∀ L R, 0 ≤ R → Summable (fun j => ‖a j‖ * (j : ℝ) ^ L * R ^ j))
    (r : ℕ) (z : ℂ) :
    HasSum (fun j => (elementarySymmetric r j : ℂ) * a j * z ^ j)
      (correctionOperator r F z) := by
  have hs := hasSum_sum (s := Finset.range (2 * r + 1))
    (fun k _ => (coefficient_derivative_series a F hseries hweighted k z).mul_left
      ((correctionCoeff r k : ℂ) * z ^ k))
  change HasSum _ (correctionOperator r F z) at hs
  apply hs.congr_fun
  intro j
  have hterm (k : ℕ) :
      (correctionCoeff r k : ℂ) * z ^ k *
          (a j * (j.descFactorial k : ℂ) * z ^ (j - k)) =
        ((correctionCoeff r k : ℂ) * (j.descFactorial k : ℂ)) * (a j * z ^ j) := by
    by_cases hj : j < k
    · simp [Nat.descFactorial_of_lt hj]
    · calc
        _ = ((correctionCoeff r k : ℂ) * (j.descFactorial k : ℂ)) *
            (a j * (z ^ k * z ^ (j - k))) := by ring
        _ = _ := by rw [← pow_add, Nat.add_sub_of_le (by omega : k ≤ j)]
  simp_rw [hterm]
  rw [← Finset.sum_mul]
  have he : (∑ k ∈ Finset.range (2 * r + 1),
      (correctionCoeff r k : ℂ) * (j.descFactorial k : ℂ)) =
      (elementarySymmetric r j : ℂ) := by
    rw [D5.S3.Zeros.Jensen.ActualSourceJensenFixedWindow.elementary_falling_factorial]
    simp only [correctionSum, fallingReal]
    push_cast
    rfl
  rw [he]
  ring

private theorem polynomial_series (a : ℕ → ℂ) (n : ℕ) (z : ℂ) :
    HasSum (fun j => (n.descFactorial j : ℂ) / (n : ℂ) ^ j * a j * z ^ j)
      ((coefficientPolynomial a n).eval z) := by
  simp only [coefficientPolynomial, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
  apply hasSum_sum_of_ne_finset_zero
  intro j hj
  have hnj : n < j := by have := Finset.mem_range.not.mp hj; omega
  simp [Nat.descFactorial_of_lt hnj]

private theorem actual_error_series (a : ℕ → ℂ) (F : ℂ → ℂ)
    (hseries : ∀ z, HasSum (fun j => a j * z ^ j) (F z))
    (hweighted : ∀ L R, 0 ≤ R → Summable (fun j => ‖a j‖ * (j : ℝ) ^ L * R ^ j))
    (n K : ℕ) (z : ℂ) :
    HasSum (fun j => (bonferroniResidual n K j : ℂ) * a j * z ^ j)
      ((coefficientPolynomial a n).eval z -
        ∑ r ∈ Finset.range (K + 1), ((-1 : ℂ) ^ r / (n : ℂ) ^ r) *
          correctionOperator r F z) := by
  have hs := hasSum_sum (s := Finset.range (K + 1))
    (fun r _ => (correction_operator_series a F hseries hweighted r z).mul_left
      ((-1 : ℂ) ^ r / (n : ℂ) ^ r))
  apply ((polynomial_series a n z).sub hs).congr_fun
  intro j
  simp only [bonferroniResidual]
  push_cast
  rw [sub_mul, sub_mul, Finset.sum_mul, Finset.sum_mul]
  apply congrArg₂ (· - ·) rfl
  apply Finset.sum_congr rfl
  intro r _
  ring

private theorem residual_weighted_summable (a : ℕ → ℂ) (n K : ℕ) (hn : 1 ≤ n)
    (hweighted : ∀ L R, 0 ≤ R → Summable (fun j => ‖a j‖ * (j : ℝ) ^ L * R ^ j))
    (L : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    Summable (fun j => ‖(bonferroniResidual n K j : ℂ) * a j‖ *
      (j : ℝ) ^ L * R ^ j) := by
  have hs := (hweighted (2 * K + 2 + L) (max 1 R)
    (le_trans zero_le_one (le_max_left _ _))).mul_left (2 / (n : ℝ) ^ (K + 1))
  apply hs.of_nonneg_of_le (fun j => by positivity)
  intro j
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hp := pow_le_pow_left₀ hR (le_max_right 1 R) j
  have hb := D5.S3.Zeros.Jensen.ActualSourceJensenFixedWindow.bonferroni_residual_bound n K j hn
  calc
    _ ≤ (2 / (n : ℝ) ^ (K + 1) * (j : ℝ) ^ (2 * K + 2)) *
        ‖a j‖ * (j : ℝ) ^ L * (max 1 R) ^ j :=
      mul_le_mul (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hb (norm_nonneg _)) (by positivity)) hp
        (by positivity) (by positivity)
    _ = _ := by rw [pow_add]; ring

theorem analytic_coefficient_operator_error (a : ℕ → ℂ) (F : ℂ → ℂ)
    (hseries : ∀ z, HasSum (fun j => a j * z ^ j) (F z))
    (hweighted : ∀ L R, 0 ≤ R → Summable (fun j => ‖a j‖ * (j : ℝ) ^ L * R ^ j))
    (n K b : ℕ) (hn : 1 ≤ n) (R : ℝ) (hR : 1 ≤ R) (z : ℂ) (hz : ‖z‖ ≤ R) :
    ‖iteratedDeriv b (fun w => (coefficientPolynomial a n).eval w -
        ∑ r ∈ Finset.range (K + 1), ((-1 : ℂ) ^ r / (n : ℂ) ^ r) *
          correctionOperator r F w) z‖ ≤
      2 / (n : ℝ) ^ (K + 1) * weightedNorm a (2 * K + 2 + b) R := by
  have hs := coefficient_derivative_series (fun j => (bonferroniResidual n K j : ℂ) * a j)
    _ (actual_error_series a F hseries hweighted n K)
    (residual_weighted_summable a n K hn hweighted) b z
  have hnorm (j : ℕ) :
      ‖((bonferroniResidual n K j : ℂ) * a j) * (j.descFactorial b : ℂ) * z ^ (j - b)‖ ≤
        ‖a j‖ * |bonferroniResidual n K j| * (j.descFactorial b : ℝ) * R ^ (j - b) := by
    simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, Complex.norm_natCast]
    rw [mul_comm |bonferroniResidual n K j| ‖a j‖]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg z) hz _) (by positivity)
  have hmajor : Summable (fun j => ‖a j‖ * |bonferroniResidual n K j| *
      (j.descFactorial b : ℝ) * R ^ (j - b)) := by
    have ht := residual_weighted_summable a n K hn hweighted b R (by linarith)
    apply ht.of_nonneg_of_le (fun j => by positivity)
    intro j
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hf : (j.descFactorial b : ℝ) ≤ (j : ℝ) ^ b := by
      exact_mod_cast Nat.descFactorial_le_pow j b
    have hp := pow_le_pow_right₀ hR (Nat.sub_le j b)
    calc
      _ ≤ ‖a j‖ * |bonferroniResidual n K j| * (j : ℝ) ^ b * R ^ j :=
        mul_le_mul (mul_le_mul_of_nonneg_left hf (by positivity)) hp
          (by positivity) (by positivity)
      _ = _ := by ring
  exact (hs.norm_le_of_bounded hmajor.hasSum hnorm).trans
    (D5.S3.Zeros.Jensen.ActualSourceJensenFixedWindow.weighted_residual_bound
      a n K b R hn hR (hweighted _ _ (by linarith)))

#print axioms analytic_coefficient_operator_error

end D5.S3.Zeros.Jensen.ActualSourceJensenFixedWindow
