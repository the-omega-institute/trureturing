/- GID: D5/S1/Recurrence/Residue/OEISA189733DenominatorConjecture
   generality: I
   mirror-B: D5/B/S1/Recurrence/Residue/OEISA189733DenominatorConjecture
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.Algebra.Polynomial.Derivative]
   utility: none
   digest: The literal Curtz triangle has the six conjectured reduced denominators. -/

import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Finite polynomial moments of the literal OEIS triangle. -/

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Recurrence.Residue.OEISA189733DenominatorConjecture

open Polynomial

/-- The source triangle, indexed by row and distance from the diagonal. -/
def triangle : ℕ → ℕ → ℚ
  | _, 0 => 0
  | m, 1 => (-1) ^ m / (m + 1)
  | m, k + 2 => triangle m (k + 1) + triangle (m + 1) k
termination_by _ k => k

/-- The rational polynomials associated with the triangle recursion. -/
private def q : ℕ → ℚ[X]
  | 0 => 0
  | 1 => 1
  | n + 2 => q (n + 1) - X * q n

private def moment (m : ℕ) : ℚ[X] →ₗ[ℚ] ℚ where
  toFun p := p.sum fun i a => a / (m + i + 1 : ℚ)
  map_add' p r := by
    apply Polynomial.sum_add_index
    · intro i; simp
    · intro i a b; exact add_div _ _ _
  map_smul' c p := by
    change (c • p).sum _ = c * p.sum _
    rw [Polynomial.sum_smul_index]
    · simp only [Polynomial.sum_def, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp [mul_div_assoc]
    · intro i; simp

private theorem moment_monomial (m n : ℕ) (a : ℚ) :
    moment m (monomial n a) = a / (m + n + 1 : ℚ) := by
  simp [moment]

private theorem moment_x_mul (m : ℕ) (p : ℚ[X]) :
    moment m (X * p) = moment (m + 1) p := by
  induction p using Polynomial.induction_on' with
  | add p r hp hr => simp [mul_add, hp, hr]
  | monomial n a =>
      rw [X_mul_monomial, moment_monomial, moment_monomial]
      push_cast
      congr 1
      ring

private theorem triangle_moment (m k : ℕ) :
    triangle m k = (-1) ^ m * moment m (q k) := by
  induction k using Nat.twoStepInduction generalizing m with
  | zero => simp [triangle, q]
  | one =>
      rw [show q 1 = monomial 0 1 by simp [q], moment_monomial]
      simp [triangle, div_eq_mul_inv]
  | more k ih ih' =>
      rw [triangle, q, map_sub, moment_x_mul, ih', ih, pow_succ]
      ring

#print axioms triangle_moment

private def l : ℕ → ℚ[X]
  | 0 => C 2
  | 1 => 1
  | n + 2 => l (n + 1) - X * l n

private theorem l_q (n : ℕ) : l (n + 1) = q (n + 1) - C 2 * X * q n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [l, q]
  | one => simp [l, q]
  | more n ih ih' =>
      rw [show n + 2 + 1 = (n + 1) + 2 by omega, l, ih', ih]
      simp only [q]
      ring

private theorem derivative_l (n : ℕ) :
    derivative (l (n + 1)) = C (-(n + 1 : ℚ)) * q n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [l, q]
  | one => norm_num [l, q, map_ofNat]
  | more n ih ih' =>
      rw [show n + 2 + 1 = (n + 1) + 2 by omega, l, map_sub,
        derivative_mul, ih', derivative_X, one_mul, ih, l_q, q]
      push_cast
      simp only [map_neg, map_add, map_one, map_ofNat]
      ring

private theorem moment_derivative (p : ℚ[X]) :
    moment 0 (derivative p) = p.eval 1 - p.eval 0 := by
  induction p using Polynomial.induction_on' with
  | add p r hp hr => simp only [map_add, eval_add, hp, hr]; ring
  | monomial n a =>
      cases n with
      | zero => simp [monomial_zero_left]
      | succ n =>
          rw [derivative_monomial_succ, moment_monomial]
          simp only [eval_monomial, one_pow, mul_one, pow_succ,
            mul_zero, sub_zero, Nat.cast_zero, zero_add]
          exact mul_div_cancel_right₀ a (by positivity)

private theorem l_eval_zero (n : ℕ) : (l (n + 1)).eval 0 = 1 := by
  induction n with
  | zero => simp [l]
  | succ n ih => simpa [l] using ih

private theorem triangle_zero (n : ℕ) :
    triangle 0 n = (1 - (l (n + 1)).eval 1) / (n + 1 : ℚ) := by
  have h := moment_derivative (l (n + 1))
  rw [derivative_l, ← smul_eq_C_mul, map_smul, l_eval_zero] at h
  rw [triangle_moment]
  simp only [pow_zero, one_mul, smul_eq_mul] at h ⊢
  apply (eq_div_iff (by positivity : (n + 1 : ℚ) ≠ 0)).mpr
  linear_combination -h

private theorem l_eval_step (n : ℕ) :
    (l (n + 2)).eval 1 = (l (n + 1)).eval 1 - (l n).eval 1 := by
  simp [l]

private theorem l_eval_six (n : ℕ) : (l (n + 6)).eval 1 = (l n).eval 1 := by
  have h0 := l_eval_step n
  have h1 := l_eval_step (n + 1)
  have h3 := l_eval_step (n + 3)
  have h4 := l_eval_step (n + 4)
  simp only [Nat.add_assoc, Nat.reduceAdd] at h1 h3 h4
  linear_combination h4 + h3 - h1 - h0

private theorem l_eval_period (k r : ℕ) : (l (6 * k + r)).eval 1 = (l r).eval 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [show 6 * (k + 1) + r = (6 * k + r) + 6 by omega, l_eval_six, ih]

private theorem triangle_six (k : ℕ) :
    triangle 0 (6 * k) = 0 ∧
    triangle 0 (6 * k + 1) = 1 / (3 * k + 1 : ℚ) ∧
    triangle 0 (6 * k + 2) = 1 / (2 * k + 1 : ℚ) ∧
    triangle 0 (6 * k + 3) = 1 / (3 * k + 2 : ℚ) ∧
    triangle 0 (6 * k + 4) = 0 ∧
    triangle 0 (6 * k + 5) = -(1 / (6 * k + 6 : ℚ)) := by
  have hv (r : ℕ) : triangle 0 (6 * k + r) =
      (1 - (l (r + 1)).eval 1) / (6 * k + r + 1 : ℚ) := by
    rw [triangle_zero, Nat.add_assoc, l_eval_period]
    push_cast
    rfl
  have h0 := hv 0
  have h1 := hv 1
  have h2 := hv 2
  have h3 := hv 3
  have h4 := hv 4
  have h5 := hv 5
  norm_num [l] at h0 h1 h2 h3 h4 h5
  refine ⟨h0, ?_, ?_, ?_, h4, ?_⟩
  · rw [h1]; field_simp; ring
  · rw [h2]; field_simp; ring
  · rw [h3]; field_simp; ring
  · rw [h5]; ring

/-- Reduced denominators of the zeroth row, including denominator one for zero. -/
def a (n : ℕ) : ℕ := (triangle 0 n).den

/-- Paul Curtz's six-residue denominator conjecture, without an index cutoff. -/
theorem result (k : ℕ) :
    (a (6 * k), a (6 * k + 1), a (6 * k + 2),
      a (6 * k + 3), a (6 * k + 4), a (6 * k + 5)) =
    (1, 3 * k + 1, 2 * k + 1, 3 * k + 2, 1, 6 * k + 6) := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := triangle_six k
  simp only [a, h0, h1, h2, h3, h4, h5, Rat.den_zero, Rat.den_neg_eq_den, one_div]
  have hd (d : ℕ) (h : 0 < d) : (1 / (d : ℚ)).den = d := by
    simpa only [one_div] using Rat.inv_natCast_den_of_pos h
  have hd1 := hd (3 * k + 1) (by omega)
  have hd2 := hd (2 * k + 1) (by omega)
  have hd3 := hd (3 * k + 2) (by omega)
  have hd5 := hd (6 * k + 6) (by omega)
  push_cast at hd1 hd2 hd3 hd5
  rw [← one_div, ← one_div, ← one_div, ← one_div, hd1, hd2, hd3, hd5]

#print axioms result

end D5.S1.Recurrence.Residue.OEISA189733DenominatorConjecture
