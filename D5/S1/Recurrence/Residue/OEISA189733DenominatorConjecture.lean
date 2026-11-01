/- GID: D5/S1/Recurrence/Residue/OEISA189733DenominatorConjecture
   generality: I
   mirror-B: D5/B/S1/Recurrence/Residue/OEISA189733DenominatorConjecture
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.Algebra.Polynomial.Derivative, mathlib/module/Mathlib.Data.Rat.Lemmas]
   utility: none
   digest: The literal Curtz triangle has the six conjectured reduced denominators. -/

import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

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
def q : ℕ → ℚ[X]
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
      simp only [triangle, q]
      rw [← C_1]
      simp [moment, div_eq_mul_inv]
  | more k ih ih' =>
      rw [triangle, q, map_sub, moment_x_mul, ih', ih, pow_succ]
      ring

#print axioms triangle_moment

end D5.S1.Recurrence.Residue.OEISA189733DenominatorConjecture
