/- GID: D5/S1/Depth/ContinuedFractions/ODorneyPadeJunctionRefutation
   generality: I
   mirror-B: D5/B/S1/Depth/ContinuedFractions/ODorneyPadeJunctionRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Determinant.Basic]
   utility: kind=certified-instance; basis=refutes=gid:D5/S1/Depth/ContinuedFractions/ODorneyPadeJunctionRefutation.claim; result=D5/S1/Depth/ContinuedFractions/ODorneyPadeJunctionRefutation.result; claim=D5/S1/Depth/ContinuedFractions/ODorneyPadeJunctionRefutation.claim
   digest: O'Dorney's junction determinant vanishes at k = 5, i = 4 and a = b = 3. -/

import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! The one-entry Toeplitz determinant in O'Dorney's Conjecture 4.7. -/

namespace D5.S1.Depth.ContinuedFractions.ODorneyPadeJunctionRefutation

open Polynomial

private def discriminant (a b : ℤ) : ℝ := (a : ℝ) ^ 2 + 4 * (b : ℝ)

private noncomputable def alpha (a b : ℤ) : ℝ :=
  ((a : ℝ) + Real.sqrt (discriminant a b)) / 2

private noncomputable def quadratic (a b : ℤ) : ℝ[X] :=
  X ^ 2 - C (a : ℝ) * X - C (b : ℝ)

private noncomputable def beta (a b : ℤ) (i : ℕ) (j : ℤ) : ℝ :=
  if 0 ≤ j ∧ j ≤ 2 * (i : ℤ) then
    (quadratic a b ^ (i - 1) * (X - C (alpha a b)) ^ 2).coeff (2 * i - j.toNat)
  else 0

private noncomputable def upsilon (a b : ℤ) (k i : ℕ) : ℝ :=
  Matrix.det (fun r c : Fin (k - i) => beta a b i ((i : ℤ) + (c.val : ℤ) - (r.val : ℤ))
    : Matrix (Fin (k - i)) (Fin (k - i)) ℝ)

/-- The determinant implication of Conjecture 4.7 in arXiv:2611.01029v1. -/
def claim : Prop :=
  ∀ (a b : ℤ) (k i : ℕ), a ≠ 0 → b ≠ 0 → 0 < discriminant a b →
    1 ≤ i → i < k → upsilon a b k i = 0 → k = 4 ∧ i = 3 ∧ a ^ 2 = b

private theorem coefficient_four (t : ℝ) :
    (quadratic 3 3 ^ 3 * (X - C t) ^ 2).coeff 4 = -54 - 54 * t + 18 * t ^ 2 := by
  have hcube : quadratic 3 3 ^ 3 =
      X ^ 6 + C (-9) * X ^ 5 + C 18 * X ^ 4 + C 27 * X ^ 3 +
        C (-54) * X ^ 2 + C (-81) * X ^ 1 + C (-27) * X ^ 0 := by
    simp only [quadratic, Int.cast_ofNat, map_neg, map_ofNat, pow_one, pow_zero, mul_one]
    ring
  have hweight : quadratic 3 3 ^ 3 * (X - C t) ^ 2 =
      quadratic 3 3 ^ 3 * X ^ 2 - C (2 * t) * (quadratic 3 3 ^ 3 * X ^ 1) +
        C (t ^ 2) * quadratic 3 3 ^ 3 := by
    simp only [map_mul, map_ofNat, map_pow, pow_one]
    ring
  rw [hweight]
  simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_mul_X_pow']
  rw [hcube]
  simp only [coeff_add, coeff_C_mul_X_pow, coeff_X_pow]
  norm_num <;> ring

private theorem quadratic_at_root : (quadratic 3 3).eval (alpha 3 3) = 0 := by
  have hs := Real.sq_sqrt (show 0 ≤ (21 : ℝ) by norm_num)
  have hD : discriminant 3 3 = 21 := by norm_num [discriminant]
  simp only [quadratic, eval_sub, eval_mul, eval_pow, eval_X, eval_C, Int.cast_ofNat, alpha, hD]
  calc
    _ = ((Real.sqrt 21) ^ 2 - 21) / 4 := by ring
    _ = 0 := by rw [hs]; norm_num

/-- At \(a=b=3, k=5, i=4\) the determinant is zero outside the claimed exception. -/
theorem result : ¬ claim := by
  intro h
  have hD : 0 < discriminant 3 3 := by norm_num [discriminant]
  have hdet : upsilon 3 3 5 4 = 0 := by
    let A : Matrix (Fin 1) (Fin 1) ℝ :=
      fun r c => beta 3 3 4 (4 + (c.val : ℤ) - (r.val : ℤ))
    change A.det = 0
    refine (Matrix.det_fin_one A).trans ?_
    change beta 3 3 4 4 = 0
    have hbeta : beta 3 3 4 4 = (quadratic 3 3 ^ 3 * (X - C (alpha 3 3)) ^ 2).coeff 4 := by
      norm_num [beta]
    rw [hbeta, coefficient_four]
    have hroot := quadratic_at_root
    simp only [quadratic, eval_sub, eval_mul, eval_pow, eval_X, eval_C, Int.cast_ofNat] at hroot
    calc
      _ = 18 * ((alpha 3 3) ^ 2 - 3 * alpha 3 3 - 3) := by ring
      _ = 0 := by rw [hroot, mul_zero]
  have hexception := h 3 3 5 4 (by norm_num) (by norm_num) hD (by decide) (by decide) hdet
  exact (by decide : (5 : ℕ) ≠ 4) hexception.1

end D5.S1.Depth.ContinuedFractions.ODorneyPadeJunctionRefutation
