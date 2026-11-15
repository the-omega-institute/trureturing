/- GID: D5/S3/Combinatorics/BinomialBases/PascalHadamardPositivityRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/BinomialBases/PascalHadamardPositivityRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Determinant.Basic, mathlib/module/Mathlib.Analysis.SpecialFunctions.Pow.Real]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/BinomialBases/PascalHadamardPositivityRefutation.claim; result=D5/S3/Combinatorics/BinomialBases/PascalHadamardPositivityRefutation.result; claim=D5/S3/Combinatorics/BinomialBases/PascalHadamardPositivityRefutation.claim
   digest: A strictly separated Pascal minor has negative determinant at real exponent one tenth, refuting the original MO515594 positivity assertion. -/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
The original question of VSP, MathOverflow 515594, revision 1
(24043C19-8B17-4527-819F-D0DAEA1E8F86), asks the universal assertion in `claim`.
Source: https://mathoverflow.net/questions/515594
Adapted from VSP's question under https://creativecommons.org/licenses/by-sa/4.0/;
the adaptation encodes its natural indices and real powers and supplies an exact refutation.
The later appended question for real `r > 1` remains outside this claim.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.BinomialBases.PascalHadamardPositivityRefutation

noncomputable section

/-- The complete first question from MO515594, with all natural indices and strict separation. -/
def claim : Prop :=
  ∀ (n k : ℕ) (alpha beta : Fin k → ℕ) (r : ℝ),
    0 < r →
    (∀ i j : Fin k, i < j → alpha i < alpha j) →
    (∀ i j : Fin k, i < j → beta i < beta j) →
    (∀ i : Fin k, alpha i ≤ n) →
    (∀ i : Fin k, beta i ≤ n) →
    (∀ i j : Fin k, beta j < alpha i) →
    Matrix.det (Matrix.of fun i j => ((Nat.choose (alpha i) (beta j) : ℕ) : ℝ) ^ r) > 0

private def witnessAlpha : Fin 3 → ℕ := ![3, 4, 5]
private def witnessBeta : Fin 3 → ℕ := ![0, 1, 2]

private lemma witness_det_formula :
    Matrix.det (Matrix.of fun i j : Fin 3 =>
      ((Nat.choose (witnessAlpha i) (witnessBeta j) : ℕ) : ℝ) ^ (1 / 10 : ℝ)) =
      (40 : ℝ) ^ (1 / 10 : ℝ) + (18 : ℝ) ^ (1 / 10 : ℝ) +
        (15 : ℝ) ^ (1 / 10 : ℝ) - 2 * (30 : ℝ) ^ (1 / 10 : ℝ) -
        (12 : ℝ) ^ (1 / 10 : ℝ) := by
  rw [Matrix.det_fin_three]
  norm_num [Matrix.of_apply, witnessAlpha, witnessBeta, Nat.choose]
  rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (by norm_num : (0 : ℝ) ≤ 10),
    ← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 6) (by norm_num : (0 : ℝ) ≤ 5),
    ← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) (by norm_num : (0 : ℝ) ≤ 10),
    ← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) (by norm_num : (0 : ℝ) ≤ 6),
    ← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) (by norm_num : (0 : ℝ) ≤ 5),
    ← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) (by norm_num : (0 : ℝ) ≤ 4)]
  ring_nf

private lemma root_upper (a q : ℝ) (ha : 0 ≤ a) (hq : 0 ≤ q) (h : a < q ^ 10) :
    a ^ (1 / 10 : ℝ) < q := by
  apply lt_of_pow_lt_pow_left₀ 10 hq
  have hroot : (a ^ (1 / 10 : ℝ)) ^ (10 : ℕ) = a := by
    convert Real.rpow_inv_natCast_pow ha (by decide : (10 : ℕ) ≠ 0) using 1 <;> norm_num
  rw [hroot]
  exact h

private lemma root_lower (a q : ℝ) (ha : 0 ≤ a) (h : q ^ 10 < a) :
    q < a ^ (1 / 10 : ℝ) := by
  apply lt_of_pow_lt_pow_left₀ 10 (Real.rpow_nonneg ha _)
  have hroot : (a ^ (1 / 10 : ℝ)) ^ (10 : ℕ) = a := by
    convert Real.rpow_inv_natCast_pow ha (by decide : (10 : ℕ) ≠ 0) using 1 <;> norm_num
  rw [hroot]
  exact h

private lemma witness_det_negative :
    Matrix.det (Matrix.of fun i j : Fin 3 =>
      ((Nat.choose (witnessAlpha i) (witnessBeta j) : ℕ) : ℝ) ^ (1 / 10 : ℝ)) < 0 := by
  rw [witness_det_formula]
  have h40 := root_upper 40 (1446126 / 1000000) (by norm_num) (by norm_num) (by norm_num)
  have h18 := root_upper 18 (1335142 / 1000000) (by norm_num) (by norm_num) (by norm_num)
  have h15 := root_upper 15 (1311020 / 1000000) (by norm_num) (by norm_num) (by norm_num)
  have h30 := root_lower 30 (1405115 / 1000000) (by norm_num) (by norm_num)
  have h12 := root_lower 12 (1282088 / 1000000) (by norm_num) (by norm_num)
  linarith

/-- The original universal strict-positivity assertion is false. -/
theorem result : ¬ claim := by
  intro h
  have hp := h 5 3 witnessAlpha witnessBeta (1 / 10) (by norm_num)
    (by intro i j hij; fin_cases i <;> fin_cases j <;> norm_num [witnessAlpha] at *)
    (by intro i j hij; fin_cases i <;> fin_cases j <;> norm_num [witnessBeta] at *)
    (by intro i; fin_cases i <;> norm_num [witnessAlpha])
    (by intro i; fin_cases i <;> norm_num [witnessBeta])
    (by intro i j; fin_cases i <;> fin_cases j <;> norm_num [witnessAlpha, witnessBeta])
  exact (not_lt_of_gt witness_det_negative) hp


end
end D5.S3.Combinatorics.BinomialBases.PascalHadamardPositivityRefutation
