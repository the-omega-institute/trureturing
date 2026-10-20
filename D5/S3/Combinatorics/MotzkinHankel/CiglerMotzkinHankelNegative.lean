/- GID: D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelNegative
   generality: G
   mirror-B: D5/B/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelNegative
   mirror-E: none(waiver:integral-negative-index-determinants)
   anchors: []
   utility: none
   digest: Backwards orthogonal polynomials yield the first nonzero negative-index determinant. -/

import D5.S3.Combinatorics.MotzkinHankel.CiglerMotzkinHankelOrthogonal

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.MotzkinHankel.CiglerMotzkinHankelNegative

open Polynomial Finset CiglerMotzkinHankelDefs CiglerMotzkinHankelOrthogonal

noncomputable def backward : ℕ → Base[X]
  | 0 => C (sVar - tVar)
  | 1 => (X - C tVar) * backward 0 - 1
  | degree + 2 => (X - C tVar) * backward (degree + 1) - backward degree

theorem negative_determinants (size : ℕ) :
    (∀ gap : ℕ, 1 ≤ gap → gap < size →
      (Matrix.of fun row column : Fin size =>
        (if row.val < gap then backward (gap - 1 - row.val)
          else orthogonal (row.val - gap)).coeff column).det = 0) ∧
    (-1 : Base) ^ size * (Matrix.of fun row column : Fin size =>
      (backward (size - 1 - row.val)).coeff column).det =
      (-1 : Base) ^ (size + 1).choose 2 * (sVar - tVar) ^ size ∧
    (-1 : Base) ^ (size + 1).choose 2 * (sVar - tVar) ^ size ≠ 0 := by
  classical
  have coefficients : ∀ degree : ℕ,
      (∀ height : ℕ, degree < height → (backward degree).coeff height = 0) ∧
        (backward degree).coeff degree = sVar - tVar := by
    apply Nat.twoStepInduction
    · constructor
      · intro height height_gt
        simp [backward, coeff_C, show height ≠ 0 by omega]
      · simp [backward]
    · constructor
      · intro height height_gt
        cases height with
        | zero => omega
        | succ height =>
          simp [backward, sub_mul, coeff_X_mul, coeff_C, coeff_one,
            show height ≠ 0 by omega]
      · simp [backward, sub_mul, coeff_X_mul, coeff_one]
    · intro degree previous current
      constructor
      · intro height height_gt
        cases height with
        | zero => omega
        | succ height =>
          rw [backward, sub_mul, coeff_sub, coeff_sub, coeff_X_mul, coeff_C_mul,
            current.1 height (by omega), current.1 (height + 1) (by omega),
            previous.1 (height + 1) (by omega)]
          ring
      · rw [backward, sub_mul, coeff_sub, coeff_sub, coeff_X_mul, coeff_C_mul,
          current.2, current.1 (degree + 1 + 1) (by omega),
          previous.1 (degree + 1 + 1) (by omega)]
        ring
  have reversed : ∀ count : ℕ,
      (Matrix.of fun row column : Fin count =>
        (backward (count - 1 - row.val)).coeff column).det =
      (-1 : Base) ^ count.choose 2 * (sVar - tVar) ^ count := by
    intro count
    induction count with
    | zero => simp
    | succ count induction_hypothesis =>
      let matrix : Matrix (Fin (count + 1)) (Fin (count + 1)) Base :=
        Matrix.of fun row column => (backward (count - row.val)).coeff column
      have minor : matrix.submatrix (0 : Fin (count + 1)).succAbove
          (Fin.last count).succAbove =
          Matrix.of (fun row column : Fin count =>
            (backward (count - 1 - row.val)).coeff column) := by
        apply Matrix.ext
        intro row column
        simp only [Matrix.submatrix_apply, matrix, Matrix.of_apply,
          Fin.succAbove_zero, Fin.succAbove_last, Fin.val_succ, Fin.val_castSucc]
        rw [show count - (row.val + 1) = count - 1 - row.val by omega]
      change matrix.det = _
      rw [Matrix.det_succ_column matrix (Fin.last count), sum_eq_single 0]
      · simp only [Fin.val_zero, Fin.val_last, zero_add, matrix, Matrix.of_apply,
          Nat.sub_zero, (coefficients count).2]
        rw [minor, induction_hypothesis, Nat.choose_succ_succ, Nat.choose_one_right,
          pow_add, pow_succ]
        ring
      · intro row _ row_ne
        have row_positive : 0 < row.val := by
          have row_val_ne : row.val ≠ 0 := by
            intro equal
            apply row_ne
            exact Fin.ext equal
          omega
        simp only [matrix, Matrix.of_apply, Fin.val_last]
        rw [(coefficients (count - row.val)).1 count (by omega)]
        ring
      · simp
  have boundary_nonzero : sVar - tVar ≠ 0 := by
    intro equal
    have evaluation := congrArg
      (MvPolynomial.eval (fun index : Fin 2 => if index = 1 then (1 : ℤ) else 0)) equal
    norm_num [sVar, tVar] at evaluation
  constructor
  · intro gap gap_positive gap_lt
    let column : Fin size := ⟨size - 1, by omega⟩
    apply Matrix.det_eq_zero_of_column_eq_zero column
    intro row
    simp only [Matrix.of_apply]
    by_cases negative : row.val < gap
    · simp only [negative, if_true]
      exact (coefficients (gap - 1 - row.val)).1 column (by dsimp [column]; omega)
    · simp only [negative, if_false]
      apply coeff_eq_zero_of_natDegree_lt
      rw [(orthogonal_basis (row.val - gap)).1.natDegree_eq]
      dsimp [column]
      omega
  · constructor
    · rw [reversed, ← mul_assoc, ← pow_add, Nat.choose_succ_succ,
        Nat.choose_one_right]
    · exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
        (pow_ne_zero _ boundary_nonzero)

end D5.S3.Combinatorics.MotzkinHankel.CiglerMotzkinHankelNegative
