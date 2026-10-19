/- GID: D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelOrthogonal
   generality: G
   mirror-B: D5/B/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelOrthogonal
   mirror-E: none(waiver:integral-motzkin-orthogonal-basis)
   anchors: [mathlib/module/Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree]
   utility: none
   digest: Monic orthogonal polynomials give the inverse of the Motzkin path basis. -/

import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import D5.S3.Combinatorics.MotzkinHankel.CiglerMotzkinHankelTransfer

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.MotzkinHankel.CiglerMotzkinHankelOrthogonal

open Polynomial Finset CiglerMotzkinHankelDefs CiglerMotzkinHankelTransfer

noncomputable def orthogonal : ℕ → Base[X]
  | 0 => 1
  | 1 => X - C sVar
  | degree + 2 => (X - C tVar) * orthogonal (degree + 1) - orthogonal degree

theorem orthogonal_basis (length : ℕ) :
    (orthogonal length).IsMonicOfDegree length ∧
      (X : Base[X]) ^ length =
        ∑ height ∈ range (length + 1), C (motzkin length height) * orthogonal height := by
  classical
  have monic : ∀ degree : ℕ, (orthogonal degree).IsMonicOfDegree degree := by
    apply Nat.twoStepInduction
    · simp [orthogonal]
    · exact isMonicOfDegree_X_sub_one sVar
    · intro degree previous current
      rw [orthogonal]
      have product := (isMonicOfDegree_X_sub_one tVar).mul current
      have lower : (orthogonal degree).natDegree < 1 + (degree + 1) := by
        rw [previous.natDegree_eq]
        omega
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using product.sub lower
  have multiplication (height : ℕ) :
      (X : Base[X]) * orthogonal height =
        orthogonal (height + 1) + C (if height = 0 then sVar else tVar) *
          orthogonal height + (if height = 0 then 0 else orthogonal (height - 1)) := by
    cases height with
    | zero => simp [orthogonal]
    | succ height =>
      simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel, orthogonal]
      ring
  have down_shift (left right : ℕ → Base[X]) (bound : ℕ) :
      (∑ height ∈ range (bound + 1),
        (if height = 0 then 0 else left (height - 1)) * right height) =
      ∑ height ∈ range bound, left height * right (height + 1) := by
    rw [sum_range_succ']
    simp
  have step (length : ℕ) :
      (∑ height ∈ range (length + 2),
        C (motzkin (length + 1) height) * orthogonal height) =
      ∑ height ∈ range (length + 1),
        C (motzkin length height) * ((X : Base[X]) * orthogonal height) := by
    have last_zero : motzkin length (length + 1) = 0 :=
      (motzkin_triangle length).1 _ (by omega)
    have next_zero : motzkin length (length + 2) = 0 :=
      (motzkin_triangle length).1 _ (by omega)
    have incoming_down :
        (∑ height ∈ range (length + 2),
          C (if height = 0 then 0 else motzkin length (height - 1)) *
            orthogonal height) =
        ∑ height ∈ range (length + 1),
          C (motzkin length height) * orthogonal (height + 1) := by
      simpa only [apply_ite, map_zero] using
        down_shift (fun height => C (motzkin length height)) orthogonal (length + 1)
    have outgoing_down :
        (∑ height ∈ range (length + 1), C (motzkin length height) *
          (if height = 0 then 0 else orthogonal (height - 1))) =
        ∑ height ∈ range length, C (motzkin length (height + 1)) *
          orthogonal height := by
      simpa only [mul_comm] using
        down_shift orthogonal (fun height => C (motzkin length height)) length
    have horizontal :
        (∑ height ∈ range (length + 2),
          C ((if height = 0 then sVar else tVar) * motzkin length height) *
            orthogonal height) =
        ∑ height ∈ range (length + 1), C (motzkin length height) *
          (C (if height = 0 then sVar else tVar) * orthogonal height) := by
      rw [show length + 2 = (length + 1) + 1 by omega, sum_range_succ]
      simp only [last_zero, mul_zero, map_zero, zero_mul, add_zero]
      apply sum_congr rfl
      intro height _
      rw [C_mul]
      ring
    have incoming_up :
        (∑ height ∈ range (length + 2),
          C (motzkin length (height + 1)) * orthogonal height) =
        ∑ height ∈ range length, C (motzkin length (height + 1)) *
          orthogonal height := by
      rw [show length + 2 = (length + 1) + 1 by omega, sum_range_succ,
        sum_range_succ]
      simp [last_zero, next_zero]
    simp only [motzkin, map_add, add_mul, sum_add_distrib]
    rw [incoming_down, horizontal, incoming_up]
    simp_rw [multiplication, mul_add, sum_add_distrib]
    rw [outgoing_down]
  refine ⟨monic length, ?_⟩
  induction length with
  | zero => simp [motzkin, orthogonal]
  | succ length induction_hypothesis =>
    rw [pow_succ', induction_hypothesis, mul_sum]
    conv_lhs => arg 2; ext height; rw [mul_left_comm]
    exact (step length).symm

theorem hankelDet_coefficients (shift size : ℕ) :
    hankelDet shift size = (-1 : Base) ^ (size * shift) *
      (Matrix.of fun row column : Fin shift =>
        (orthogonal (size + row)).coeff column).det := by
  classical
  have augmented : ∀ count width : ℕ, ∀ bottom : ℕ → ℕ → Base,
      (Matrix.of fun row column : Fin (width + count) =>
        if row.val < count then
          (if column.val = width + row.val then 1 else 0)
        else bottom (row.val - count) column.val).det =
      (-1 : Base) ^ (count * width) *
        (Matrix.of fun row column : Fin width => bottom row column).det := by
    intro count
    induction count with
    | zero => intro width bottom; simp
    | succ count induction_hypothesis =>
      intro width bottom
      let matrix : Matrix (Fin (width + count + 1)) (Fin (width + count + 1)) Base :=
        Matrix.of fun row column =>
          if row.val < count + 1 then
            (if column.val = width + row.val then 1 else 0)
          else bottom (row.val - (count + 1)) column.val
      let pivot : Fin (width + count + 1) := ⟨width, by omega⟩
      have expansion : matrix.det = (-1 : Base) ^ width *
          (matrix.submatrix Fin.succ pivot.succAbove).det := by
        rw [Matrix.det_succ_row_zero, sum_eq_single pivot]
        · simp [matrix, pivot]
        · intro column _ column_ne
          have column_val_ne : column.val ≠ width := by
            intro equal
            apply column_ne
            exact Fin.ext equal
          simp [matrix, column_val_ne]
        · simp
      have minor : matrix.submatrix Fin.succ pivot.succAbove =
          Matrix.of (fun row column : Fin (width + count) =>
            if row.val < count then
              (if column.val = width + row.val then 1 else 0)
            else bottom (row.val - count)
              (if column.val < width then column.val else column.val + 1)) := by
        apply Matrix.ext
        intro row column
        have hole : (pivot.succAbove column).val =
            if column.val < width then column.val else column.val + 1 := by
          by_cases before : column.val < width
          · rw [Fin.succAbove_of_castSucc_lt pivot column (by exact before)]
            simp [before]
          · rw [Fin.succAbove_of_le_castSucc pivot column (by exact le_of_not_gt before)]
            simp [before]
        simp only [Matrix.submatrix_apply, Matrix.of_apply, matrix, Fin.val_succ, hole]
        have row_test : row.val + 1 < count + 1 ↔ row.val < count := by omega
        rw [if_congr row_test rfl rfl]
        by_cases top : row.val < count
        · simp only [top, if_true]
          have column_test :
              (if column.val < width then column.val else column.val + 1) =
                width + (row.val + 1) ↔ column.val = width + row.val := by
            split_ifs <;> omega
          rw [if_congr column_test rfl rfl]
        · simp only [top, if_false]
          congr 1
          omega
      have bottom_fixed :
          (Matrix.of fun row column : Fin width =>
            bottom row (if column.val < width then column.val else column.val + 1)) =
          Matrix.of (fun row column : Fin width => bottom row column) := by
        apply Matrix.ext
        intro row column
        simp
      change matrix.det = _
      rw [expansion, minor, induction_hypothesis width
        (fun row column => bottom row (if column < width then column else column + 1)),
        bottom_fixed, ← mul_assoc, ← pow_add]
      congr 1
      ring
  let total := shift + size
  let paths : Matrix (Fin total) (Fin total) Base :=
    Matrix.of fun row height => motzkin row height
  let coefficients : Matrix (Fin total) (Fin total) Base :=
    Matrix.of fun row degree => (orthogonal row).coeff degree
  have inverse : paths * coefficients = 1 := by
    apply Matrix.ext
    intro row column
    simp only [Matrix.mul_apply, paths, coefficients, Matrix.of_apply]
    rw [Fin.sum_univ_eq_sum_range
      (fun height => motzkin row height * (orthogonal height).coeff column) total]
    have finite_sum :
        (∑ height ∈ range total, motzkin row height * (orthogonal height).coeff column) =
        ∑ height ∈ range (row.val + 1),
          motzkin row height * (orthogonal height).coeff column := by
      symm
      apply sum_subset (range_mono (by omega))
      intro height _ outside
      rw [(motzkin_triangle row).1 height (by simpa using outside), zero_mul]
    rw [finite_sum]
    have expansion := congrArg (fun polynomial : Base[X] => polynomial.coeff column)
      (orthogonal_basis row).2
    simp only [finsetSum_coeff, coeff_C_mul, coeff_X_pow] at expansion
    rw [← expansion]
    simp [Matrix.one_apply, Fin.ext_iff, eq_comm]
  have coefficients_lower : coefficients.IsLowerTriangular := by
    intro row column column_gt
    exact coeff_eq_zero_of_natDegree_lt
      (by simpa [(orthogonal_basis row).1.natDegree_eq] using column_gt)
  have coefficients_det : coefficients.det = 1 := by
    rw [Matrix.det_of_isLowerTriangular coefficients coefficients_lower]
    apply prod_eq_one
    intro row _
    change (orthogonal row).coeff row = 1
    simpa only [(orthogonal_basis row).1.natDegree_eq] using
      (orthogonal_basis row).1.monic.coeff_natDegree
  let extended : Matrix (Fin total) (Fin total) Base :=
    Matrix.of fun row column =>
      if row.val < size then motzkin (shift + row) column
      else if row = column then 1 else 0
  have product : extended * coefficients =
      Matrix.of (fun row column : Fin total =>
        if row.val < size then
          (if column.val = shift + row.val then 1 else 0)
        else (orthogonal (size + (row.val - size))).coeff column) := by
    apply Matrix.ext
    intro row column
    by_cases top : row.val < size
    · let shifted_row : Fin total := ⟨shift + row.val, by dsimp [total]; omega⟩
      have entry := congrArg (fun matrix : Matrix (Fin total) (Fin total) Base =>
        matrix shifted_row column) inverse
      simp only [Matrix.mul_apply, paths, coefficients, Matrix.of_apply] at entry
      simp only [Matrix.mul_apply, extended, Matrix.of_apply, top, if_true]
      simpa [shifted_row, coefficients, Matrix.one_apply, Fin.ext_iff, eq_comm] using entry
    · simp only [Matrix.mul_apply, extended, Matrix.of_apply, top, if_false]
      rw [sum_eq_single row]
      · simp only [ite_true, one_mul, coefficients, Matrix.of_apply]
        rw [Nat.add_sub_of_le (Nat.le_of_not_lt top)]
      · intro height _ height_ne
        simp [Ne.symm height_ne]
      · simp
  have extended_det : extended.det = hankelDet shift size := by
    let indexing : Fin size ⊕ Fin shift ≃ Fin total :=
      (finSumFinEquiv : Fin size ⊕ Fin shift ≃ Fin (size + shift)).trans
        (finCongr (Nat.add_comm size shift))
    let corner : Matrix (Fin size) (Fin size) Base :=
      Matrix.of fun row column => motzkin (shift + row) column
    let side : Matrix (Fin size) (Fin shift) Base :=
      Matrix.of fun row column => motzkin (shift + row) (size + column)
    have block : extended.submatrix indexing indexing = Matrix.fromBlocks corner side 0 1 := by
      apply Matrix.ext
      intro row column
      cases row <;> cases column <;>
        simp [extended, indexing, corner, side, Matrix.fromBlocks,
          Matrix.one_apply, Fin.ext_iff, Nat.add_comm, total]
      all_goals omega
    rw [← Matrix.det_submatrix_equiv_self indexing extended, block,
      Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one,
      hankelDet_transfer shift size]
  have determinant_product : (extended * coefficients).det = extended.det := by
    rw [Matrix.det_mul, coefficients_det, mul_one]
  rw [← extended_det, ← determinant_product, product]
  exact augmented size shift (fun row degree => (orthogonal (size + row)).coeff degree)

end D5.S3.Combinatorics.MotzkinHankel.CiglerMotzkinHankelOrthogonal
