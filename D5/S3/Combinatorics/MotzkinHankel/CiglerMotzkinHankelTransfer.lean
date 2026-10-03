/- GID: D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelTransfer
   generality: G
   mirror-B: D5/B/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelTransfer
   mirror-E: none(waiver:integral-motzkin-transfer-minor)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Block, mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Motzkin convolution reduces shifted Hankel determinants to path transfer minors. -/

import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic
import D5.S3.Combinatorics.MotzkinHankel.CiglerMotzkinHankelDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.MotzkinHankel.CiglerMotzkinHankelTransfer

open Finset CiglerMotzkinHankelDefs

theorem motzkin_triangle (length : ℕ) :
    (∀ height : ℕ, length < height → motzkin length height = 0) ∧
      motzkin length length = 1 := by
  induction length with
  | zero =>
    constructor
    · intro height height_gt
      simp [motzkin, show height ≠ 0 by omega]
    · simp [motzkin]
  | succ length induction_hypothesis =>
    constructor
    · intro height height_gt
      have height_ne : height ≠ 0 := by omega
      rw [motzkin, if_neg height_ne, if_neg height_ne,
        induction_hypothesis.1 (height - 1) (by omega),
        induction_hypothesis.1 height (by omega),
        induction_hypothesis.1 (height + 1) (by omega)]
      ring
    · rw [motzkin, if_neg (by omega : length + 1 ≠ 0),
        if_neg (by omega : length + 1 ≠ 0), Nat.add_sub_cancel,
        induction_hypothesis.2,
        induction_hypothesis.1 (length + 1) (by omega),
        induction_hypothesis.1 (length + 1 + 1) (by omega)]
      ring

theorem hankelDet_transfer (shift size : ℕ) :
    hankelDet shift size =
      (Matrix.of fun row column : Fin size => motzkin (shift + row) column).det := by
  classical
  have down_shift (left right : ℕ → Base) (bound : ℕ) :
      (∑ height ∈ range (bound + 1),
        (if height = 0 then 0 else left (height - 1)) * right height) =
      ∑ height ∈ range bound, left height * right (height + 1) := by
    rw [sum_range_succ']
    simp
  have up_shift (left right : ℕ → Base) (bound : ℕ) :
      (∑ height ∈ range (bound + 1), left (height + 1) * right height) =
      (∑ height ∈ range bound, left (height + 1) * right height) +
        left (bound + 1) * right bound := sum_range_succ _ _
  have move_step (left_length right_length bound : ℕ)
      (right_lt : right_length < bound) :
      (∑ height ∈ range (bound + 1),
        motzkin (left_length + 1) height * motzkin right_length height) =
      ∑ height ∈ range (bound + 1),
        motzkin left_length height * motzkin (right_length + 1) height := by
    simp only [motzkin, add_mul, mul_add, sum_add_distrib]
    have right_tail : motzkin right_length bound = 0 :=
      (motzkin_triangle right_length).1 bound right_lt
    have right_next : motzkin right_length (bound + 1) = 0 :=
      (motzkin_triangle right_length).1 (bound + 1) (by omega)
    have upper_left := up_shift (motzkin left_length) (motzkin right_length) bound
    have upper_right := up_shift (motzkin right_length) (motzkin left_length) bound
    have lower_left := down_shift (motzkin left_length) (motzkin right_length) bound
    have lower_right := down_shift (motzkin right_length) (motzkin left_length) bound
    simp only [right_tail, right_next, mul_zero, zero_mul, add_zero] at upper_left upper_right
    have diagonal :
        (∑ height ∈ range (bound + 1),
          ((if height = 0 then sVar else tVar) * motzkin left_length height) *
            motzkin right_length height) =
        ∑ height ∈ range (bound + 1), motzkin left_length height *
          ((if height = 0 then sVar else tVar) * motzkin right_length height) := by
      apply sum_congr rfl
      intro height _
      ring
    rw [lower_left, upper_left, diagonal]
    have lower_right_comm :
        (∑ height ∈ range (bound + 1), motzkin left_length height *
          (if height = 0 then 0 else motzkin right_length (height - 1))) =
        ∑ height ∈ range bound, motzkin left_length (height + 1) *
          motzkin right_length height := by
      simpa only [mul_comm] using lower_right
    have upper_right_comm :
        (∑ height ∈ range (bound + 1), motzkin left_length height *
          motzkin right_length (height + 1)) =
        ∑ height ∈ range bound, motzkin left_length height *
          motzkin right_length (height + 1) := by
      simpa only [mul_comm] using upper_right
    rw [lower_right_comm, upper_right_comm]
    ring
  have convolution : ∀ right_length left_length bound : ℕ, right_length ≤ bound →
      motzkin (left_length + right_length) 0 =
        ∑ height ∈ range (bound + 1),
          motzkin left_length height * motzkin right_length height := by
    intro right_length
    induction right_length with
    | zero =>
      intro left_length bound _
      simp [motzkin]
    | succ right_length induction_hypothesis =>
      intro left_length bound right_le
      rw [show left_length + (right_length + 1) =
        (left_length + 1) + right_length by omega,
        induction_hypothesis (left_length + 1) bound (by omega),
        move_step left_length right_length bound (by omega)]
  let paths : Matrix (Fin size) (Fin size) Base :=
    Matrix.of fun row height => motzkin row height
  let shifted : Matrix (Fin size) (Fin size) Base :=
    Matrix.of fun row height => motzkin (shift + row) height
  have factorization :
      (Matrix.of fun row column : Fin size => motzkin (shift + row + column) 0) =
        shifted * paths.transpose := by
    apply Matrix.ext
    intro row column
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, paths, shifted]
    rw [Fin.sum_univ_eq_sum_range
      (fun height => motzkin (shift + row) height * motzkin column height) size]
    cases size with
    | zero => exact Fin.elim0 row
    | succ bound => exact convolution column (shift + row) bound (by omega)
  have paths_lower : paths.IsLowerTriangular := by
    intro row column column_gt
    exact (motzkin_triangle row).1 column column_gt
  have paths_det : paths.det = 1 := by
    rw [Matrix.det_of_isLowerTriangular paths paths_lower]
    simp only [paths, Matrix.of_apply, (motzkin_triangle _).2, prod_const_one]
  unfold hankelDet
  rw [factorization, Matrix.det_mul, Matrix.det_transpose, paths_det, mul_one]

end D5.S3.Combinatorics.MotzkinHankel.CiglerMotzkinHankelTransfer
