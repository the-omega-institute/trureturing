/- GID: D5/S3/Quantum/MatrixUnits
   generality: G
   mirror-B: D5/B/S3/Quantum/MatrixUnits
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Exact finite matrix-unit and cyclic Weyl-pair structure. -/

import Mathlib

namespace D5.S3.Quantum.MatrixUnits

open scoped Fin.NatCast

/-- The canonical primitive root used by an `n`-level finite register. -/
noncomputable def quditRoot (n : Nat) [NeZero n] : Complex :=
  Complex.exp (2 * Real.pi * Complex.I / n)

/-- The cyclic shift matrix on the standard basis of `Fin n`. -/
def quditShift (n : Nat) : Matrix (Fin n) (Fin n) Complex :=
  (finRotate n).permMatrix Complex

/-- The diagonal phase matrix with entries `1, omega, ..., omega^(n-1)`. -/
noncomputable def quditPhase (n : Nat) [NeZero n] : Matrix (Fin n) (Fin n) Complex :=
  Matrix.diagonal fun i => quditRoot n ^ i.val

private theorem qudit_root_primitive (n : Nat) [NeZero n] :
    IsPrimitiveRoot (quditRoot n) n := by
  exact Complex.isPrimitiveRoot_exp n (NeZero.ne n)

private theorem qudit_phase_rotate (n : Nat) [NeZero n] (i : Fin n) :
    quditRoot n ^ (finRotate n i).val = quditRoot n * quditRoot n ^ i.val := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  by_cases hi : i = Fin.last m
  · subst i
    rw [finRotate_last]
    simpa [pow_succ'] using (qudit_root_primitive (m + 1)).pow_eq_one.symm
  · have hlt : i.val < m := by
      have hle : i.val ≤ m := Nat.le_of_lt_succ i.isLt
      exact lt_of_le_of_ne hle (fun h => hi (Fin.ext h))
    have hrotate : finRotate (m + 1) i = ⟨i.val + 1, by omega⟩ := by
      simpa only [Fin.ext_iff] using finRotate_of_lt hlt
    rw [hrotate]
    simp only [pow_succ]
    exact mul_comm _ _

/-- The constructed shift and phase matrices obey the finite Weyl relation. -/
theorem qudit_weyl_relation (n : Nat) [NeZero n] :
    quditShift n * quditPhase n =
      quditRoot n • (quditPhase n * quditShift n) := by
  rw [quditShift, quditPhase]
  rw [PEquiv.toMatrix_toPEquiv_mul]
  rw [PEquiv.mul_toMatrix_toPEquiv]
  ext i j
  simp only [Matrix.submatrix_apply, id_eq, Matrix.smul_apply]
  by_cases hij : finRotate n i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq, Equiv.symm_apply_apply]
    exact qudit_phase_rotate n i
  · have hsymm : (finRotate n).symm j ≠ i := by
      intro h
      apply hij
      have hj : j = finRotate n i := by
        simpa using congrArg (finRotate n) h
      exact hj.symm
    rw [Matrix.diagonal_apply_ne (fun i => quditRoot n ^ i.val) hij]
    rw [Matrix.diagonal_apply_ne (fun i => quditRoot n ^ i.val) hsymm.symm]
    simp

/-- The constructed phase matrix has order dividing the register dimension. -/
theorem qudit_phase_order (n : Nat) [NeZero n] :
    quditPhase n ^ n = 1 := by
  rw [quditPhase, Matrix.diagonal_pow]
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq, Pi.pow_apply, Matrix.one_apply, if_pos]
    rw [← pow_mul, Nat.mul_comm, pow_mul, (qudit_root_primitive n).pow_eq_one, one_pow]
  · simp [hij]

private theorem fin_rotate_pow_card (n : Nat) [NeZero n] :
    finRotate n ^ n = 1 := by
  apply Equiv.ext
  intro i
  have hpow : ∀ k : Nat, (finRotate n ^ k) i = i + (k : Fin n) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ', Equiv.Perm.mul_apply, finRotate_apply, ih]
        simp [add_assoc]
  simpa using hpow n

private theorem perm_matrix_pow (n k : Nat) :
    quditShift n ^ k = ((finRotate n) ^ k).permMatrix Complex := by
  induction k with
  | zero => simp [quditShift]
  | succ k ih =>
      rw [pow_succ', ih, quditShift]
      rw [← Matrix.permMatrix_mul]
      rfl

/-- The cyclic shift matrix has order dividing the register dimension. -/
theorem qudit_shift_order (n : Nat) [NeZero n] :
    quditShift n ^ n = 1 := by
  rw [perm_matrix_pow, fin_rotate_pow_card]
  simp

/-- Multiplication and adjoint matrix-unit certificates have exactly zero residual. -/
theorem matrix_unit_certificate_error_zero
    (index : Type*) [Fintype index] [DecidableEq index]
    (i j k l : index) :
    Matrix.single i j (1 : Complex) * Matrix.single k l 1 -
        (if j = k then Matrix.single i l 1 else 0) = 0 ∧
      star (Matrix.single i j (1 : Complex)) - Matrix.single j i 1 = 0 := by
  constructor
  · by_cases hjk : j = k
    · subst k
      simp
    · rw [if_neg hjk, Matrix.single_mul_single_of_ne 1 i j k hjk 1]
      simp
  · simp [Matrix.star_eq_conjTranspose]

/-- The standard matrix units generate the entire finite square matrix algebra. -/
theorem matrix_units_generate_full_algebra
    (index : Type*) [Fintype index] [DecidableEq index] :
    Algebra.adjoin Complex
        (Set.range fun pair : index × index => Matrix.single pair.1 pair.2 (1 : Complex)) = ⊤ := by
  apply top_unique
  intro matrix _
  rw [Matrix.matrix_eq_sum_single matrix]
  apply Subalgebra.sum_mem
  intro i _
  apply Subalgebra.sum_mem
  intro j _
  have hSingle : Matrix.single i j (matrix i j) =
      matrix i j • Matrix.single i j (1 : Complex) := by
    rw [Matrix.smul_single]
    simp
  rw [hSingle]
  exact Subalgebra.smul_mem _
    (Algebra.subset_adjoin (Set.mem_range_self (i, j))) (matrix i j)

/-- A full complex matrix algebra of dimension at least two has no character. -/
theorem matrix_algebra_has_no_character
    (index : Type*) [Fintype index] [DecidableEq index]
    (hCard : 2 ≤ Fintype.card index) :
    IsEmpty (Matrix index index Complex →ₐ[Complex] Complex) := by
  letI : Nontrivial index := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  constructor
  intro character
  have hOffDiagonal : ∀ i j : index, i ≠ j →
      character (Matrix.single i j (1 : Complex)) = 0 := by
    intro i j hij
    have hSquare :
        Matrix.single i j (1 : Complex) * Matrix.single i j 1 = 0 := by
      exact Matrix.single_mul_single_of_ne 1 i j i hij.symm 1
    have hImageSquare :
        character (Matrix.single i j (1 : Complex)) *
            character (Matrix.single i j 1) = 0 := by
      rw [← map_mul, hSquare, map_zero]
    exact mul_self_eq_zero.mp hImageSquare
  have hDiagonal : ∀ i : index,
      character (Matrix.single i i (1 : Complex)) = 0 := by
    intro i
    obtain ⟨j, hji⟩ := exists_ne i
    calc
      character (Matrix.single i i (1 : Complex)) =
          character (Matrix.single i j 1 * Matrix.single j i 1) := by
            rw [Matrix.single_mul_single_same]
            simp
      _ = character (Matrix.single i j 1) * character (Matrix.single j i 1) :=
        map_mul character _ _
      _ = 0 := by rw [hOffDiagonal i j hji.symm]; simp
  have hOne : character (1 : Matrix index index Complex) = 0 := by
    rw [← Matrix.sum_single_one]
    simp [hDiagonal]
  simp at hOne

end D5.S3.Quantum.MatrixUnits
