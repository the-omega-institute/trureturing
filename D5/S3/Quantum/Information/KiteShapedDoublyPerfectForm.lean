/- GID: D5/S3/Quantum/Information/KiteShapedDoublyPerfectForm
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/KiteShapedDoublyPerfectForm
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Binary kite forms are doubly perfect exactly off one residue modulo three. -/

import D5.S3.Quantum.FockSpace.ForbiddenNeighbourDeterminant

set_option autoImplicit false

/-! Kite matrices over the binary field and their quadratic and symplectic block forms. -/

namespace D5.S3.Quantum.Information.KiteShapedDoublyPerfectForm

def kite (n : ℕ) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  fun i j => if i.val + j.val + 2 ≤ n + 1 then 1 else 0

def quadraticForm (n : ℕ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (ZMod 2) :=
  Matrix.fromBlocks (kite n) 0 0 (kite n)

def claim : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    (kite n).IsSymm ∧
    (kite n).SeparatingRight ∧ (quadraticForm n).SeparatingRight ∧
    ((kite n * kite n - 1).SeparatingRight ↔ n % 3 ≠ 1) ∧
    ((quadraticForm n + Matrix.J (Fin n) (ZMod 2)).SeparatingRight ↔ n % 3 ≠ 1)

private def inverseKite (n : ℕ) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  fun i j => (if i.val + j.val + 1 = n then 1 else 0) +
    (if i.val + j.val = n then 1 else 0)

private def tridiagonal (n : ℕ) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  fun i j => if (i = j ∧ i.val ≠ 0) ∨ i.val + 1 = j.val ∨ j.val + 1 = i.val
    then 1 else 0

private lemma kite_symmetric (n : ℕ) : (kite n).IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply, kite, Nat.add_comm i.val j.val]

private lemma inverse_column (n : ℕ) (j : Fin n) (f : Fin n → ZMod 2) :
    ∑ k, f k * inverseKite n k j =
      f j.rev + if h : 0 < j.val then f ⟨n - j.val, by omega⟩ else 0 := by
  have first (k : Fin n) : k.val + j.val + 1 = n ↔ k = j.rev := by
    rw [Fin.ext_iff, Fin.val_rev]
    omega
  simp only [inverseKite, mul_add, Finset.sum_add_distrib, first,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  congr 1
  split_ifs with h
  · have second (k : Fin n) : k.val + j.val = n ↔ k = (⟨n - j.val, by omega⟩ : Fin n) := by
      rw [Fin.ext_iff]
      dsimp
      omega
    simp only [second, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  · have second (k : Fin n) : k.val + j.val ≠ n := by omega
    simp only [second, ite_false, Finset.sum_const_zero]

private lemma kite_inverse (n : ℕ) : kite n * inverseKite n = 1 := by
  ext i j
  rw [Matrix.mul_apply, inverse_column]
  simp only [kite, Fin.val_rev, Matrix.one_apply]
  split_ifs <;> simp only [CharTwo.add_self_eq_zero, zero_add, add_zero] <;> omega

private lemma kite_det (n : ℕ) : (kite n).det = 1 := by
  have hn : (kite n).det ≠ 0 := Matrix.det_ne_zero_of_right_inverse (kite_inverse n)
  exact Fin.eq_one_of_ne_zero _ hn

private lemma inverse_square (n : ℕ) :
    tridiagonal n = 1 + inverseKite n * inverseKite n := by
  ext i j
  rw [Matrix.add_apply, Matrix.mul_apply, inverse_column]
  simp only [tridiagonal, inverseKite, Matrix.one_apply, Fin.val_rev, Fin.ext_iff]
  split_ifs <;> simp only [CharTwo.add_self_eq_zero, zero_add, add_zero] <;> omega

private lemma tridiagonal_recurrence (n : ℕ) :
    (tridiagonal (n + 2)).det = (tridiagonal (n + 1)).det + (tridiagonal n).det := by
  let R := (tridiagonal (n + 2)).submatrix Fin.revPerm Fin.revPerm
  have hr (j : Fin n) : R 0 j.succ.succ = 0 := by
    simp only [R, Matrix.submatrix_apply, Fin.revPerm_apply, Fin.rev_zero, Fin.rev_succ,
      tridiagonal, Fin.ext_iff, Fin.val_last, Fin.val_castSucc, Fin.val_rev]
    exact if_neg (by omega)
  have hc (i : Fin n) : R i.succ.succ 0 = 0 := by
    simp only [R, Matrix.submatrix_apply, Fin.revPerm_apply, Fin.rev_zero, Fin.rev_succ,
      tridiagonal, Fin.ext_iff, Fin.val_last, Fin.val_castSucc, Fin.val_rev]
    exact if_neg (by omega)
  have ht : R.submatrix Fin.succ Fin.succ =
      (tridiagonal (n + 1)).submatrix Fin.revPerm Fin.revPerm := by
    ext i j
    simp only [R, Matrix.submatrix_apply, Fin.revPerm_apply, Fin.rev_succ,
      tridiagonal, Fin.ext_iff, Fin.val_castSucc]
  have ht2 : R.submatrix (fun i : Fin n => i.succ.succ) (fun j : Fin n => j.succ.succ) =
      (tridiagonal n).submatrix Fin.revPerm Fin.revPerm := by
    ext i j
    simp only [R, Matrix.submatrix_apply, Fin.revPerm_apply, Fin.rev_succ,
      tridiagonal, Fin.ext_iff, Fin.val_castSucc]
  have h := D5.S3.Quantum.FockSpace.ForbiddenNeighbourDeterminant.det_sparse_front R hr hc
  rw [ht, ht2, Matrix.det_submatrix_equiv_self, Matrix.det_submatrix_equiv_self] at h
  simpa [R, tridiagonal, Fin.ext_iff, Fin.val_rev, Fin.val_one', sub_eq_add_neg] using h

private lemma tridiagonal_det_zero (n : ℕ) : (tridiagonal n).det = 0 ↔ n % 3 = 1 := by
  have values : ∀ k, (tridiagonal k).det = if k % 3 = 1 then 0 else 1 := by
    intro k
    induction k using Nat.twoStepInduction with
    | zero => simp
    | one => simp [tridiagonal]
    | more k hk hk1 =>
        rw [tridiagonal_recurrence, hk, hk1]
        have hm : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
        rcases hm with h | h | h <;>
          simp [Nat.add_mod, h, CharTwo.add_self_eq_zero]
  rw [values]
  split_ifs <;> simp_all

private lemma square_det (n : ℕ) :
    (kite n * kite n - 1).det = (tridiagonal n).det := by
  have hp : kite n * kite n * tridiagonal n = kite n * kite n + 1 := by
    rw [inverse_square, Matrix.mul_add, Matrix.mul_one]
    congr 1
    calc
      kite n * kite n * (inverseKite n * inverseKite n) =
          kite n * (kite n * inverseKite n) * inverseKite n := by
            simp only [Matrix.mul_assoc]
      _ = 1 := by rw [kite_inverse, Matrix.mul_one, kite_inverse]
  have hn : -(1 : Matrix (Fin n) (Fin n) (ZMod 2)) = 1 := by
    ext i j
    exact CharTwo.neg_eq _
  rw [sub_eq_add_neg, hn, ← hp, Matrix.det_mul, Matrix.det_mul, kite_det]
  simp

private lemma quadratic_det (n : ℕ) : (quadraticForm n).det = 1 := by
  simp [quadraticForm, Matrix.det_fromBlocks_zero₂₁, kite_det]

private lemma symplectic_det (n : ℕ) :
    (quadraticForm n + Matrix.J (Fin n) (ZMod 2)).det = (kite n * kite n - 1).det := by
  let : Invertible (kite n) := invertibleOfRightInverse _ _ (kite_inverse n)
  have hi : ⅟(kite n) = inverseKite n := invOf_eq_right_inv (kite_inverse n)
  have hb : quadraticForm n + Matrix.J (Fin n) (ZMod 2) =
      Matrix.fromBlocks (kite n) 1 1 (kite n) := by
    ext i j
    cases i <;> cases j <;> simp [quadraticForm, Matrix.J, Matrix.one_apply]
  rw [hb, Matrix.det_fromBlocks₁₁, kite_det, one_mul, Matrix.one_mul, Matrix.mul_one, hi]
  have h := Matrix.det_mul (kite n) (kite n - inverseKite n)
  rw [Matrix.mul_sub, kite_inverse, kite_det, one_mul] at h
  exact h.symm

theorem result : claim := by
  intro n _hn
  refine ⟨kite_symmetric n, Matrix.separatingRight_iff_det_ne_zero.mpr ?_,
    Matrix.separatingRight_iff_det_ne_zero.mpr ?_, ?_, ?_⟩
  · rw [kite_det]
    exact one_ne_zero
  · rw [quadratic_det]
    exact one_ne_zero
  · rw [Matrix.separatingRight_iff_det_ne_zero, square_det, ne_eq, tridiagonal_det_zero]
  · rw [Matrix.separatingRight_iff_det_ne_zero, symplectic_det, square_det, ne_eq,
      tridiagonal_det_zero]

end D5.S3.Quantum.Information.KiteShapedDoublyPerfectForm
