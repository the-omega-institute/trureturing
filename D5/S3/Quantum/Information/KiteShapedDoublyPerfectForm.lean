/- GID: D5/S3/Quantum/Information/KiteShapedDoublyPerfectForm
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/KiteShapedDoublyPerfectForm
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Binary kite forms are doubly perfect exactly off one residue modulo three. -/

import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.CharP.Two
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace D5.S3.Quantum.Information.KiteShapedDoublyPerfectForm

def kite (n : ℕ) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  fun i j => if i.val + j.val + 2 ≤ n + 1 then 1 else 0

def quadraticForm (n : ℕ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (ZMod 2) :=
  Matrix.fromBlocks (kite n) 0 0 (kite n)

def symplecticForm (n : ℕ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (ZMod 2) :=
  Matrix.fromBlocks 0 1 (-1) 0

def TrivialKernel {ι : Type*} [Fintype ι] (M : Matrix ι ι (ZMod 2)) : Prop :=
  ∀ v, M.mulVec v = 0 → v = 0

def claim : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    (kite n).IsSymm ∧
    TrivialKernel (kite n) ∧ TrivialKernel (quadraticForm n) ∧
    (TrivialKernel (kite n * kite n - 1) ↔ n % 3 ≠ 1) ∧
    (TrivialKernel (quadraticForm n + symplecticForm n) ↔ n % 3 ≠ 1)

private def inverseKite (n : ℕ) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  fun i j => (if i.val + j.val + 1 = n then 1 else 0) +
    (if i.val + j.val = n then 1 else 0)

private def tridiagonal (n : ℕ) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  fun i j => if (i = j ∧ i.val ≠ 0) ∨ i.val + 1 = j.val ∨ j.val + 1 = i.val
    then 1 else 0

private lemma kernel_iff_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (ZMod 2)) : TrivialKernel M ↔ M.det ≠ 0 := by
  classical
  constructor
  · intro h hd
    obtain ⟨v, hv, hz⟩ := M.exists_mulVec_eq_zero_iff.mpr hd
    exact hv (h v hz)
  · intro hd v hz
    by_contra hv
    exact hd (M.exists_mulVec_eq_zero_iff.mp ⟨v, hv, hz⟩)

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
  have h := congrArg Matrix.det (kite_inverse n)
  rw [Matrix.det_mul, Matrix.det_one] at h
  have hn : (kite n).det ≠ 0 := by
    intro hz
    simp [hz] at h
  have hv := ZMod.val_lt (kite n).det
  have hvn := (ZMod.val_ne_zero _).2 hn
  apply (ZMod.val_injective 2)
  simpa only [ZMod.val_one_eq_one_mod, Nat.one_mod] using
    (show ((kite n).det).val = 1 by omega)

private lemma inverse_square (n : ℕ) :
    tridiagonal n = 1 + inverseKite n * inverseKite n := by
  ext i j
  rw [Matrix.add_apply, Matrix.mul_apply, inverse_column]
  simp only [tridiagonal, inverseKite, Matrix.one_apply, Fin.val_rev, Fin.ext_iff]
  split_ifs <;> simp only [CharTwo.add_self_eq_zero, zero_add, add_zero] <;> omega

private lemma tridiagonal_castSucc (n : ℕ) :
    (tridiagonal (n + 1)).submatrix Fin.castSucc Fin.castSucc = tridiagonal n := by
  ext i j
  simp only [Matrix.submatrix_apply, tridiagonal, Fin.ext_iff, Fin.val_castSucc]

private lemma tridiagonal_corner_minor (n : ℕ) :
    ((tridiagonal (n + 2)).submatrix Fin.castSucc
      (Fin.castSucc (Fin.last n)).succAbove).det = (tridiagonal n).det := by
  let M := (tridiagonal (n + 2)).submatrix Fin.castSucc
    (Fin.castSucc (Fin.last n)).succAbove
  have hcol (i : Fin (n + 1)) : M i (Fin.last n) =
      if i = Fin.last n then 1 else 0 := by
    simp only [M, Matrix.submatrix_apply, Fin.succAbove_castSucc_self,
      tridiagonal, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ, Fin.val_last]
    split_ifs <;> first | rfl | omega
  have hminor : M.submatrix Fin.castSucc Fin.castSucc = tridiagonal n := by
    ext i j
    have hc : (Fin.castSucc (Fin.last n)).succAbove j.castSucc =
        j.castSucc.castSucc :=
      Fin.succAbove_castSucc_of_lt _ _ (Fin.castSucc_lt_last j)
    simp only [M, Matrix.submatrix_apply, hc, tridiagonal, Fin.ext_iff, Fin.val_castSucc]
  change M.det = _
  rw [Matrix.det_succ_column M (Fin.last n)]
  simp only [ZMod.neg_eq_self_mod_two, one_pow, one_mul, hcol, ite_mul, one_mul,
    zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true, Fin.succAbove_last, hminor]

private lemma tridiagonal_recurrence (n : ℕ) :
    (tridiagonal (n + 2)).det = (tridiagonal (n + 1)).det + (tridiagonal n).det := by
  rw [Matrix.det_succ_row _ (Fin.last (n + 1))]
  simp only [ZMod.neg_eq_self_mod_two, one_pow, one_mul]
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  have hz (j : Fin n) : tridiagonal (n + 2) (Fin.last (n + 1))
      j.castSucc.castSucc = 0 := by
    simp only [tridiagonal, Fin.ext_iff, Fin.val_last, Fin.val_castSucc]
    exact if_neg (by omega)
  have ha : tridiagonal (n + 2) (Fin.last (n + 1)) (Fin.last n).castSucc = 1 := by
    simp [tridiagonal]
  have hb : tridiagonal (n + 2) (Fin.last (n + 1)) (Fin.last (n + 1)) = 1 := by
    simp [tridiagonal]
  simp only [hz, zero_mul, Finset.sum_const_zero, zero_add, ha, hb, one_mul,
    Fin.succAbove_last, tridiagonal_castSucc, tridiagonal_corner_minor]
  exact add_comm _ _

private lemma tridiagonal_det_zero (n : ℕ) : (tridiagonal n).det = 0 ↔ n % 3 = 1 := by
  have values : ∀ k, (tridiagonal k).det = if k % 3 = 1 then 0 else 1 := by
    intro k
    induction k using Nat.twoStepInduction with
    | zero => simp
    | one => simp [Matrix.det_fin_one, tridiagonal]
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
    simp [Matrix.one_apply]
  rw [sub_eq_add_neg, hn, ← hp, Matrix.det_mul, Matrix.det_mul, kite_det]
  simp

private lemma quadratic_det (n : ℕ) : (quadraticForm n).det = 1 := by
  simp [quadraticForm, Matrix.det_fromBlocks_zero₂₁, kite_det]

private lemma symplectic_det (n : ℕ) :
    (quadraticForm n + symplecticForm n).det = (kite n * kite n - 1).det := by
  letI : Invertible (kite n) := invertibleOfRightInverse _ _ (kite_inverse n)
  have hi : ⅟(kite n) = inverseKite n := invOf_eq_right_inv (kite_inverse n)
  have hb : quadraticForm n + symplecticForm n =
      Matrix.fromBlocks (kite n) 1 1 (kite n) := by
    ext i j
    cases i <;> cases j <;> simp [quadraticForm, symplecticForm, Matrix.one_apply]
  rw [hb, Matrix.det_fromBlocks₁₁, kite_det, one_mul, Matrix.one_mul, Matrix.mul_one, hi]
  have h := Matrix.det_mul (kite n) (kite n - inverseKite n)
  rw [Matrix.mul_sub, kite_inverse, kite_det, one_mul] at h
  exact h.symm

theorem result : claim := by
  intro n _hn
  refine ⟨kite_symmetric n, (kernel_iff_det _).2 ?_, (kernel_iff_det _).2 ?_, ?_, ?_⟩
  · rw [kite_det]
    exact one_ne_zero
  · rw [quadratic_det]
    exact one_ne_zero
  · rw [kernel_iff_det, square_det, ne_eq, tridiagonal_det_zero]
  · rw [kernel_iff_det, symplectic_det, square_det, ne_eq, tridiagonal_det_zero]

end D5.S3.Quantum.Information.KiteShapedDoublyPerfectForm
