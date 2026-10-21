/- GID: D5/S3/Combinatorics/SpectralGraph/CyclicTridiagonalTransferTrace
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/CyclicTridiagonalTransferTrace
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Cyclic tridiagonal determinants equal the transfer trace minus two. -/

/-
proof_shape: content: impulse_zero_of_lt, impulse_self, impulseMatrix_det,
  cycleDiag_det_boundary, tailTransfer_entries, cycleDiag_det_transfer.
proof_shape: bind-only: cycleDiag_apply, impulse_residual, cycle_middle_row, cycle_mul_middle, cycle_first_row,
  cycle_last_row, cycle_mul_first, cycle_mul_last, endsEquiv_zero, endsEquiv_one,
  endsEquiv_right, impulse_tail, transfer_det, evolution_add, evolution_det,
  tailTransfer_full.
Definition rows have proof_shape: bind-only; they introduce the data used in the proofs.
escape_witness: impulse solutions reduce the cyclic determinant to a two-dimensional
boundary determinant; induction identifies the transfer evolution with those solutions.
admission_basis: escape-witness (cycleDiag_det_transfer).
Direct frozen dependencies: none.
The shared transfer and evolution declarations retain the mathematical bodies from
AndersonDefectFamily. Their consumers include the determinant reduction, the five-step
block determinant and AndersonDefectFamily's periodic evolution.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19504.
-/

import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic.LinearCombination

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

noncomputable section
open scoped BigOperators Matrix
namespace D5.S3.Combinatorics.SpectralGraph.CyclicTridiagonalTransferTrace

variable {R : Type*} [CommRing R]

/-- Impulse fundamental solutions; columns form a lower unitriangular matrix. -/
private def impulse (d : ℕ → R) (j : ℕ) : ℕ → R
  | 0 => if j = 0 then 1 else 0
  | 1 => if j = 1 then 1 else 0
  | i + 2 => d (i + 1) * impulse d j (i + 1) - impulse d j i + if j = i + 2 then 1 else 0

private lemma impulse_zero_of_lt (d : ℕ → R) {i j : ℕ} (h : i < j) : impulse d j i = 0 := by
    revert h
    induction i using Nat.twoStepInduction with
    | zero => intro h; simp [impulse, show j ≠ 0 by omega]
    | one => intro h; simp [impulse, show j ≠ 1 by omega]
    | more i h0 h1 =>
        intro h
        simp [impulse, h0 (by omega), h1 (by omega), show j ≠ i + 2 by omega]

private lemma impulse_self (d : ℕ → R) (i : ℕ) : impulse d i i = 1 := by
    cases i with
    | zero => simp [impulse]
    | succ i =>
        cases i with
        | zero => simp [impulse]
        | succ i => simp [impulse, impulse_zero_of_lt d (show i < i+2 by omega),
            impulse_zero_of_lt d (show i+1 < i+2 by omega)]

private lemma impulse_residual (d : ℕ → R) (j i : ℕ) :
    d (i+1) * impulse d j (i+1) - impulse d j i - impulse d j (i+2) =
      -(if j = i+2 then 1 else 0) := by
    rw [impulse]
    ring

def cycleDiag (N : ℕ) (d : ℕ → R) : Matrix (Fin N) (Fin N) R :=
  Matrix.diagonal (fun i => d i.val) - (SimpleGraph.cycleGraph N).adjMatrix R

lemma cycleDiag_apply (n : ℕ) (d : ℕ → R) (i j : Fin (n+3)) :
    cycleDiag (n+3) d i j = if i = j then d i.val
      else if (i.val+1) % (n+3) = j.val ∨ (j.val+1) % (n+3) = i.val then -1 else 0 := by
  by_cases hij : i = j
  · subst j
    simp [cycleDiag, SimpleGraph.adjMatrix_apply]
  · have hadj : (SimpleGraph.cycleGraph (n+3)).Adj i j ↔
        (i.val+1) % (n+3) = j.val ∨ (j.val+1) % (n+3) = i.val := by
      rw [SimpleGraph.cycleGraph_adj, sub_eq_iff_eq_add', sub_eq_iff_eq_add']
      simp [Fin.ext_iff, Fin.val_add, Fin.val_one, Nat.add_comm, eq_comm, or_comm]
    simp only [cycleDiag, Matrix.sub_apply, Matrix.diagonal_apply,
      SimpleGraph.adjMatrix_apply, if_neg hij, hadj, zero_sub]
    split_ifs <;> simp


private def impulseMatrix (N : ℕ) (d : ℕ → R) : Matrix (Fin N) (Fin N) R :=
  fun i j => impulse d j.val i.val

private lemma impulseMatrix_det (N : ℕ) (d : ℕ → R) : (impulseMatrix N d).det = 1 := by
    rw [Matrix.det_of_isLowerTriangular _ (by
      intro i j hij
      exact impulse_zero_of_lt d hij)]
    simp [impulseMatrix, impulse_self]

private lemma cycle_middle_row (n : ℕ) (d : ℕ → R) (i : Fin (n+1)) :
    cycleDiag (n+3) d ⟨i.val+1, by omega⟩ =
      fun j => (if j.val = i.val then (-1 : R) else 0) +
        (if j.val = i.val+1 then d (i.val+1) else 0) +
        (if j.val = i.val+2 then (-1 : R) else 0) := by
    funext j
    have hi : i.val < n+1 := i.isLt
    have hj : j.val < n+3 := j.isLt
    have hmod : (i.val + 1 + 1) % (n+3) = i.val+2 := Nat.mod_eq_of_lt (by omega)
    by_cases hjlast : j.val + 1 = n+3
    · have hjv : j.val = n+2 := Nat.add_right_cancel hjlast
      simp only [cycleDiag_apply, Fin.ext_iff, hmod, hjlast, Nat.mod_self]
      split_ifs <;> (try simp only [or_false, false_or] at *) <;> first | omega | ring
    · have hjmod : (j.val+1) % (n+3) = j.val+1 := Nat.mod_eq_of_lt (by omega)
      simp only [cycleDiag_apply, Fin.ext_iff, hmod, hjmod]
      split_ifs <;> (try simp only [or_false, false_or] at *) <;> first | omega | ring

private lemma cycle_mul_middle (n : ℕ) (d : ℕ → R) (i : Fin (n+1)) (j : Fin (n+3)) :
    (cycleDiag (n+3) d * impulseMatrix (n+3) d) ⟨i.val+1, by omega⟩ j =
      -(if j.val = i.val+2 then 1 else 0) := by
    rw [Matrix.mul_apply, cycle_middle_row]
    simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul]
    simp only [show ∀ k : Fin (n+3), k.val = i.val ↔ k = ⟨i.val, by omega⟩ by
      intro k; exact ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩,
      show ∀ k : Fin (n+3), k.val = i.val+1 ↔ k = ⟨i.val+1, by omega⟩ by
        intro k; exact ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩,
      show ∀ k : Fin (n+3), k.val = i.val+2 ↔ k = ⟨i.val+2, by omega⟩ by
        intro k; exact ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, impulseMatrix]
    simp only [Fin.ext_iff]
    linear_combination impulse_residual d j.val i.val

private lemma cycle_first_row (n : ℕ) (d : ℕ → R) :
    cycleDiag (n+3) d 0 =
      fun j => (if j.val = 0 then d 0 else 0) +
        (if j.val = 1 then (-1 : R) else 0) +
        (if j.val = n+2 then (-1 : R) else 0) := by
    funext j
    have hj : j.val < n+3 := j.isLt
    by_cases hjlast : j.val+1 = n+3
    · have hjv : j.val = n+2 := Nat.add_right_cancel hjlast
      simp [cycleDiag_apply, Fin.ext_iff, hjv, show (1:ℕ) % (n+3) = 1 from Nat.mod_eq_of_lt (by omega)]
    · have hjmod : (j.val+1) % (n+3) = j.val+1 := Nat.mod_eq_of_lt (by omega)
      simp only [cycleDiag_apply, Fin.ext_iff, Fin.val_zero, zero_add, hjmod,
        show (1:ℕ) % (n+3) = 1 from Nat.mod_eq_of_lt (by omega)]
      split_ifs <;> (try simp only [or_false, false_or] at *) <;> first | omega | ring

private lemma cycle_last_row (n : ℕ) (d : ℕ → R) :
    cycleDiag (n+3) d (Fin.last (n+2)) =
      fun j => (if j.val = 0 then (-1 : R) else 0) +
        (if j.val = n+1 then (-1 : R) else 0) +
        (if j.val = n+2 then d (n+2) else 0) := by
    funext j
    have hj : j.val < n+3 := j.isLt
    by_cases hjlast : j.val+1 = n+3
    · have hjv : j.val = n+2 := Nat.add_right_cancel hjlast
      simp [cycleDiag_apply, Fin.ext_iff, hjv]
    · have hjmod : (j.val+1) % (n+3) = j.val+1 := Nat.mod_eq_of_lt (by omega)
      simp only [cycleDiag_apply, Fin.ext_iff, Fin.val_last, show n+2+1 = n+3 by omega,
        Nat.mod_self, hjmod]
      split_ifs <;> (try simp only [or_false, false_or] at *) <;> first | omega | ring

private lemma cycle_mul_first (n : ℕ) (d : ℕ → R) (j : Fin (n+3)) :
    (cycleDiag (n+3) d * impulseMatrix (n+3) d) 0 j =
      d 0 * impulse d j.val 0 - impulse d j.val 1 - impulse d j.val (n+2) := by
    rw [Matrix.mul_apply, cycle_first_row]
    simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul]
    simp only [show ∀ k : Fin (n+3), k.val = 0 ↔ k = 0 by intro k; exact ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩,
      show ∀ k : Fin (n+3), k.val = 1 ↔ k = 1 by intro k; exact ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩,
      show ∀ k : Fin (n+3), k.val = n+2 ↔ k = Fin.last (n+2) by
        intro k; exact ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩]
    simp [impulseMatrix]
    ring

private lemma cycle_mul_last (n : ℕ) (d : ℕ → R) (j : Fin (n+3)) :
    (cycleDiag (n+3) d * impulseMatrix (n+3) d) (Fin.last (n+2)) j =
      d (n+2) * impulse d j.val (n+2) - impulse d j.val (n+1) - impulse d j.val 0 := by
    rw [Matrix.mul_apply, cycle_last_row]
    simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul]
    simp only [show ∀ k : Fin (n+3), k.val = 0 ↔ k = 0 by intro k; exact ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩,
      show ∀ k : Fin (n+3), k.val = n+1 ↔ k = ⟨n+1, by omega⟩ by
        intro k; exact ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩,
      show ∀ k : Fin (n+3), k.val = n+2 ↔ k = Fin.last (n+2) by
        intro k; exact ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩]
    simp [impulseMatrix]
    ring



private def endsEquiv (n : ℕ) : Fin 2 ⊕ Fin (n+1) ≃ Fin (n+3) :=
  (Equiv.sumCongr (finSumFinEquiv : Fin 1 ⊕ Fin 1 ≃ Fin 2).symm
    (Equiv.refl (Fin (n+1)))).trans
    ((Equiv.sumAssoc (Fin 1) (Fin 1) (Fin (n+1))).trans
      ((Equiv.sumCongr (Equiv.refl (Fin 1)) (Equiv.sumComm (Fin 1) (Fin (n+1)))).trans
        ((Equiv.sumCongr (Equiv.refl (Fin 1))
          (finSumFinEquiv : Fin (n+1) ⊕ Fin 1 ≃ Fin (n+2))).trans
          ((finSumFinEquiv : Fin 1 ⊕ Fin (n+2) ≃ Fin (1+(n+2))).trans
            (finCongr (by omega))))))

@[simp] private lemma endsEquiv_zero (n : ℕ) : endsEquiv n (.inl ⟨0, by decide⟩) = 0 := by
  apply Fin.ext
  simp [endsEquiv, finSumFinEquiv, Fin.addCases]
@[simp] private lemma endsEquiv_one (n : ℕ) : endsEquiv n (.inl ⟨1, by decide⟩) = Fin.last (n+2) := by
  apply Fin.ext
  simp [endsEquiv, finSumFinEquiv, Fin.addCases]
@[simp] private lemma endsEquiv_right (n : ℕ) (i : Fin (n+1)) :
    endsEquiv n (.inr i) = ⟨i.val+1, by omega⟩ := by
  apply Fin.ext
  simp [endsEquiv, finSumFinEquiv, Nat.add_comm]

private lemma impulse_tail (d : ℕ → R) {j : ℕ} (hj : j < 2) (i : ℕ) :
    impulse d j (i+2) = d (i+1)*impulse d j (i+1)-impulse d j i := by
    simp [impulse, show j ≠ i+2 by omega]

private def boundary (n : ℕ) (d : ℕ → R) : Matrix (Fin 2) (Fin 2) R :=
  !![-1-impulse d 1 (n+2), d 0-impulse d 0 (n+2);
      impulse d 1 (n+3), impulse d 0 (n+3)-1]

private lemma cycleDiag_det_boundary (n : ℕ) (d : ℕ → R) :
    (cycleDiag (n+3) d).det = -(boundary n d).det := by
    let A := cycleDiag (n+3) d
    let H := (A * impulseMatrix (n+3) d).submatrix id (finRotate (n+3))
    let Q : Matrix (Fin 2) (Fin (n+1)) R :=
      fun i j => H (endsEquiv n (.inl i)) (endsEquiv n (.inr j))
    have hrotate (i : Fin (n+1)) :
        finRotate (n+3) i.succ.castSucc = i.succ.succ := by
      exact finRotate_of_lt (Nat.succ_lt_succ i.isLt)
    have hblock : H.submatrix (endsEquiv n) (endsEquiv n) =
        Matrix.fromBlocks (boundary n d) Q 0 ((-1 : R) • (1 : Matrix (Fin (n+1)) (Fin (n+1)) R)) := by
      ext i j
      rcases i with i | i <;> rcases j with j | j
      · fin_cases i <;> fin_cases j
        all_goals simp only [Matrix.submatrix_apply, endsEquiv_zero, endsEquiv_one,
          Matrix.fromBlocks_apply₁₁, H, id_eq, A]
        · change (cycleDiag (n+3) d * impulseMatrix (n+3) d) 0 (finRotate (n+3) 0) =
            -1-impulse d 1 (n+2)
          rw [finRotate_apply_zero, cycle_mul_first]
          simp [impulse]
        · change (cycleDiag (n+3) d * impulseMatrix (n+3) d) 0
            (finRotate (n+3) (Fin.last (n+2))) = d 0-impulse d 0 (n+2)
          rw [finRotate_last, cycle_mul_first]
          simp [impulse]
        · change (cycleDiag (n+3) d * impulseMatrix (n+3) d) (Fin.last (n+2))
            (finRotate (n+3) 0) = impulse d 1 (n+3)
          rw [finRotate_apply_zero, cycle_mul_last, impulse_tail d (by omega : 1 < 2) (n+1)]
          simp [impulse, show n+1+1 = n+2 by omega]
        · change (cycleDiag (n+3) d * impulseMatrix (n+3) d) (Fin.last (n+2))
            (finRotate (n+3) (Fin.last (n+2))) = impulse d 0 (n+3)-1
          rw [finRotate_last, cycle_mul_last, impulse_tail d (by omega : 0 < 2) (n+1)]
          simp [impulse, show n+1+1 = n+2 by omega]
      · rfl
      · fin_cases j <;>
          simp only [Matrix.submatrix_apply, endsEquiv_zero, endsEquiv_one,
            endsEquiv_right, Matrix.fromBlocks_apply₂₁, H, id_eq, A,
            finRotate_apply_zero, finRotate_last, cycle_mul_middle, Matrix.zero_apply]
        all_goals simp [show 1 ≠ i.val+2 by omega, show 0 ≠ i.val+2 by omega]
      · simp only [Matrix.submatrix_apply, endsEquiv_right, H, id_eq, A, hrotate,
          cycle_mul_middle, Matrix.fromBlocks_apply₂₂, Matrix.smul_apply,
          Matrix.one_apply, smul_eq_mul]
        by_cases hij : i = j
        · subst j
          simp [hrotate, Fin.val_add, Fin.val_one,
            Nat.mod_eq_of_lt (show i.val+1+1 < n+3 by omega)]
        · have hv : i.val ≠ j.val := fun h => hij (Fin.ext h)
          simp [Fin.ext_iff, hv, Ne.symm hv, hrotate, Fin.val_add, Fin.val_one,
            Nat.mod_eq_of_lt (show j.val+1+1 < n+3 by omega)]
    have hp : H.det = (-1 : R)^(n+2) * A.det := by
      dsimp only [H]
      rw [Matrix.det_permute', Matrix.det_mul, impulseMatrix_det, mul_one,
        sign_finRotate]
      simp
    have hd : H.det = (boundary n d).det * (-1 : R)^(n+1) := by
      rw [← Matrix.det_submatrix_equiv_self (endsEquiv n) H, hblock,
        Matrix.det_fromBlocks_zero₂₁, Matrix.det_smul, Matrix.det_one]
      simp
    have he := hp.symm.trans hd
    let t : R := (-1 : R)^(n+1)
    have ht : t*t = 1 := by dsimp [t]; rw [← mul_pow]; simp
    rw [show n+2 = (n+1)+1 by omega, pow_succ] at he
    change t * (-1) * A.det = (boundary n d).det * t at he
    change A.det = -(boundary n d).det
    linear_combination -t * he - (A.det + (boundary n d).det) * ht

def transfer {K : Type*} [Ring K] (d : K) : Matrix (Fin 2) (Fin 2) K :=
  !![d, -1; 1, 0]

def evolution {K : Type*} [Ring K] (d : ℕ → K) :
    ℕ → Matrix (Fin 2) (Fin 2) K
  | 0 => 1
  | n + 1 => transfer (d n) * evolution d n

lemma transfer_det {K : Type*} [CommRing K] (d : K) :
    (transfer d).det = 1 := by
  simp [transfer, Matrix.det_fin_two]

lemma evolution_add {K : Type*} [Ring K] (d : ℕ → K) (n k : ℕ) :
    evolution d (n + k) = evolution (fun i => d (n + i)) k * evolution d n := by
  induction k with
  | zero => simp [evolution]
  | succ k ih =>
    change transfer (d (n + k)) * evolution d (n + k) =
      (transfer (d (n + k)) * evolution (fun i => d (n + i)) k) * evolution d n
    rw [ih, mul_assoc]


lemma evolution_det {K : Type*} [CommRing K] (d : ℕ → K) (n : ℕ) :
    (evolution d n).det = 1 := by
  induction n with
  | zero => simp [evolution]
  | succ n ih => simp [evolution, Matrix.det_mul, transfer_det, ih]


private lemma tailTransfer_entries (d : ℕ → R) (n : ℕ) :
    evolution (fun i => d (i+1)) n = !![impulse d 1 (n+1), impulse d 0 (n+1);
      impulse d 1 n, impulse d 0 n] := by
    induction n with
    | zero => ext i j; fin_cases i <;> fin_cases j <;> simp [evolution, impulse]
    | succ n ih =>
        rw [evolution, ih]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [transfer, Matrix.mul_apply, Fin.sum_univ_two, impulse,
            show 0 ≠ n+2 by omega, show 1 ≠ n+2 by omega] <;> ring

private lemma tailTransfer_full (d : ℕ → R) (n : ℕ) :
    evolution (fun i => d (i+1)) n * transfer (d 0) = evolution d (n+1) := by
    simpa only [Nat.add_comm, evolution, mul_one] using (evolution_add d 1 n).symm

/-- The cyclic tridiagonal determinant is the transfer trace minus two, over any commutative ring. -/
theorem cycleDiag_det_transfer (n : ℕ) (d : ℕ → R) :
    (cycleDiag (n+3) d).det = (evolution d (n+3)).trace - 2 := by
    have hd := evolution_det (fun i => d (i+1)) (n+2)
    rw [tailTransfer_entries, Matrix.det_fin_two] at hd
    rw [cycleDiag_det_boundary, ← tailTransfer_full d (n+2), tailTransfer_entries]
    simp [boundary, transfer, Matrix.trace_fin_two, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.det_fin_two] at *
    linear_combination -hd

end D5.S3.Combinatorics.SpectralGraph.CyclicTridiagonalTransferTrace
