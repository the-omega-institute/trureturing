/- GID: D5/S1/Recurrence/Algebraic/RatajczakTTransformDeterminant
   generality: I
   mirror-B: D5/B/S1/Recurrence/Algebraic/RatajczakTTransformDeterminant
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Determinant.Basic, mathlib/module/Mathlib.LinearAlgebra.Matrix.Block]
   utility: none
   digest: Ratajczak's T-transform determinant is A110491 in every order. -/

/- Formalization classification:
   proof_shape: result: content
   escape_witness: the literal determinant is reduced to a source-specific tridiagonal
     continuant and proved to satisfy the independently defined A110491 recurrence
   admission_basis: open-problem-resolution (issue #9591)
   Direct frozen dependencies: none (pinned Mathlib only)
-/

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

open Matrix

namespace D5.S1.Recurrence.Algebraic.RatajczakTTransformDeterminant

/-- A093178, with the source's indexing from zero. -/
def sourceB (r : ℕ) : ℤ := if Even r then 1 else r

/-- A110491, independently specified by its order-two recurrence. -/
def sourceA : ℕ → ℤ
  | 0 => 1
  | 1 => 2
  | m + 2 =>
      2 * sourceA (m + 1) + 4 * (m + 1 : ℕ) * (m : ℕ) * sourceA m

/-- The literal matrix in Ratajczak's T-transform comment on A110491. -/
def sourceMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℤ := fun i j =>
  let i1 := i.val + 1
  let j1 := j.val + 1
  if i1 > j1 then sourceB (2 * j1) else sourceB (i1 + j1 - 1)

/-- The determinant in Ratajczak's T-transform formula is A110491 in every order. -/
theorem result (m : ℕ) :
    (sourceMatrix (m + 1)).det = sourceA m := by
  classical
  let M := sourceMatrix (m + 1)
  let R : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ := fun i j =>
    Fin.cases (M 0 j) (fun k => M k.succ j - M (Fin.castSucc k) j) i
  let H : Matrix (Fin m) (Fin m) ℤ := fun p q =>
    if p.val = q.val + 1 then -2 * (p.val : ℤ)
    else if p.val ≤ q.val then
      if (p.val + q.val) % 2 = 0 then (p.val + q.val + 2 : ℕ)
      else -(p.val + q.val + 1 : ℕ)
    else 0
  let S : Matrix (Fin m) (Fin m) ℤ :=
    Matrix.diagonal fun p => (-1 : ℤ) ^ (p.val + 1)
  let L : Matrix (Fin m) (Fin m) ℤ := fun p q =>
    if p.val = q.val + 1 then p.val
    else if p.val ≤ q.val then (((p.val + q.val + 2) / 2 : ℕ) : ℤ)
    else 0
  let B : Matrix (Fin m) (Fin m) ℤ := fun p q =>
    if p.val = q.val + 1 then p.val
    else if p.val ≤ q.val then if p.val % 2 = q.val % 2 then 1 else 0
    else 0
  let U2 : Matrix (Fin m) (Fin m) ℤ := fun p q =>
    (if p = q then 1 else 0) - (if p.val + 2 = q.val then 1 else 0)
  let Tn : (n : ℕ) → Matrix (Fin n) (Fin n) ℤ := fun _ p q =>
    if p = q then 1
    else if p.val = q.val + 1 then p.val
    else if q.val = p.val + 1 then -(p.val : ℤ)
    else 0
  let T := Tn m
  have hMR : M.det = R.det := by
    apply Matrix.det_eq_of_forall_row_eq_smul_add_pred (c := fun _ => 1)
    · intro j
      simp [R]
    · intro i j
      simp [R]
  have hR0 : R 0 0 = 1 := by
    simp [R, M, sourceMatrix, sourceB]
  have hRcol : ∀ i : Fin m, R i.succ 0 = 0 := by
    intro i
    simp [R, M, sourceMatrix, sourceB]
    split_ifs <;> simp_all
  have hRH : R.submatrix Fin.succ Fin.succ = H := by
    ext p q
    simp only [Matrix.submatrix_apply]
    simp [R, M, H, sourceMatrix, sourceB]
    split_ifs <;> simp_all [Nat.even_iff]
    all_goals omega
  have hMH : M.det = H.det := by
    rw [hMR, Matrix.det_succ_column_zero, Fin.sum_univ_succ]
    simp [hR0, hRcol, hRH]
  have hSHS : S * H * S = (2 : ℤ) • L := by
    have sign_mod (n : ℕ) :
        (-1 : ℤ) ^ n = if n % 2 = 0 then 1 else -1 := by
      rw [neg_one_pow_eq_pow_mod_two]
      rcases Nat.mod_two_eq_zero_or_one n with hn | hn <;> simp [hn]
    ext p q
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    change
      ((-1 : ℤ) ^ (p.val + 1) * H p q) * (-1 : ℤ) ^ (q.val + 1) =
        2 * L p q
    simp only [sign_mod, H, L]
    all_goals split_ifs <;> norm_num at *
    all_goals omega
  have hSS : S * S = (1 : Matrix (Fin m) (Fin m) ℤ) := by
    dsimp [S]
    rw [Matrix.diagonal_mul_diagonal]
    ext p q
    by_cases hpq : p = q
    · subst q
      simp [← mul_pow]
    · simp [hpq]
  have hHL : H.det = 2 ^ m * L.det := by
    have hdetSS : S.det * S.det = 1 := by
      rw [← Matrix.det_mul, hSS, Matrix.det_one]
    have hdetconj : (S * H * S).det = H.det := by
      rw [Matrix.det_mul, Matrix.det_mul]
      calc
        S.det * H.det * S.det = H.det * (S.det * S.det) := by ring
        _ = H.det := by rw [hdetSS, mul_one]
    rw [hSHS, Matrix.det_smul] at hdetconj
    simpa using hdetconj.symm
  have floor_step (a b : ℕ) :
      (((a + (b + 1) + 2) / 2 : ℕ) : ℤ) =
        (if a % 2 = (b + 1) % 2 then 1 else 0) +
          (((a + b + 2) / 2 : ℕ) : ℤ) := by
    rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
      rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;>
      simp_all [Nat.add_mod]
    all_goals omega
  have hLB : L.det = B.det := by
    cases m with
    | zero => simp
    | succ n =>
      apply Matrix.det_eq_of_forall_col_eq_smul_add_pred (c := fun _ => 1)
      · intro i
        simp [L, B]
        split_ifs <;> simp_all
      · intro i j
        by_cases htwo : i.val = j.val + 2
        · have hnold : ¬ i ≤ j.castSucc := by
            intro h
            change i.val ≤ j.val at h
            omega
          simp [L, B, htwo, hnold]
        by_cases hone : i.val = j.val + 1
        · have hnew : i ≤ j.succ := by
            change i.val ≤ j.val + 1
            omega
          simp [L, B, hone, hnew]
          omega
        by_cases hle : i.val ≤ j.val
        · have hold : i ≤ j.castSucc := by
            change i.val ≤ j.val
            exact hle
          have hnew : i ≤ j.succ := by
            change i.val ≤ j.val + 1
            omega
          have hf := floor_step i.val j.val
          simpa [L, B, htwo, hone, hold, hnew] using hf
        · have hnold : ¬ i ≤ j.castSucc := by
            intro h
            change i.val ≤ j.val at h
            omega
          have hnnew : ¬ i ≤ j.succ := by
            intro h
            change i.val ≤ j.val + 1 at h
            omega
          simp [L, B, htwo, hone, hnold, hnnew]
  have hBU : B * U2 = T := by
    ext p q
    rw [Matrix.mul_apply]
    simp only [U2, mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    by_cases hq : 2 ≤ q.val
    · let k : Fin m := ⟨q.val - 2, by omega⟩
      have hsum :
          (∑ x : Fin m, if x.val + 2 = q.val then B p x else 0) = B p k := by
        rw [Finset.sum_eq_single k]
        · rw [if_pos (by dsimp [k]; omega)]
        · intro x _ hx
          rw [if_neg]
          intro heq
          apply hx
          apply Fin.ext
          simp [k]
          omega
        · simp
      rw [hsum]
      simp only [B, T, Tn, k]
      split_ifs <;> omega
    · have hsum :
          (∑ x : Fin m, if x.val + 2 = q.val then B p x else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro x _
        rw [if_neg]
        omega
      rw [hsum, sub_zero]
      simp only [B, T, Tn]
      split_ifs <;> omega
  have hdetU2 : U2.det = 1 := by
    have hupper : U2.IsUpperTriangular := by
      intro p q hpq
      simp only [U2]
      have hpq' : q.val < p.val := hpq
      simp [Fin.ext_iff, ne_of_gt hpq', show ¬p.val + 2 = q.val by omega]
    rw [Matrix.det_of_isUpperTriangular hupper]
    simp [U2]
  have hBT : B.det = T.det := by
    have hdet := congrArg Matrix.det hBU
    rw [Matrix.det_mul, hdetU2, mul_one] at hdet
    exact hdet
  have det_sparse_front {n : ℕ}
      (A : Matrix (Fin (n + 2)) (Fin (n + 2)) ℤ)
      (hr : ∀ j : Fin n, A 0 j.succ.succ = 0)
      (hc : ∀ i : Fin n, A i.succ.succ 0 = 0) :
      A.det = A 0 0 * (A.submatrix Fin.succ Fin.succ).det -
        A 0 1 * A 1 0 *
          (A.submatrix (fun i : Fin n => i.succ.succ)
            (fun j : Fin n => j.succ.succ)).det := by
    rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp only [Fin.succ_zero_eq_one, Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero,
      Fin.val_succ, hr, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
    have hminor :
        (A.submatrix Fin.succ (1 : Fin (n + 2)).succAbove).det =
          A 1 0 * (A.submatrix (fun i : Fin n => i.succ.succ)
            (fun j : Fin n => j.succ.succ)).det := by
      rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
      simp only [Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero,
        Matrix.submatrix_apply]
      have hzero : (1 : Fin (n + 2)).succAbove 0 = 0 := by simp
      rw [hzero]
      simp only [hc, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
      congr 2
    rw [hminor]
    norm_num [Fin.val_one']
    ring
  have hTrec (n : ℕ) :
      (Tn (n + 2)).det = (Tn (n + 1)).det +
        ((n + 1 : ℕ) : ℤ) * (n : ℤ) * (Tn n).det := by
    let A := (Tn (n + 2)).submatrix (@Fin.revPerm (n + 2)) (@Fin.revPerm (n + 2))
    have hr : ∀ j : Fin n, A 0 j.succ.succ = 0 := by
      intro j
      change Tn (n + 2) ((@Fin.revPerm (n + 2)) 0)
        ((@Fin.revPerm (n + 2)) j.succ.succ) = 0
      simp only [Tn, Fin.ext_iff, Fin.revPerm_apply, Fin.val_rev, Fin.val_zero,
        Fin.val_succ]
      split_ifs <;> omega
    have hc : ∀ i : Fin n, A i.succ.succ 0 = 0 := by
      intro i
      change Tn (n + 2) ((@Fin.revPerm (n + 2)) i.succ.succ)
        ((@Fin.revPerm (n + 2)) 0) = 0
      simp only [Tn, Fin.ext_iff, Fin.revPerm_apply, Fin.val_rev, Fin.val_zero,
        Fin.val_succ]
      split_ifs <;> omega
    rw [← Matrix.det_submatrix_equiv_self (@Fin.revPerm (n + 2)) (Tn (n + 2)),
      det_sparse_front A hr hc]
    have htail : (A.submatrix Fin.succ Fin.succ).det = (Tn (n + 1)).det := by
      rw [← Matrix.det_submatrix_equiv_self (@Fin.revPerm (n + 1)) (Tn (n + 1))]
      congr 1
      ext i j
      change Tn (n + 2) ((@Fin.revPerm (n + 2)) i.succ)
          ((@Fin.revPerm (n + 2)) j.succ) =
        Tn (n + 1) ((@Fin.revPerm (n + 1)) i) ((@Fin.revPerm (n + 1)) j)
      simp only [Tn, Fin.ext_iff, Fin.revPerm_apply, Fin.val_rev, Fin.val_succ]
      split_ifs <;> omega
    have htail2 :
        (A.submatrix (fun i : Fin n => i.succ.succ)
          (fun j : Fin n => j.succ.succ)).det = (Tn n).det := by
      rw [← Matrix.det_submatrix_equiv_self (@Fin.revPerm n) (Tn n)]
      congr 1
      ext i j
      change Tn (n + 2) ((@Fin.revPerm (n + 2)) i.succ.succ)
          ((@Fin.revPerm (n + 2)) j.succ.succ) =
        Tn n ((@Fin.revPerm n) i) ((@Fin.revPerm n) j)
      simp only [Tn, Fin.ext_iff, Fin.revPerm_apply, Fin.val_rev, Fin.val_succ]
      split_ifs <;> omega
    rw [htail, htail2]
    have h00 : A 0 0 = 1 := by
      change Tn (n + 2) ((@Fin.revPerm (n + 2)) 0) ((@Fin.revPerm (n + 2)) 0) = 1
      simp [Tn]
    have h01 : A 0 1 = (n + 1 : ℕ) := by
      change Tn (n + 2) ((@Fin.revPerm (n + 2)) 0) ((@Fin.revPerm (n + 2)) 1) =
        (n + 1 : ℕ)
      simp only [Tn, Fin.ext_iff, Fin.revPerm_apply, Fin.val_rev, Fin.val_zero,
        Fin.val_one']
      split_ifs <;> norm_num at *
    have h10 : A 1 0 = -(n : ℤ) := by
      change Tn (n + 2) ((@Fin.revPerm (n + 2)) 1) ((@Fin.revPerm (n + 2)) 0) =
        -(n : ℤ)
      simp only [Tn, Fin.ext_iff, Fin.revPerm_apply, Fin.val_rev, Fin.val_zero,
        Fin.val_one']
      split_ifs <;> norm_num at *; omega
    rw [h00, h01, h10]
    push_cast
    ring
  have hscale (n : ℕ) : 2 ^ n * (Tn n).det = sourceA n := by
    induction n using Nat.twoStepInduction with
    | zero =>
        rw [Matrix.det_fin_zero]
        norm_num [sourceA]
    | one =>
        rw [Matrix.det_fin_one]
        norm_num [Tn, sourceA]
    | more n ih0 ih1 =>
        rw [hTrec]
        calc
          2 ^ (n + 2) *
                ((Tn (n + 1)).det +
                  ((n + 1 : ℕ) : ℤ) * (n : ℤ) * (Tn n).det) =
              2 * (2 ^ (n + 1) * (Tn (n + 1)).det) +
                4 * ((n + 1 : ℕ) : ℤ) * (n : ℤ) * (2 ^ n * (Tn n).det) := by
            simp only [pow_succ]
            ring
          _ = 2 * sourceA (n + 1) +
                4 * ((n + 1 : ℕ) : ℤ) * (n : ℤ) * sourceA n := by
            rw [ih1, ih0]
          _ = sourceA (n + 2) := by rfl
  change M.det = sourceA m
  rw [hMH, hHL, hLB, hBT]
  exact hscale m

end D5.S1.Recurrence.Algebraic.RatajczakTTransformDeterminant
