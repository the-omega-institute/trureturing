/- GID: D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsPermanentPadding
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsPermanentPadding
   mirror-E: none(waiver:direct-Lean-proof-of-pan-skandera-wang-all-split-inequality)
   anchors: []
   utility: none
   digest: Identity padding preserves selected principal permanents. -/

/- Mathematical classification:
   principal_padOne:
     proof_shape: content
     escape_witness: permanent_padOption: decomposition of permutations that move the new coordinate
   split_padLeft:
     proof_shape: content
     escape_witness: principal_padOne: induction with the shifted initial split
   parity_padLeft:
     proof_shape: content
     escape_witness: principal_padOne: induction exchanging the old parity classes
   admission_basis: escape-witness
   utility reason: general statements at arbitrary orders, not a bounded certificate.
   Direct frozen dependencies:
     none (the frozen PSW theorem is used through the supporting modules).
   Information-escape registration is paused under CLAUDE.md section 3.9. -/

import D5.S3.Combinatorics.Permanental.PanSkanderaWangAllSplitsPadding

open Finset Matrix Equiv
namespace PSW
open scoped Classical

private def padOption {α : Type*} (M : Matrix α α ℝ) : Matrix (Option α) (Option α) ℝ
  | none, none => 1
  | none, some _ => 0
  | some _, none => 0
  | some i, some j => M i j

private theorem permanent_padOption {α : Type*} [DecidableEq α] [Fintype α] (M : Matrix α α ℝ) :
    (padOption M).permanent = M.permanent := by
  rw [Matrix.permanent, ← Perm.decomposeOption.symm.sum_comp, Fintype.sum_prod_type]
  rw [Fintype.sum_option]
  have hzero : ∀ i : α, (∑ σ : Perm α,
      ∏ k : Option α, padOption M (Perm.decomposeOption.symm (some i, σ) k) k) = 0 := by
    intro i
    apply Finset.sum_eq_zero
    intro σ _
    apply Finset.prod_eq_zero (mem_univ none)
    simp [padOption, Perm.decomposeOption_symm_apply, Perm.mul_apply]
  simp_rw [hzero]
  simp only [Finset.sum_const_zero, add_zero]
  unfold Matrix.permanent
  apply Finset.sum_congr rfl
  intro σ _
  simp [Fintype.prod_option, Perm.decomposeOption_symm_of_none_apply, padOption]

/-- The original part of any principal index set after one left identity padding. -/
def oldIndices {n : ℕ} (s : Finset (Fin (n + 1))) : Finset (Fin n) :=
  univ.filter (fun i => i.succ ∈ s)

private def succSubsetEquiv {n : ℕ} (s : Finset (Fin (n + 1))) (hs : (0 : Fin (n + 1)) ∉ s) :
    oldIndices s ≃ s where
  toFun i := ⟨i.val.succ, by simpa [oldIndices] using i.property⟩
  invFun i := ⟨i.val.pred (by intro h; exact hs (h ▸ i.property)), by
    simp only [oldIndices, mem_filter, mem_univ, true_and]
    simpa using i.property⟩
  left_inv i := by apply Subtype.ext; simp
  right_inv i := by apply Subtype.ext; simp

private def optionSubsetEquiv {n : ℕ} (s : Finset (Fin (n + 1))) (hs : (0 : Fin (n + 1)) ∈ s) :
    Option (oldIndices s) ≃ s where
  toFun
    | none => ⟨0, hs⟩
    | some i => ⟨i.val.succ, by simpa [oldIndices] using i.property⟩
  invFun i := if h : i.val = 0 then none else
    some ⟨i.val.pred h, by simp only [oldIndices, mem_filter, mem_univ, true_and]; simpa using i.property⟩
  left_inv i := by cases i with
    | none => simp
    | some i => simp [Fin.succ_ne_zero]
  right_inv i := by
    by_cases hi : i.val = 0
    · simp only [hi, ↓reduceDIte]; exact Subtype.ext hi.symm
    · simp [hi]

/-- An adjoined identity leaves the permanent of every selected principal block unchanged. -/
theorem principal_padOne {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (s : Finset (Fin (n + 1))) :
    principalPermanent (padOne A) s = principalPermanent A (oldIndices s) := by
  have permanent_reindex {α β : Type} [DecidableEq α] [Fintype α]
      [DecidableEq β] [Fintype β] (e : α ≃ β) (M : Matrix β β ℝ) : (M.submatrix e e).permanent = M.permanent := by
    unfold Matrix.permanent
    apply Fintype.sum_equiv (Equiv.permCongr e)
    intro σ
    apply Fintype.prod_equiv e
    intro i
    simp
  classical
  by_cases hs : (0 : Fin (n + 1)) ∈ s
  · let e := optionSubsetEquiv s hs
    have hm : ((padOne A).submatrix (fun i : s => i.val) (fun i : s => i.val)).submatrix e e =
        padOption (A.submatrix (fun i : oldIndices s => i.val) (fun i : oldIndices s => i.val)) := by
      ext i j
      cases i <;> cases j <;> rfl
    unfold principalPermanent
    rw [← permanent_reindex e, hm, permanent_padOption]
  · let e := succSubsetEquiv s hs
    have hm : ((padOne A).submatrix (fun i : s => i.val) (fun i : s => i.val)).submatrix e e =
        A.submatrix (fun i : oldIndices s => i.val) (fun i : oldIndices s => i.val) := by
      ext i j
      rfl
    unfold principalPermanent
    rw [← permanent_reindex e, hm]

/-- The split product and alternating parity product appearing in the exact target. -/
noncomputable def splitProduct {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (h : ℕ) : ℝ :=
  principalPermanent A (prefixIndices n h) * principalPermanent A (univ \ prefixIndices n h)

noncomputable def parityProduct {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  principalPermanent A (evenIndices n) * principalPermanent A (univ \ evenIndices n)

theorem split_padLeft {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (d h : ℕ) :
    splitProduct (padLeft A d) (h + d) = splitProduct A h := by
  have split_padOne {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (h : ℕ) :
      splitProduct (padOne A) (h + 1) = splitProduct A h := by
    have hprefix : oldIndices (prefixIndices (n + 1) (h + 1)) = prefixIndices n h := by
      ext i
      simp [oldIndices, prefixIndices]
    have hcompl : ∀ s : Finset (Fin (n + 1)),
        oldIndices (univ \ s) = univ \ oldIndices s := by
      intro s
      ext i
      simp [oldIndices]
    unfold splitProduct
    rw [principal_padOne, principal_padOne, hprefix,
      hcompl (prefixIndices (n + 1) (h + 1)), hprefix]
  induction d with
  | zero => rfl
  | succ d ih =>
    change splitProduct (padOne (padLeft A d)) ((h + d) + 1) = _
    rw [split_padOne, ih]

theorem parity_padLeft {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (d : ℕ) :
    parityProduct (padLeft A d) = parityProduct A := by
  have parity_padOne {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
      parityProduct (padOne A) = parityProduct A := by
    have heven : oldIndices (evenIndices (n + 1)) = univ \ evenIndices n := by
      ext i
      simp only [oldIndices, evenIndices, mem_filter, mem_univ, true_and, mem_sdiff, Fin.val_succ]
      omega
    have hcompl : ∀ s : Finset (Fin (n + 1)),
        oldIndices (univ \ s) = univ \ oldIndices s := by
      intro s
      ext i
      simp [oldIndices]
    have hcompleven : oldIndices (univ \ evenIndices (n + 1)) = evenIndices n := by
      rw [hcompl, heven]
      simp
    unfold parityProduct
    rw [principal_padOne, principal_padOne, heven, hcompleven]
    exact mul_comm _ _
  induction d with
  | zero => rfl
  | succ d ih => change parityProduct (padOne (padLeft A d)) = _; rw [parity_padOne, ih]

#print axioms principal_padOne
#print axioms split_padLeft
#print axioms parity_padLeft
end PSW
