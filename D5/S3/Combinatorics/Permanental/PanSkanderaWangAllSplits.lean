/- GID: D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplits
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Permanental/PanSkanderaWangAllSplits
   mirror-E: none(waiver:direct-Lean-proof-of-pan-skandera-wang-all-split-inequality)
   anchors: []
   utility: none
   digest: Every TNN matrix satisfies Pan-Skandera-Wang all-split inequality. -/

/- Mathematical classification:
   result:
     proof_shape: content
     escape_witness: lower_half and split_reverse/parity_reverse: identity-padding reduction
       to the balanced inequality and reversal transport to the complementary split
   admission_basis: open-problem-resolution (#13069; Proved)
   utility reason: general statements at arbitrary orders, not a bounded certificate.
   Direct frozen dependencies:
     none (the frozen PSW theorem is used through the supporting modules).
   Information-escape registration is paused under CLAUDE.md section 3.9. -/

import D5.S3.Combinatorics.Permanental.PanSkanderaWangAllSplitsBalanced
import D5.S3.Combinatorics.Permanental.PanSkanderaWangAllSplitsReverse

open Finset Matrix Equiv
namespace PSW

def claim : Prop := ∀ n : ℕ, 2 ≤ n → ∀ A : Matrix (Fin n) (Fin n) ℝ,
  TNN A → ∀ h : ℕ, 1 ≤ h → h ≤ n - 1 →
  principalPermanent A (evenIndices n) * principalPermanent A (univ \ evenIndices n) ≤
  principalPermanent A (prefixIndices n h) * principalPermanent A (univ \ prefixIndices n h)

/-- Every TNN real matrix satisfies Pan–Skandera–Wang's conjectured inequality at every split. -/
theorem result : claim := by
  let reverseEmbedding {k n : ℕ} (r : Fin k ↪o Fin n) : Fin k ↪o Fin n :=
    OrderEmbedding.ofStrictMono (fun i => (r i.rev).rev) (by
      intro i j hij
      apply Fin.rev_lt_rev.mpr
      exact r.strictMono (Fin.rev_lt_rev.mpr hij))
  have tnn_reverse {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : TNN A) : TNN (reverseMatrix A) := by
    intro k r c
    have hm : (reverseMatrix A).submatrix r c =
        (A.submatrix (reverseEmbedding r) (reverseEmbedding c)).submatrix Fin.revPerm Fin.revPerm := by
      ext i j
      simp [reverseMatrix, Matrix.submatrix_apply, reverseEmbedding, OrderEmbedding.ofStrictMono, Fin.revPerm]
    rw [hm, Matrix.det_submatrix_equiv_self]
    exact hA k (reverseEmbedding r) (reverseEmbedding c)
  let reverseIndices {n : ℕ} (s : Finset (Fin n)) : Finset (Fin n) := univ.filter (fun i => i.rev ∈ s)
  have permanent_reindex {α β : Type} [DecidableEq α] [Fintype α]
      [DecidableEq β] [Fintype β] (e : α ≃ β) (M : Matrix β β ℝ) : (M.submatrix e e).permanent = M.permanent := by
    unfold Matrix.permanent
    apply Fintype.sum_equiv (Equiv.permCongr e)
    intro σ
    apply Fintype.prod_equiv e
    intro i
    simp


  let reverseSubsetEquiv {n : ℕ} (s : Finset (Fin n)) : reverseIndices s ≃ s := {
    toFun i := ⟨i.val.rev, (Finset.mem_filter.mp i.property).2⟩
    invFun i := ⟨i.val.rev, by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, by simpa using i.property⟩⟩
    left_inv i := by apply Subtype.ext; simp
    right_inv i := by apply Subtype.ext; simp
  }
  have principal_reverse {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (s : Finset (Fin n)) :
      principalPermanent (reverseMatrix A) s = principalPermanent A (reverseIndices s) := by
    let e := reverseSubsetEquiv s
    have hm : ((reverseMatrix A).submatrix (fun i : s => i.val) (fun i : s => i.val)).submatrix e e =
        A.submatrix (fun i : reverseIndices s => i.val) (fun i : reverseIndices s => i.val) := by
      ext i j
      simp [reverseMatrix, e, reverseSubsetEquiv]
    unfold principalPermanent
    rw [← permanent_reindex e, hm]
  have split_reverse {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) {h : ℕ} (hh : h ≤ n) :
      splitProduct (reverseMatrix A) h = splitProduct A (n - h) := by
    have hcompl : ∀ s : Finset (Fin n),
        reverseIndices (univ \ s) = univ \ reverseIndices s := by
      intro s
      ext i
      simp [reverseIndices]
    have hprefix : reverseIndices (prefixIndices n h) = univ \ prefixIndices n (n - h) := by
      ext i
      simp only [reverseIndices, prefixIndices, mem_filter, mem_univ, true_and, mem_sdiff, not_lt]
      have hn := i.isLt
      simp only [Fin.val_rev]
      omega
    unfold splitProduct
    rw [principal_reverse, principal_reverse, hcompl, hprefix]
    simp [mul_comm]


  have parity_reverse {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
      parityProduct (reverseMatrix A) = parityProduct A := by
    have hcompl : ∀ s : Finset (Fin n),
        reverseIndices (univ \ s) = univ \ reverseIndices s := by
      intro s
      ext i
      simp [reverseIndices]
    have heven : reverseIndices (evenIndices n) =
        if n % 2 = 0 then univ \ evenIndices n else evenIndices n := by
      ext i
      simp only [reverseIndices, evenIndices, mem_filter, mem_univ, true_and]
      have hn := i.isLt
      rw [Fin.val_rev]
      split_ifs <;> simp only [mem_sdiff, mem_filter, mem_univ, true_and] <;> omega
    unfold parityProduct
    rw [principal_reverse, principal_reverse, hcompl, heven]
    split_ifs
    · simp [mul_comm]
    · rfl
  have lower_half : ∀ {n h : ℕ}, 3 ≤ n → 1 ≤ h → 2 * h ≤ n →
      ∀ {A : Matrix (Fin n) (Fin n) ℝ}, TNN A → parityProduct A ≤ splitProduct A h := by
    intro n h hn hh1 hhalf A hA
    let d := n - 2 * h
    have hN : 4 ≤ n + d := by dsimp [d]; omega
    have hmid : (n + d) / 2 = h + d := by dsimp [d]; omega
    have hb := balanced hN (tnn_padLeft hA d)
    change parityProduct (padLeft A d) ≤ splitProduct (padLeft A d) ((n + d) / 2) at hb
    rw [hmid, parity_padLeft, split_padLeft] at hb
    exact hb
  intro n hn A hA h hh1 hhn
  change parityProduct A ≤ splitProduct A h
  have hhn' : h ≤ n := by omega
  by_cases hn2 : n = 2
  · subst n
    have hh : h = 1 := by omega
    subst h
    have he : evenIndices 2 = univ \ prefixIndices 2 1 := by
      ext i
      fin_cases i <;> simp [evenIndices, prefixIndices]
    unfold parityProduct splitProduct
    rw [he]
    have hc : (univ : Finset (Fin 2)) \ (univ \ prefixIndices 2 1) = prefixIndices 2 1 := by
      ext i
      simp
    rw [hc, mul_comm]
  · have hn3 : 3 ≤ n := by omega
    by_cases hhalf : 2 * h ≤ n
    · exact lower_half hn3 hh1 hhalf hA
    · have hk1 : 1 ≤ n - h := by omega
      have hkhalf : 2 * (n - h) ≤ n := by omega
      have hr := lower_half hn3 hk1 hkhalf (tnn_reverse hA)
      rw [parity_reverse, split_reverse A (by omega : n - h ≤ n), Nat.sub_sub_self hhn'] at hr
      exact hr

#print axioms result
end PSW
