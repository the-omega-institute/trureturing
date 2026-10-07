/- GID: D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsBlock
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsBlock
   mirror-E: none(waiver:direct-Lean-proof-of-pan-skandera-wang-all-split-inequality)
   anchors: []
   utility: none
   digest: Complementary principal permanents expand over block-preserving permutations. -/

/- Mathematical classification:
   blockEquiv:
     proof_shape: content
     escape_witness: conclusion: verified equivalence of block pairs and preserving permutations
   permanent_block_expansion:
     proof_shape: content
     escape_witness: blockEquiv: constructed product-to-block permutation equivalence
   admission_basis: escape-witness
   utility reason: general statements at arbitrary orders, not a bounded certificate.
   Direct frozen dependencies:
     none (the frozen PSW theorem is used through the supporting modules).
   Information-escape registration is paused under CLAUDE.md section 3.9. -/

import D5.S3.Combinatorics.Permanental.PanSkanderaWangAllSplitsWord

open Finset Equiv
open D5.S3.Combinatorics.PanSkanderaWangBruhat
namespace PSW
open scoped Classical

/-- Permutations preserving one specified block, and hence its complement. -/
def Preserves {α : Type*} [DecidableEq α] (s : Finset α) (w : Perm α) : Prop :=
  ∀ i : α, w i ∈ s ↔ i ∈ s

private noncomputable def joinPerm {α : Type*} [DecidableEq α] (s : Finset α)
    (σ : Perm s) (τ : Perm {i : α // i ∉ s}) : Perm α :=
  Perm.ofSubtype σ * Perm.ofSubtype τ

noncomputable def blockEquiv {α : Type*} [DecidableEq α] (s : Finset α) :
    (Perm s × Perm {i : α // i ∉ s}) ≃ {w : Perm α // Preserves s w} := by
  have join_left (s : Finset α)
      (σ : Perm s) (τ : Perm {i : α // i ∉ s}) (i : s) : joinPerm s σ τ i = σ i := by
    rw [joinPerm, Perm.mul_apply, Perm.ofSubtype_apply_of_not_mem τ (fun h => h i.property),
      Perm.ofSubtype_apply_coe]
  have join_right (s : Finset α)
      (σ : Perm s) (τ : Perm {i : α // i ∉ s}) (i : {i : α // i ∉ s}) : joinPerm s σ τ i = τ i := by
    simp [joinPerm, Perm.mul_apply, Perm.ofSubtype_apply_coe,
      Perm.ofSubtype_apply_of_not_mem _ (τ i).property]
  exact {
    toFun v := ⟨joinPerm s v.1 v.2, by
      intro i
      by_cases hi : i ∈ s
      · have h := join_left s v.1 v.2 ⟨i, hi⟩
        simpa only [h, hi, iff_true] using (v.1 ⟨i, hi⟩).property
      · have h := join_right s v.1 v.2 ⟨i, hi⟩
        simpa only [h, hi, iff_false] using (v.2 ⟨i, hi⟩).property⟩
    invFun w := (w.1.subtypePerm w.2, w.1.subtypePerm (fun i => not_congr (w.2 i)))
    left_inv v := by
      apply Prod.ext
      · apply Equiv.ext
        intro i
        apply Subtype.ext
        simp only [Perm.subtypePerm_apply]
        exact join_left s v.1 v.2 i
      · apply Equiv.ext
        intro i
        apply Subtype.ext
        simp only [Perm.subtypePerm_apply]
        exact join_right s v.1 v.2 i
    right_inv w := by
      apply Subtype.ext
      apply Equiv.ext
      intro i
      by_cases hi : i ∈ s
      · have he := join_left s (w.1.subtypePerm w.2)
          (w.1.subtypePerm (fun i => not_congr (w.2 i))) ⟨i, hi⟩
        change joinPerm s (w.1.subtypePerm w.2)
          (w.1.subtypePerm (fun i => not_congr (w.2 i))) i = w.1 i at he
        exact he
      · have he := join_right s (w.1.subtypePerm w.2)
          (w.1.subtypePerm (fun i => not_congr (w.2 i))) ⟨i, hi⟩
        change joinPerm s (w.1.subtypePerm w.2)
          (w.1.subtypePerm (fun i => not_congr (w.2 i))) i = w.1 i at he
        exact he

  }

/-- Expand a product of two complementary principal permanents into block-preserving monomials. -/
theorem permanent_block_expansion {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (s : Finset (Fin n)) :
    principalPermanent A s * principalPermanent A (univ \ s) =
    ∑ w : {w : Perm (Fin n) // Preserves s w}, monomial A w.1 := by
  classical
  have join_left {α : Type} [DecidableEq α] (s : Finset α)
      (σ : Perm s) (τ : Perm {i : α // i ∉ s}) (i : s) : joinPerm s σ τ i = σ i := by
    rw [joinPerm, Perm.mul_apply, Perm.ofSubtype_apply_of_not_mem τ (fun h => h i.property),
      Perm.ofSubtype_apply_coe]
  have join_right {α : Type} [DecidableEq α] (s : Finset α)
      (σ : Perm s) (τ : Perm {i : α // i ∉ s}) (i : {i : α // i ∉ s}) : joinPerm s σ τ i = τ i := by
    simp [joinPerm, Perm.mul_apply, Perm.ofSubtype_apply_coe,
      Perm.ofSubtype_apply_of_not_mem _ (τ i).property]
  have permanent_row_sum {α : Type} [DecidableEq α] [Fintype α]
      (M : Matrix α α ℝ) : M.permanent = ∑ σ : Perm α, ∏ i : α, M i (σ i) := by
    simpa only [Matrix.permanent, Matrix.transpose_apply] using (Matrix.permanent_transpose M).symm
  let hcompl : ({i : Fin n // i ∈ univ \ s}) ≃ {i : Fin n // i ∉ s} :=
    Equiv.subtypeEquivRight (fun i => by simp)
  have hper : principalPermanent A (univ \ s) =
      (A.submatrix (fun i : {i : Fin n // i ∉ s} => i.val) (fun i : {i : Fin n // i ∉ s} => i.val)).permanent := by
    unfold principalPermanent Matrix.permanent
    apply Fintype.sum_equiv (Equiv.permCongr hcompl)
    intro σ
    apply Fintype.prod_equiv hcompl
    intro i
    simp [hcompl]
  rw [hper]
  unfold principalPermanent
  rw [permanent_row_sum, permanent_row_sum, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  simp only [Matrix.submatrix_apply]
  change (∑ σ : Perm s, ∑ τ : Perm {i : Fin n // i ∉ s},
    (∏ i : s, A i (σ i)) * (∏ i : {i : Fin n // i ∉ s}, A i (τ i))) = _
  rw [← Fintype.sum_prod_type (fun v : Perm s × Perm {i : Fin n // i ∉ s} =>
    (∏ i : s, A i (v.1 i)) * (∏ i : {i : Fin n // i ∉ s}, A i (v.2 i)))]
  rw [← (blockEquiv s).sum_comp]
  apply Finset.sum_congr rfl
  rintro ⟨σ, τ⟩ _
  change (∏ i : s, A i (σ i)) * (∏ i : {i : Fin n // i ∉ s}, A i (τ i)) =
    ∏ i : Fin n, A i (joinPerm s σ τ i)
  rw [← (Equiv.sumCompl (fun i : Fin n => i ∈ s)).prod_comp]
  simp only [Fintype.prod_sum_type, Equiv.sumCompl_apply_inl, Equiv.sumCompl_apply_inr]
  congr 1
  · apply Finset.prod_congr rfl
    intro i _
    rw [join_left]
  · apply Finset.prod_congr rfl
    intro i _
    rw [join_right]

#print axioms permanent_block_expansion
end PSW
