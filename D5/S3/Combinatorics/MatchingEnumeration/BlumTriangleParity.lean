/- GID: D5/S3/Combinatorics/MatchingEnumeration/BlumTriangleParity
   generality: G
   mirror-B: D5/B/S3/Combinatorics/MatchingEnumeration/BlumTriangleParity
   mirror-E: none(waiver:general-matching-parity)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Determinant.Basic]
   utility: none
   digest: Permutation inversion proves determinant and matching parity agree. -/

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.MatchingEnumeration.BlumTriangleParity

open Finset Matrix

/-- For a symmetric zero-diagonal zero-one matrix in characteristic two, its determinant
counts the edge-supported fixed-point-free involutions, represented as vertex functions. -/
theorem determinant_matching_parity {V K : Type*} [Fintype V] [DecidableEq V]
    [CommRing K] [Nontrivial K] [CharP K 2] (A : Matrix V V K)
    (hsymm : Aᵀ = A) (hdiag : ∀ v, A v v = 0)
    (hbits : ∀ v w, A v w = 0 ∨ A v w = 1) :
    A.det = (Nat.card {σ : V → V //
      ∀ v, σ (σ v) = v ∧ σ v ≠ v ∧ A v (σ v) = 1} : K) := by
  classical
  let weight : Equiv.Perm V → K := fun σ => ∏ v, A (σ v) v
  have symmetric (v w : V) : A v w = A w v := by
    exact congrFun (congrFun hsymm w) v
  have reverse (σ : Equiv.Perm V) : weight σ⁻¹ = weight σ := by
    apply Fintype.prod_equiv σ.symm
    intro v
    simpa using symmetric (σ.symm v) v
  have expansion : A.det = ∑ σ : Equiv.Perm V, weight σ := by
    rw [Matrix.det_apply]
    apply sum_congr rfl
    intro σ _
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
    · simp [h, weight]
    · simp [h, weight, CharTwo.neg_eq]
  have cancel : (∑ σ ∈ univ.filter (fun σ : Equiv.Perm V => σ⁻¹ ≠ σ),
      weight σ) = 0 := by
    refine sum_involution (fun σ _ => σ⁻¹) ?_ ?_ ?_ ?_
    · intro σ _
      rw [reverse, CharTwo.add_self_eq_zero]
    · intro σ hσ _
      exact (mem_filter.mp hσ).2
    · intro σ hσ
      simp only [mem_filter, mem_univ, true_and, inv_inv]
      exact Ne.symm (mem_filter.mp hσ).2
    · intro σ _
      exact inv_inv σ
  have survivors : A.det = ∑ σ ∈ univ.filter (fun σ : Equiv.Perm V => σ⁻¹ = σ),
      weight σ := by
    rw [expansion, ← sum_filter_add_sum_filter_not univ
      (fun σ : Equiv.Perm V => σ⁻¹ = σ) weight, cancel, add_zero]
  let good : Equiv.Perm V → Prop := fun σ =>
    σ⁻¹ = σ ∧ ∀ v, A v (σ v) = 1
  have weights (σ : Equiv.Perm V) (hσ : σ⁻¹ = σ) :
      weight σ = if good σ then 1 else 0 := by
    by_cases h : ∀ v, A v (σ v) = 1
    · simp [weight, good, hσ, h, symmetric]
    · simp only [good, hσ, true_and, if_neg h]
      obtain ⟨v, hv⟩ := not_forall.mp h
      have hz : A (σ v) v = 0 := by
        rw [symmetric]
        exact (hbits v (σ v)).resolve_right hv
      exact prod_eq_zero (mem_univ v) hz
  have count : A.det = ((univ.filter good).card : K) := by
    rw [survivors]
    calc
      _ = ∑ σ ∈ univ.filter (fun σ : Equiv.Perm V => σ⁻¹ = σ),
          if good σ then (1 : K) else 0 := by
        apply sum_congr rfl
        intro σ hσ
        exact weights σ (mem_filter.mp hσ).2
      _ = ∑ σ ∈ univ.filter good, (1 : K) := by
        rw [← sum_filter]
        congr 1
        ext σ
        simp [good]
      _ = _ := by simp
  let e : {σ : Equiv.Perm V // good σ} ≃
      {σ : V → V // ∀ v, σ (σ v) = v ∧ σ v ≠ v ∧ A v (σ v) = 1} :=
    { toFun := fun σ => ⟨σ.1, fun v => by
        have invol : σ.1 (σ.1 v) = v := by
          have h := σ.1.symm_apply_apply v
          change σ.1⁻¹ (σ.1 v) = v at h
          rw [σ.2.1] at h
          exact h
        refine ⟨invol, ?_, σ.2.2 v⟩
        intro hv
        have h := σ.2.2 v
        rw [hv, hdiag] at h
        exact zero_ne_one h⟩
      invFun := fun σ =>
        ⟨{ toFun := σ.1
           invFun := σ.1
           left_inv := fun v => (σ.2 v).1
           right_inv := fun v => (σ.2 v).1 }, by
          constructor
          · rfl
          · intro v
            exact (σ.2 v).2.2⟩
      left_inv := fun σ => by
        apply Subtype.ext
        exact Equiv.ext (fun _ => rfl)
      right_inv := fun σ => by
        apply Subtype.ext
        rfl }
  rw [count, ← Fintype.card_subtype good, ← Nat.card_eq_fintype_card,
    Nat.card_congr e]

end D5.S3.Combinatorics.MatchingEnumeration.BlumTriangleParity
