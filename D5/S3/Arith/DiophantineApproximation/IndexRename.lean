/- GID: D5/S3/Arith/DiophantineApproximation/IndexRename
   generality: G
   mirror-B: D5/B/S3/Arith/DiophantineApproximation/IndexRename
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Renaming and cardinality control the index of a multivariate polynomial. -/
/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
Adapted for trureturing: module namespace, pinned-library compatibility, and direct library reuse.
-/
module

public import D5.S3.Arith.DiophantineApproximation.BoxMonomial
public import D5.S3.Arith.DiophantineApproximation.PolynomialIndex

@[expose] public section

open Nat

open Finsupp Function

open scoped ENNReal

namespace MvPolynomial

section Rename

variable {σ τ R : Type*} [CommSemiring R] {e : σ → τ}

/-- **A Hasse derivative commutes with an injective renaming**, once the order is renamed too. -/
theorem hasseDeriv_rename (he : Injective e) (μ : σ →₀ ℕ) (P : MvPolynomial σ R) :
    hasseDeriv (μ.mapDomain e) (rename e P) = rename e (hasseDeriv μ P) := by
  have hasseDeriv_apply :
      (∀ (μ : σ →₀ ℕ) (P : MvPolynomial σ R),
        MvPolynomial.hasseDeriv μ P = ∑ m ∈ P.support,
          MvPolynomial.monomial (m - μ) ((μ.prod fun j k ↦ (m j).choose k : ℕ) * P.coeff m)) ∧
      (∀ (μ : τ →₀ ℕ) (P : MvPolynomial τ R),
        MvPolynomial.hasseDeriv μ P = ∑ m ∈ P.support,
          MvPolynomial.monomial (m - μ) ((μ.prod fun j k ↦ (m j).choose k : ℕ) * P.coeff m)) := by
    constructor
    all_goals
      intro μ P
      rw [MvPolynomial.hasseDeriv, Module.Basis.constr_apply]
      rw [show (MvPolynomial.basisMonomials _ R).repr P = AddMonoidAlgebra.coeff P from rfl,
        MvPolynomial.sum_def]
      exact Finset.sum_congr rfl fun m _ ↦ by rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_comm]
  have prod_choose_eq_zero :
      (∀ {μ m : σ →₀ ℕ}, ¬ μ ≤ m → (μ.prod fun j k ↦ (m j).choose k) = 0) ∧
      (∀ {μ m : τ →₀ ℕ}, ¬ μ ≤ m → (μ.prod fun j k ↦ (m j).choose k) = 0) := by
    constructor
    all_goals
      intro μ m h
      rw [Finsupp.le_def] at h
      push Not at h
      obtain ⟨j, hj⟩ := h
      exact Finset.prod_eq_zero (i := j) (Finsupp.mem_support_iff.mpr (by omega))
        (Nat.choose_eq_zero_of_lt hj)
  have hasseDeriv_coeff :
      (∀ (μ : σ →₀ ℕ) (P : MvPolynomial σ R) (n : σ →₀ ℕ),
        (MvPolynomial.hasseDeriv μ P).coeff n
          = ((μ.prod fun j k ↦ (n j + k).choose k : ℕ) : R) * P.coeff (n + μ)) ∧
      (∀ (μ : τ →₀ ℕ) (P : MvPolynomial τ R) (n : τ →₀ ℕ),
        (MvPolynomial.hasseDeriv μ P).coeff n
          = ((μ.prod fun j k ↦ (n j + k).choose k : ℕ) : R) * P.coeff (n + μ)) := by
    constructor
    all_goals
      intro μ P n
      classical
      first
      | rw [hasseDeriv_apply.1, MvPolynomial.coeff_sum]
      | rw [hasseDeriv_apply.2, MvPolynomial.coeff_sum]
      simp only [MvPolynomial.coeff_monomial]
      rw [Finset.sum_eq_single (n + μ)]
      · rw [if_pos (add_tsub_cancel_right n μ)]
        have h : (μ.prod fun j k ↦ ((n + μ) j).choose k) = μ.prod fun j k ↦ (n j + k).choose k :=
          Finsupp.prod_congr fun j _ ↦ by rw [Finsupp.add_apply]
        rw [h]
      · intro m _ hne
        by_cases h : m - μ = n
        · rw [if_pos h]
          have hle : ¬ μ ≤ m := fun hle ↦ hne (by rw [← h, tsub_add_cancel_of_le hle])
          first
          | rw [prod_choose_eq_zero.1 hle]
          | rw [prod_choose_eq_zero.2 hle]
          simp
        · rw [if_neg h]
      · intro h
        rw [notMem_support_iff.mp h]
        simp
  have hCoeffOff : ∀ {Q : MvPolynomial σ R} {ρ : τ →₀ ℕ},
      ¬ ((ρ.support : Set τ) ⊆ Set.range e) → (rename e Q).coeff ρ = 0 := by
    intro Q ρ hρ
    classical
    refine coeff_rename_eq_zero _ _ _ fun u hu ↦ absurd (fun t ht ↦ ?_) hρ
    rw [← hu] at ht
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp (mapDomain_support (Finset.mem_coe.mp ht))
    exact ⟨a, rfl⟩
  classical
  refine MvPolynomial.ext _ _ fun n ↦ ?_
  by_cases hn : (n.support : Set τ) ⊆ Set.range e
  · obtain ⟨n', rfl⟩ : ∃ n' : σ →₀ ℕ, n'.mapDomain e = n :=
      ⟨comapDomain e n (he.injOn), mapDomain_comapDomain e he n hn⟩
    rw [hasseDeriv_coeff.2, coeff_rename_mapDomain _ he, hasseDeriv_coeff.1,
      ← mapDomain_add, coeff_rename_mapDomain _ he]
    congr 1
    rw [Finsupp.prod_mapDomain_index_inj he]
    exact congrArg _ (Finsupp.prod_congr fun j _ ↦
      congrArg (fun t ↦ (t + μ j).choose (μ j)) (Finsupp.mapDomain_apply he n' j))
  · obtain ⟨j, hj, hjr⟩ : ∃ j, n j ≠ 0 ∧ j ∉ Set.range e := by
      by_contra h
      exact hn (fun j hj ↦ by
        by_contra hjr
        exact h ⟨j, Finsupp.mem_support_iff.mp (Finset.mem_coe.mp hj), hjr⟩)
    have hns : ¬ (((n + μ.mapDomain e).support : Set τ) ⊆ Set.range e) := fun hs ↦
      hjr (hs (by simp only [Finset.mem_coe, Finsupp.mem_support_iff, Finsupp.add_apply]; omega))
    rw [hasseDeriv_coeff.2, hCoeffOff hns, mul_zero, hCoeffOff hn]

end Rename

section IndexRename

variable {σ τ R : Type*} [CommRing R] {e : σ → τ}

end IndexRename

section Shapes

variable {σ R : Type*} [CommRing R] (d : σ → ℝ)

end Shapes

section Card

variable {σ R : Type*} [Fintype σ] [CommRing R] {d : σ → ℝ}

/-- **A polynomial of partial degrees at most `d` has index at most the number of variables.**
The bound is what keeps the conclusion of Roth's lemma non-vacuous once the parameter `σ` of the
lemma is close to `1`. -/
theorem index_le_card (hd : ∀ j, 0 < d j) {P : MvPolynomial σ R} (hP : P ≠ 0)
    (hdeg : ∀ j, (P.degreeOf j : ℝ) ≤ d j) (α : σ → R) :
    index d α P ≤ (Fintype.card σ : ℝ≥0∞) := by
  classical
  have ht : taylorAt α P ≠ 0 := by
    intro h
    have hleft : (taylorAt (-α)).comp (taylorAt α) =
        AlgHom.id R (MvPolynomial σ R) := by
      apply MvPolynomial.algHom_ext
      intro j
      rw [AlgHom.comp_apply, AlgHom.id_apply,
        show taylorAt α (X j) = X j + C (α j) from aeval_X _ _]
      rw [map_add,
        show taylorAt (-α) (X j) = X j + C ((-α) j) from aeval_X _ _,
        show taylorAt (-α) (C (α j)) = C (α j) from aeval_C _ _]
      simp only [Pi.neg_apply, add_assoc, ← C_add, neg_add_cancel, C_0, add_zero]
    have hzero : P = 0 := by
      calc
        P = taylorAt (-α) (taylorAt α P) := (AlgHom.congr_fun hleft P).symm
        _ = taylorAt (-α) 0 := congrArg (taylorAt (-α)) h
        _ = 0 := map_zero _
    exact hP hzero
  obtain ⟨μ, hμ⟩ : ∃ μ, (taylorAt α P).coeff μ ≠ 0 := by
    by_contra hc
    push Not at hc
    exact ht (MvPolynomial.ext _ _ fun ν ↦ by simp [hc ν])
  have hne : eval α (hasseDeriv μ P) ≠ 0 := by rwa [← coeff_taylorAt]
  have hbound : ∀ j, (μ j : ℝ) ≤ d j := fun j ↦ by
    by_contra hlt
    exact hne (by rw [hasseDeriv_eq_zero_of_lt (j := j)
      (by exact_mod_cast lt_of_le_of_lt (hdeg j) (not_le.mp hlt)), map_zero])
  refine le_trans ((fun (d : _ → ℝ) {α : _ → _} {P : MvPolynomial _ _} {μ : _ →₀ ℕ}
      (h : MvPolynomial.eval α (MvPolynomial.hasseDeriv μ P) ≠ 0) ↦
      (show MvPolynomial.index d α P ≤ ENNReal.ofReal (μ.sum fun j k ↦ k / d j) from
        iInf_le_of_le μ (iInf_le _ h))) d hne) ?_
  rw [← ENNReal.ofReal_natCast]
  refine ENNReal.ofReal_le_ofReal ?_
  calc (μ.sum fun j k ↦ (k : ℝ) / d j) = ∑ j ∈ μ.support, (μ j : ℝ) / d j := rfl
    _ ≤ ∑ _j ∈ μ.support, (1 : ℝ) :=
        Finset.sum_le_sum fun j _ ↦ (div_le_one (hd j)).mpr (hbound j)
    _ ≤ (Fintype.card σ : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        exact_mod_cast Finset.card_le_univ μ.support

end Card

end MvPolynomial
