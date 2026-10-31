/- GID: D5/S3/Combinatorics/Partitions/SpechtSchurAlternant
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/SpechtSchurAlternant
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Selected tableau and Schur suppliers for the ordinary Specht Frobenius comparison. -/

/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license. Authors: The Tau Ceti contributors.
Selected declarations from TauCeti 5a01f5fe3621126cccf9ba22e700493cbc7b7156.
Namespaces and root references adapted to the existing D5 source chain.
License, selection, consumers and retirement:
Library/FiniteGroups/tauceti2026spechtpolytabloids.md.
Unfinished escape audit: https://github.com/the-omega-institute/trureturing/issues/24542.
-/
import D5.S3.Combinatorics.Partitions.SpechtSchurBranching
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

namespace D5.S3.Combinatorics.Partitions.SpechtPolytabloid
noncomputable section
open scoped BigOperators

namespace TauCeti

open MvPolynomial Equiv Finset

variable (σ : Type*) [Fintype σ] [DecidableEq σ] (R : Type*) [CommRing R]

noncomputable def alternant (α : σ → ℕ) : MvPolynomial σ R :=
  (Matrix.of fun i j => (X i : MvPolynomial σ R) ^ α j).det

variable {σ R}

theorem alternant_def (α : σ → ℕ) :
    alternant σ R α = (Matrix.of fun i j => (X i : MvPolynomial σ R) ^ α j).det :=
  (rfl)

theorem alternant_eq_sum (α : σ → ℕ) :
    alternant σ R α = ∑ τ : Perm σ, Perm.sign τ • ∏ i, (X (τ i) : MvPolynomial σ R) ^ α i := by
  simp only [alternant_def, Matrix.det_apply, Matrix.of_apply]

theorem coeff_alternant (α : σ → ℕ) (d : σ →₀ ℕ) :
    (alternant σ R α).coeff d =
      ∑ τ ∈ univ.filter (fun τ : Perm σ => ⇑d ∘ ⇑τ = α), ((Perm.sign τ : ℤ) : R) := by
  rw [alternant_eq_sum, coeff_sum, sum_filter]
  refine sum_congr rfl fun τ _ => ?_
  have hprod : ∏ i, (X (τ i) : MvPolynomial σ R) ^ α i = ∏ k, (X k) ^ α (τ.symm k) := by
    rw [← Equiv.prod_comp τ fun k => (X k : MvPolynomial σ R) ^ α (τ.symm k)]
    simp
  have hiff : d = Finsupp.indicator (univ : Finset σ) (fun k _ => α (τ.symm k)) ↔
      ⇑d ∘ ⇑τ = α := by
    constructor
    · rintro rfl
      funext i
      simp
    · intro h
      ext k
      simp [← h]
  rw [Units.smul_def, zsmul_eq_mul, ← map_intCast (C : R →+* MvPolynomial σ R), coeff_C_mul,
    hprod, coeff_prod_X_pow]
  by_cases h : ⇑d ∘ ⇑τ = α <;> simp [hiff, h]

theorem coeff_alternant_of_injective {α : σ → ℕ} (hα : Function.Injective α) (τ : Perm σ) :
    (alternant σ R α).coeff (Finsupp.equivFunOnFinite.symm (α ∘ τ)) =
      ((Perm.sign τ : ℤ) : R) := by
  rw [coeff_alternant, sum_eq_single τ⁻¹]
  · simp
  · intro ρ hρ hne
    have hρ' : (α ∘ τ) ∘ ρ = α := by simpa using (mem_filter.1 hρ).2
    refine absurd ?_ hne
    ext i
    have hi : τ (ρ i) = i := hα (congrFun hρ' i)
    exact Perm.eq_inv_iff_eq.2 hi
  · intro h
    refine absurd (mem_filter.2 ⟨mem_univ _, ?_⟩) h
    funext i
    simp

theorem alternant_ne_zero_of_injective [Nontrivial R] {α : σ → ℕ} (hα : Function.Injective α) :
    alternant σ R α ≠ 0 := by
  intro h
  have := coeff_alternant_of_injective (R := R) hα 1
  simp [h] at this

@[simp]
theorem alternant_comp_perm (e : Perm σ) (α : σ → ℕ) :
    alternant σ R (α ∘ e) = Perm.sign e • alternant σ R α := by
  rw [alternant_def, alternant_def, Units.smul_def, zsmul_eq_mul, ← Matrix.det_permute']
  congr 1

theorem alternant_eq_zero_of_not_injective {α : σ → ℕ} (hα : ¬ Function.Injective α) :
    alternant σ R α = 0 := by
  simp only [Function.Injective, not_forall] at hα
  obtain ⟨i, j, hij, hne⟩ := hα
  exact Matrix.det_zero_of_column_eq hne fun k => by simp [hij]

theorem hsymm_mul_alternant (r : ℕ) (α : σ → ℕ) :
    hsymm σ R r * alternant σ R α =
      ∑ γ ∈ Finset.piAntidiag (Finset.univ : Finset σ) r,
        alternant σ R fun i => α i + γ i := by
  have hsum : ∀ (τ : Perm σ) (γ : σ → ℕ), ∑ i, γ (τ i) = ∑ i, γ i := fun τ γ =>
    Equiv.sum_comp τ γ

  have key : ∀ τ : Perm σ,
      ∑ γ ∈ Finset.piAntidiag (Finset.univ : Finset σ) r,
          ∏ i, (X (τ i) : MvPolynomial σ R) ^ γ i = hsymm σ R r := by
    intro τ
    rw [hsymm_eq_sum_piAntidiag]
    refine Finset.sum_nbij' (fun γ => γ ∘ τ.symm) (fun γ => γ ∘ τ) (fun γ hγ => ?_)
      (fun γ hγ => ?_) (fun γ _ => funext fun i => by simp) (fun γ _ => funext fun i => by simp)
      fun γ _ => ?_
    · simp only [Finset.mem_piAntidiag, Finset.mem_univ, implies_true, and_true,
        Function.comp_apply] at hγ ⊢
      rw [hsum τ.symm γ, hγ]
    · simp only [Finset.mem_piAntidiag, Finset.mem_univ, implies_true, and_true,
        Function.comp_apply] at hγ ⊢
      rw [hsum τ γ, hγ]
    · simp only [Function.comp_apply]
      rw [← Equiv.prod_comp τ fun k => (X k : MvPolynomial σ R) ^ γ (τ.symm k)]
      exact Finset.prod_congr rfl fun i _ => by rw [Equiv.symm_apply_apply]
  simp only [alternant_eq_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [mul_smul_comm, ← Finset.smul_sum]
  congr 1
  rw [← key τ, Finset.sum_mul]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => by rw [← pow_add, Nat.add_comm]

end TauCeti

end
end D5.S3.Combinatorics.Partitions.SpechtPolytabloid
