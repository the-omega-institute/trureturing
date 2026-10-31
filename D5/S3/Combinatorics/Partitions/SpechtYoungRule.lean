/- GID: D5/S3/Combinatorics/Partitions/SpechtYoungRule
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/SpechtYoungRule
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual complex Specht-to-Young Hom dimensions are the tableau Kostka numbers. -/

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license. Authors: The Tau Ceti contributors.
Selected and adapted from TauCeti 5a01f5fe3621126cccf9ba22e700493cbc7b7156.
License, exact selections and consumers: Library/FiniteGroups/tauceti2026spechtpolytabloids.md.
Unfinished escape audit: https://github.com/the-omega-institute/trureturing/issues/24542.
-/
import D5.S3.Combinatorics.Partitions.SpechtSchurKostka
import Mathlib.Data.Matrix.Mul
import Mathlib.Order.WellFoundedSet

namespace D5.S3.Combinatorics.Partitions.SpechtPolytabloid
noncomputable section
open scoped BigOperators
namespace TauCeti
open Equiv MvPolynomial

theorem eq_of_transpose_mul_self_eq {ι R : Type*} [Fintype ι] [PartialOrder ι]
    [AddCancelCommMonoid R] [MulZeroOneClass R]
    {U V : Matrix ι ι R} (hU : ∀ i j, U i j ≠ 0 → j ≤ i) (hV : ∀ i j, V i j ≠ 0 → j ≤ i)
    (hU₁ : ∀ i, U i i = 1) (hV₁ : ∀ i, V i i = 1) (h : U.transpose * U = V.transpose * V) :
    U = V := by
  classical
  have : WellFoundedGT ι := Finite.to_wellFoundedGT
  ext i j

  induction i using WellFoundedGT.induction generalizing j with
  | _ i ih =>
  have hU0 : ∀ l, ¬ i ≤ l → U l i = 0 := fun l hl => not_ne_iff.mp (mt (hU l i) hl)
  have hV0 : ∀ l, ¬ i ≤ l → V l i = 0 := fun l hl => not_ne_iff.mp (mt (hV l i) hl)

  have hj := congrArg (fun M : Matrix ι ι R => M j i) h
  simp only [Matrix.mul_apply, Matrix.transpose_apply,
    ← Finset.add_sum_erase _ _ (Finset.mem_univ i), hU₁, hV₁, mul_one] at hj
  have hrest : ∑ l ∈ Finset.univ.erase i, U l j * U l i =
      ∑ l ∈ Finset.univ.erase i, V l j * V l i := Finset.sum_congr rfl fun l hl => by
    by_cases hil : i ≤ l
    · have hlt : i < l := lt_of_le_of_ne hil (Finset.ne_of_mem_erase hl).symm
      rw [ih l hlt, ih l hlt]
    · rw [hU0 l hil, hV0 l hil, mul_zero, mul_zero]
  rw [hrest] at hj
  exact add_right_cancel hj

/-- Young's rule for the independently constructed same-shape complex Specht modules. -/
theorem finrank_hom_spechtModuleℂ_permutationModuleℂ_eq_kostkaNumber {n : ℕ}
    (μ ν : n.Partition) :
    Module.finrank ℂ (spechtModuleℂ μ ⟶ permutationModuleℂ ν) = kostkaNumber μ ν := by
  classical
  letI : PartialOrder n.Partition :=
    { le := fun ξ ν => Dominates ν ξ
      le_refl := fun _ _ => le_rfl
      le_trans := fun _ _ _ h₁ h₂ k => (h₁ k).trans (h₂ k)
      le_antisymm := fun _ _ h₁ h₂ => Dominates.antisymm h₂ h₁ }
  let U : Matrix n.Partition n.Partition ℂ := fun λ ξ =>
    (Module.finrank ℂ (spechtModuleℂ λ ⟶ permutationModuleℂ ξ) : ℂ)
  let V : Matrix n.Partition n.Partition ℂ := fun λ ξ => (kostkaNumber λ ξ : ℂ)
  have hU : ∀ λ ξ, U λ ξ ≠ 0 → ξ ≤ λ := by
    intro λ ξ h
    change Dominates λ ξ
    by_contra hd
    exact h (by simp [U, finrank_hom_spechtModuleℂ_permutationModuleℂ_eq_zero hd])
  have hV : ∀ λ ξ, V λ ξ ≠ 0 → ξ ≤ λ := by
    intro λ ξ h
    change Dominates λ ξ
    by_contra hd
    exact h (by simp [V, kostkaNumber_eq_zero_of_not_dominates hd])
  have hU₁ : ∀ λ, U λ λ = 1 := by
    intro λ
    simp [U, finrank_hom_spechtModuleℂ_permutationModuleℂ_self]
  have hV₁ : ∀ λ, V λ λ = 1 := by intro λ; simp [V, kostkaNumber_self]
  have hgram : U.transpose * U = V.transpose * V := by
    ext ξ ζ
    have hζ : ζ.parts.card ≤ Fintype.card (Fin n) := by
      have h := Multiset.card_nsmul_le_sum (s := ζ.parts) (a := 1)
        fun x hx => ζ.parts_pos hx
      rw [smul_eq_mul, mul_one, ζ.parts_sum] at h
      simpa only [Fintype.card_fin] using h
    change (∑ λ : n.Partition,
      (Module.finrank ℂ (spechtModuleℂ λ ⟶ permutationModuleℂ ξ) : ℂ) *
        (Module.finrank ℂ (spechtModuleℂ λ ⟶ permutationModuleℂ ζ) : ℂ)) =
      ∑ λ : n.Partition, (kostkaNumber λ ξ : ℂ) * (kostkaNumber λ ζ : ℂ)
    rw [← coeff_hsymmPart_partWeight_eq_sum_multiplicity_mul (σ := Fin n) ξ ζ hζ]
    exact coeff_hsymmPart_partWeight (R := ℂ) ξ ζ
      (by rwa [YoungDiagram.colLen_zero_ofPartition])
  have hUV := eq_of_transpose_mul_self_eq hU hV hU₁ hV₁ hgram
  have h := congrArg (fun M : Matrix n.Partition n.Partition ℂ => M μ ν) hUV
  change (Module.finrank ℂ (spechtModuleℂ μ ⟶ permutationModuleℂ ν) : ℂ) =
    (kostkaNumber μ ν : ℂ) at h
  exact_mod_cast h

/-- Young's rule on the actual ordinary complex characters. -/
theorem char_permutationModuleℂ_eq_sum_kostkaNumber_mul_spechtTrace {n : ℕ}
    (ν : n.Partition) (π : Perm (Fin n)) :
    (permutationModuleℂ ν).character π = ∑ μ : n.Partition,
      (kostkaNumber μ ν : ℂ) * LinearMap.trace ℂ _ ((spechtModuleℂ μ).ρ π) := by
  rw [char_permutationModuleℂ_eq_sum_multiplicity_mul_spechtTrace]
  simp_rw [finrank_hom_spechtModuleℂ_permutationModuleℂ_eq_kostkaNumber]

/-- The same equality over the integers, with the full Young fixed-tabloid count. -/
theorem card_fixedPoints_eq_sum_kostkaNumber_mul_spechtChar {n : ℕ}
    (ν : n.Partition) (π : Perm (Fin n)) :
    (Nat.card {q : Perm (Fin n) ⧸ youngSubgroup ν // π • q = q} : ℤ) =
      ∑ μ : n.Partition, (kostkaNumber μ ν : ℤ) * spechtChar μ π := by
  have h := char_permutationModuleℂ_eq_sum_kostkaNumber_mul_spechtTrace ν π
  rw [char_permutationModuleℂ] at h
  change (Nat.card {q : Perm (Fin n) ⧸ youngSubgroup ν // π • q = q} : ℂ) =
    ∑ μ : n.Partition, (kostkaNumber μ ν : ℂ) * (spechtModuleℂ μ).character π at h
  simp only [character_spechtModuleℂ_intCast] at h
  exact_mod_cast h

end TauCeti
end
end D5.S3.Combinatorics.Partitions.SpechtPolytabloid
