/- GID: D5/S3/Combinatorics/Partitions/SpechtYoungCompleteness
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/SpechtYoungCompleteness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Completeness of actual Specht traces and the Young permutation multiplicity Gram identity. -/

/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license. Authors: The Tau Ceti contributors.
The class-function equivalence and basis construction adapt selected arguments in
TauCeti 5a01f5fe3621126cccf9ba22e700493cbc7b7156, CharacterTable/ClassFunction,
CharacterTable/Completeness and Symmetric/Specht/Basis. Existing D5 class-function
and pairing declarations supply the generic character theory. The literal Specht
row orthogonality supplies independence; no general irreducible enumeration is used.
License, source selection, adaptations and retirement:
Library/FiniteGroups/tauceti2026spechtpolytabloids.md.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/24542.
-/
import D5.S3.Combinatorics.Partitions.SpechtYoungTrace
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace D5.S3.Combinatorics.Partitions.SpechtPolytabloid
noncomputable section
open scoped BigOperators
open D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti (ClassFunction)

namespace TauCeti
open Equiv CategoryTheory
variable {n : ℕ}

private def classFunctionEquivConjClasses (n : ℕ) :
    ClassFunction ℂ (Perm (Fin n)) ≃ₗ[ℂ] (ConjClasses (Perm (Fin n)) → ℂ) where
  toFun := ClassFunction.toConjClasses
  invFun f := ⟨fun g => f (ConjClasses.mk g), fun g h => by
    apply congrArg f
    exact ConjClasses.mk_eq_mk_iff_isConj.mpr
      (IsConj.symm (isConj_iff.mpr ⟨h, rfl⟩))⟩
  map_add' f g := by
    ext C
    obtain ⟨x, rfl⟩ := ConjClasses.exists_rep C
    rfl
  map_smul' c f := by
    ext C
    obtain ⟨x, rfl⟩ := ConjClasses.exists_rep C
    rfl
  left_inv f := by ext g; rfl
  right_inv f := by
    ext C
    obtain ⟨x, rfl⟩ := ConjClasses.exists_rep C
    rfl

private theorem spechtClassFunction_pairing (μ ν : n.Partition) :
    ClassFunction.characterPairing
      (ClassFunction.ofCharacter (spechtModuleℂ μ).ρ)
      (ClassFunction.ofCharacter (spechtModuleℂ ν).ρ) =
        if μ = ν then (1 : ℂ) else 0 := by
  classical
  rw [ClassFunction.characterPairing_apply]
  simp only [ClassFunction.ofCharacter_apply, Representation.character]
  rw [sum_spechtTrace_mul_spechtTrace_inv, Nat.card_perm, Nat.card_fin]
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  split_ifs <;> simp [hf]

private theorem linearIndependent_spechtClassFunction (n : ℕ) :
    LinearIndependent ℂ (fun μ : n.Partition =>
      ClassFunction.ofCharacter (spechtModuleℂ μ).ρ) := by
  refine LinearMap.BilinForm.linearIndependent_of_iIsOrtho
    (B := ClassFunction.characterPairing)
    (LinearMap.BilinForm.iIsOrtho_def.mpr fun μ ν h => ?_) (fun μ => ?_)
  · rw [spechtClassFunction_pairing, if_neg h]
  · rw [spechtClassFunction_pairing, if_pos rfl]
    exact one_ne_zero

/-- The basis consists of the actual traces of the preserved same-shape complex modules. -/
noncomputable def spechtCharacterBasis (n : ℕ) :
    Module.Basis n.Partition ℂ (ClassFunction ℂ (Perm (Fin n))) :=
  basisOfLinearIndependentOfCardEqFinrank'
    (fun μ => ClassFunction.ofCharacter (spechtModuleℂ μ).ρ)
    (linearIndependent_spechtClassFunction n) (by
      rw [(classFunctionEquivConjClasses n).finrank_eq, Module.finrank_fintype_fun_eq_card]
      exact Fintype.card_congr (partitionEquivConjClasses n))

private theorem spechtCharacterBasis_apply (μ : n.Partition) :
    spechtCharacterBasis n μ = ClassFunction.ofCharacter (spechtModuleℂ μ).ρ := by
  exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _) μ

private theorem spechtCharacterBasis_repr
    (f : ClassFunction ℂ (Perm (Fin n))) (μ : n.Partition) :
    (spechtCharacterBasis n).repr f μ =
      ClassFunction.characterPairing (ClassFunction.ofCharacter (spechtModuleℂ μ).ρ) f := by
  classical
  conv_rhs => rw [← (spechtCharacterBasis n).sum_repr f]
  rw [map_sum, Finset.sum_eq_single μ]
  · rw [map_smul, spechtCharacterBasis_apply, spechtClassFunction_pairing,
      if_pos rfl, smul_eq_mul, mul_one]
  · intro ν _ hν
    rw [map_smul, spechtCharacterBasis_apply, spechtClassFunction_pairing,
      if_neg hν.symm, smul_zero]
  · intro hμ
    exact absurd (Finset.mem_univ μ) hμ

/-- Every complex class function has its actual Specht trace expansion, in every degree. -/
theorem eq_sum_spechtTrace (f : ClassFunction ℂ (Perm (Fin n))) (π : Perm (Fin n)) :
    f.1 π = ∑ μ : n.Partition,
      ClassFunction.characterPairing (ClassFunction.ofCharacter (spechtModuleℂ μ).ρ) f *
        LinearMap.trace ℂ _ ((spechtModuleℂ μ).ρ π) := by
  have h := congrArg (fun g : ClassFunction ℂ (Perm (Fin n)) => g.1 π)
    ((spechtCharacterBasis n).sum_repr f)
  simpa only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply,
    smul_eq_mul, spechtCharacterBasis_repr, spechtCharacterBasis_apply,
    ClassFunction.ofCharacter_apply, Representation.character] using h.symm

private def youngClassFunction (ν : n.Partition) : ClassFunction ℂ (Perm (Fin n)) :=
  ClassFunction.ofCharacter (permutationModuleℂ ν).ρ

private theorem youngClassFunction_coordinate (μ ν : n.Partition) :
    ClassFunction.characterPairing (ClassFunction.ofCharacter (spechtModuleℂ μ).ρ)
      (youngClassFunction ν) =
        (Module.finrank ℂ (spechtModuleℂ μ ⟶ permutationModuleℂ ν) : ℂ) := by
  letI : Invertible (Nat.card (Perm (Fin n)) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  rw [ClassFunction.characterPairing_symm]
  exact ClassFunction.characterPairing_ofFDRep_eq_finrank
    (permutationModuleℂ ν) (spechtModuleℂ μ)

/-- Young permutation characters expand with the dimensions of actual Specht-to-Young Hom spaces. -/
theorem char_permutationModuleℂ_eq_sum_multiplicity_mul_spechtTrace
    (ν : n.Partition) (π : Perm (Fin n)) :
    (permutationModuleℂ ν).character π = ∑ μ : n.Partition,
      (Module.finrank ℂ (spechtModuleℂ μ ⟶ permutationModuleℂ ν) : ℂ) *
        LinearMap.trace ℂ _ ((spechtModuleℂ μ).ρ π) := by
  simpa only [youngClassFunction, ClassFunction.ofCharacter_apply,
    youngClassFunction_coordinate] using eq_sum_spechtTrace (youngClassFunction ν) π

/-- The permutation-character Gram matrix is n! times the Gram matrix of actual multiplicities. -/
theorem sum_char_permutationModuleℂ_mul_char_permutationModuleℂ (ν ξ : n.Partition) :
    ∑ π : Perm (Fin n), (permutationModuleℂ ν).character π *
      (permutationModuleℂ ξ).character π =
    (n.factorial : ℂ) * ∑ μ : n.Partition,
      ((Module.finrank ℂ (spechtModuleℂ μ ⟶ permutationModuleℂ ν) : ℂ) *
        (Module.finrank ℂ (spechtModuleℂ μ ⟶ permutationModuleℂ ξ) : ℂ)) := by
  classical
  calc
    _ = ∑ μ : n.Partition,
        (Module.finrank ℂ (spechtModuleℂ μ ⟶ permutationModuleℂ ν) : ℂ) *
          ∑ π : Perm (Fin n), LinearMap.trace ℂ _ ((spechtModuleℂ μ).ρ π) *
            (permutationModuleℂ ξ).character π := by
      simp_rw [char_permutationModuleℂ_eq_sum_multiplicity_mul_spechtTrace ν,
        Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro μ _
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun π _ => mul_assoc _ _ _
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro μ _
      have h := sum_spechtTrace_mul_card_fixedPoints μ ξ
      have hs : ∑ π : Perm (Fin n), LinearMap.trace ℂ _ ((spechtModuleℂ μ).ρ π) *
          (permutationModuleℂ ξ).character π =
          (n.factorial : ℂ) *
            (Module.finrank ℂ (spechtModuleℂ μ ⟶ permutationModuleℂ ξ) : ℂ) := by
        simpa only [char_permutationModuleℂ] using h
      rw [hs]
      ring

end TauCeti
end
end D5.S3.Combinatorics.Partitions.SpechtPolytabloid
