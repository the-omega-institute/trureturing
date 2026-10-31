/- GID: D5/S3/Combinatorics/Partitions/SpechtOrdinaryTrace
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/SpechtOrdinaryTrace
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Integral ordinary traces of the same literal complex Specht modules on full permutation partitions. -/

/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license. Authors: The Tau Ceti contributors.
Selected A17.2PORT from TauCeti 5a01f5fe3621126cccf9ba22e700493cbc7b7156.
Changes: selected declarations, repository namespaces and existing D5 class-function
supplier; rational integrality uses OUR pinned Mathlib FDRep.isIntegral_character,
rather than porting a second finite-order trace proof. Trivial def/eq wrappers are
inlined. The final ordinary-trace certification is a local composition.
License, immutable locators, consumers and retirement rule:
Library/FiniteGroups/tauceti2026spechtpolytabloids.md.

SOURCE ONLY: no native elaboration, axiom closure, proof-term liveness, accepted
admission, validated Reg, firstfreeze, emission, deposit, PR or CI is claimed.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/24542.
Every selected helper has a source consumer below. These are necessary suppliers,
not standalone new-content qualification or a proof of the original HSW theorem.
The endpoint certifies simplicity AND the integral trace of the actual same-shape
complex module, with existence and independence for FULL partitions (including 1s).
It does not identify that trace with HSW.frobChar; arbitrary-degree Frobenius/Schur,
height vanishing, bialternant extraction, literal padded rows and both weighted sums
remain unfinished. No coefficient is defined to be an ordinary character.
utility: none: general unbounded representation and conjugacy constructions.
-/
import D5.S3.Combinatorics.Partitions.SpechtComplexIrreducibility
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.Algebra.Group.ConjFinite
import Mathlib.GroupTheory.Perm.Cycle.PossibleTypes
import Mathlib.RepresentationTheory.Character

namespace D5.S3.Combinatorics.Partitions.SpechtPolytabloid

noncomputable section
open scoped BigOperators

namespace TauCeti
open Equiv

theorem parts_equivCast {m l : ℕ} (h : m = l) (p : m.Partition) :
    (Equiv.cast (congrArg Nat.Partition h) p).parts = p.parts := by
  subst h; rfl

theorem exists_perm_partition_eq {α : Type*} [Fintype α] [DecidableEq α]
    (p : (Fintype.card α).Partition) :
    ∃ σ : Equiv.Perm α, σ.partition = p := by
  let largeParts := p.parts.filter fun a => 2 ≤ a
  let unitParts := p.parts.filter fun a => ¬2 ≤ a
  have hsplit : largeParts + unitParts = p.parts := by
    exact Multiset.filter_add_not (p := fun a : ℕ => 2 ≤ a) p.parts
  have hunit : unitParts = Multiset.replicate unitParts.card 1 := by
    apply Multiset.eq_replicate_card.mpr
    intro a ha
    have ha' := Multiset.mem_filter.mp ha
    have hpos := p.parts_pos ha'.1
    omega
  have hunitSum : unitParts.sum = unitParts.card := by
    calc
      unitParts.sum = (Multiset.replicate unitParts.card 1).sum :=
        congrArg Multiset.sum hunit
      _ = unitParts.card := by
        rw [Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id, mul_one]
  have hsum : largeParts.sum + unitParts.card = Fintype.card α := by
    rw [← p.parts_sum, ← hsplit, Multiset.sum_add, hunitSum]
  have hlarge : largeParts.sum ≤ Fintype.card α := by omega
  have hlarge_mem : ∀ a ∈ largeParts, 2 ≤ a := by
    intro a ha
    exact (Multiset.mem_filter.mp ha).2
  obtain ⟨σ, hσ⟩ :=
    (Equiv.Perm.exists_with_cycleType_iff α).mpr ⟨hlarge, hlarge_mem⟩
  refine ⟨σ, ?_⟩
  apply Nat.Partition.ext
  have hsupport : σ.support.card = largeParts.sum := by
    rw [← Equiv.Perm.sum_cycleType, hσ]
  have hremaining : Fintype.card α - largeParts.sum = unitParts.card := by
    omega
  rw [Equiv.Perm.parts_partition, hσ, hsupport, hremaining, ← hunit, hsplit]


def permConjClassPartition {α : Type*} [Fintype α] [DecidableEq α] :
    ConjClasses (Equiv.Perm α) → (Fintype.card α).Partition :=
  Quotient.lift Equiv.Perm.partition fun _ _ h =>
    Equiv.Perm.partition_eq_of_isConj.mp h


@[simp]
theorem permConjClassPartition_mk {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) :
    permConjClassPartition (ConjClasses.mk σ) = σ.partition := by
  simp [permConjClassPartition, ConjClasses.mk]


theorem permConjClassPartition_injective {α : Type*} [Fintype α] [DecidableEq α] :
    Function.Injective (permConjClassPartition (α := α)) := by
  intro C D h
  obtain ⟨σ, rfl⟩ := ConjClasses.exists_rep C
  obtain ⟨τ, rfl⟩ := ConjClasses.exists_rep D
  rw [ConjClasses.mk_eq_mk_iff_isConj]
  apply Equiv.Perm.partition_eq_of_isConj.mpr
  simpa only [permConjClassPartition_mk] using h


theorem permConjClassPartition_surjective {α : Type*} [Fintype α] [DecidableEq α] :
    Function.Surjective (permConjClassPartition (α := α)) := by
  intro p
  obtain ⟨σ, hσ⟩ := exists_perm_partition_eq p
  exact ⟨ConjClasses.mk σ, by simpa using hσ⟩


noncomputable def partitionEquivPermConjClasses (α : Type*) [Fintype α] [DecidableEq α] :
    (Fintype.card α).Partition ≃ ConjClasses (Equiv.Perm α) :=
  (Equiv.ofBijective (permConjClassPartition (α := α))
    ⟨permConjClassPartition_injective, permConjClassPartition_surjective⟩).symm


noncomputable def partitionEquivConjClasses (n : ℕ) :
    n.Partition ≃ ConjClasses (Equiv.Perm (Fin n)) :=
  (Equiv.cast (congrArg Nat.Partition (Fintype.card_fin n).symm)).trans
    (partitionEquivPermConjClasses (Fin n))


@[simp]
theorem partitionEquivPermConjClasses_symm_mk (α : Type*) [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) :
    (partitionEquivPermConjClasses α).symm (ConjClasses.mk σ) = σ.partition := by
  -- the inverse of `partitionEquivPermConjClasses` is `permConjClassPartition` by construction;
  -- `change` names it, the equivalence having no `symm_apply` lemma of its own.
  change permConjClassPartition (ConjClasses.mk σ) = σ.partition
  exact permConjClassPartition_mk σ


@[simp]
theorem partitionEquivConjClasses_symm_mk (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (partitionEquivConjClasses n).symm (ConjClasses.mk σ) =
      (Equiv.cast (congrArg Nat.Partition (Fintype.card_fin n).symm)).symm
        σ.partition := by
  simp [partitionEquivConjClasses]


theorem parts_partitionEquivConjClasses_symm_mk (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    ((partitionEquivConjClasses n).symm (ConjClasses.mk σ)).parts = σ.partition.parts := by
  rw [partitionEquivConjClasses_symm_mk]
  exact parts_equivCast (Fintype.card_fin n) _

end TauCeti

namespace FDRep
variable {G : Type*} [Group G] [Finite G]

-- Adapted to the exact general integrality supplier already present at OUR pin.
theorem exists_char_eq_intCast (V : _root_.FDRep ℚ G) (g : G) :
    ∃ m : ℤ, V.character g = (m : ℚ) := by
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.1
    (_root_.FDRep.isIntegral_character V g)
  exact ⟨m, by simpa using hm.symm⟩

noncomputable def intCharacter (V : _root_.FDRep ℚ G) (g : G) : ℤ :=
  (V.character g).num

@[simp]
theorem intCharacter_cast (V : _root_.FDRep ℚ G) (g : G) :
    (intCharacter V g : ℚ) = V.character g := by
  obtain ⟨m, hm⟩ := exists_char_eq_intCast V g
  rw [intCharacter, hm, Rat.num_intCast]

@[simp]
theorem intCharacter_conj (V : _root_.FDRep ℚ G) (g h : G) :
    intCharacter V (h * g * h⁻¹) = intCharacter V g := by
  apply Int.cast_injective (α := ℚ)
  rw [intCharacter_cast, intCharacter_cast, _root_.FDRep.char_conj]

noncomputable def intClassFunction (V : _root_.FDRep ℚ G) :
    D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.ClassFunction ℤ G :=
  ⟨intCharacter V,
    D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.ClassFunction.mem_iff.2
      (intCharacter_conj V)⟩

@[simp]
theorem intClassFunction_apply (V : _root_.FDRep ℚ G) (g : G) :
    (intClassFunction V).1 g = intCharacter V g := rfl
end FDRep

namespace Representation
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

@[simp]
theorem character_baseChange {G : Type*} [Monoid G]
    (ρ : _root_.Representation K G V) (g : G) :
    (baseChange L ρ).character g = algebraMap K L (ρ.character g) := by
  simp [_root_.Representation.character, baseChange_apply, LinearMap.trace_baseChange]
end Representation

namespace TauCeti
variable {n : ℕ}

noncomputable def spechtChar (μ : n.Partition) : Equiv.Perm (Fin n) → ℤ :=
  FDRep.intCharacter (spechtModule μ)

@[simp]
theorem spechtChar_cast (μ : n.Partition) (σ : Equiv.Perm (Fin n)) :
    (spechtChar μ σ : ℚ) = (spechtModule μ).character σ := by
  rw [spechtChar, FDRep.intCharacter_cast]

noncomputable def spechtCharConjClasses (μ : n.Partition) :
    ConjClasses (Equiv.Perm (Fin n)) → ℤ :=
  D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.ClassFunction.toConjClasses
    (FDRep.intClassFunction (spechtModule μ))

@[simp]
theorem spechtCharConjClasses_mk (μ : n.Partition) (σ : Equiv.Perm (Fin n)) :
    spechtCharConjClasses μ (ConjClasses.mk σ) = spechtChar μ σ := by
  rw [spechtCharConjClasses,
    D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.ClassFunction.toConjClasses_mk,
    FDRep.intClassFunction_apply, spechtChar]

noncomputable def spechtCharValue (μ ν : n.Partition) : ℤ :=
  spechtCharConjClasses μ (partitionEquivConjClasses n ν)

theorem spechtCharValue_eq_spechtChar (μ ν : n.Partition) {σ : Equiv.Perm (Fin n)}
    (hσ : ConjClasses.mk σ = partitionEquivConjClasses n ν) :
    spechtCharValue μ ν = spechtChar μ σ := by
  rw [spechtCharValue, ← hσ, spechtCharConjClasses_mk]

theorem character_spechtModuleℂ (μ : n.Partition) (σ : Equiv.Perm (Fin n)) :
    (spechtModuleℂ μ).character σ = algebraMap ℚ ℂ ((spechtModule μ).character σ) := by
  rw [spechtModuleℂ_def, _root_.FDRep.character, _root_.FDRep.of_ρ']
  exact Representation.character_baseChange _ σ

@[simp]
theorem character_spechtModuleℂ_intCast (μ : n.Partition) (σ : Equiv.Perm (Fin n)) :
    (spechtModuleℂ μ).character σ = (spechtChar μ σ : ℂ) := by
  rw [character_spechtModuleℂ, ← spechtChar_cast, eq_ratCast, Rat.cast_intCast]

/-- Certification of an ordinary character value of the independently constructed,
same-partition complex irreducible Specht representation. The representative exists,
and every permutation with the FULL prescribed partition (1-cycles included) has
this trace. This is a necessary semantic supplier, not the Frobenius comparison. -/
theorem spechtCharValue_ordinaryTrace (μ ν : n.Partition) :
    CategoryTheory.Simple (spechtModuleℂ μ) ∧
      ∃ σ : Equiv.Perm (Fin n), σ.partition.parts = ν.parts ∧
        ∀ τ : Equiv.Perm (Fin n), τ.partition.parts = ν.parts →
          LinearMap.trace ℂ _ ((spechtModuleℂ μ).ρ τ) = (spechtCharValue μ ν : ℂ) := by
  refine ⟨instSimpleSpechtModuleℂ μ, ?_⟩
  obtain ⟨σ, hσ⟩ := (partitionEquivConjClasses n ν).exists_rep
  have hp := parts_partitionEquivConjClasses_symm_mk n σ
  rw [hσ, Equiv.symm_apply_apply] at hp
  refine ⟨σ, hp.symm, fun τ hτ => ?_⟩
  have hν : (partitionEquivConjClasses n).symm (ConjClasses.mk τ) = ν :=
    Nat.Partition.ext ((parts_partitionEquivConjClasses_symm_mk n τ).trans hτ)
  have hc : ConjClasses.mk τ = partitionEquivConjClasses n ν := by
    rw [← hν, Equiv.apply_symm_apply]
  change (spechtModuleℂ μ).character τ = (spechtCharValue μ ν : ℂ)
  rw [character_spechtModuleℂ_intCast, spechtCharValue_eq_spechtChar μ ν hc]

end TauCeti
end
end D5.S3.Combinatorics.Partitions.SpechtPolytabloid
