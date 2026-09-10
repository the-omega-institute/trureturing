/- GID: D5/S3/ConceptDynamics/ZfcSupport/AdjunctiveSet
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ZfcSupport/AdjunctiveSet
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Set.Finite.Basic]
   utility: none
   digest: Vorspiel.AdjunctiveSet for first-order set definition elimination. -/
module

public import Mathlib.Data.Set.Finite.Basic

/- Source: FormalizedFormalLogic/Foundation@30a16ffa93d79d73ab4d02427fa00f50e039bf29
   Foundation/Vorspiel/AdjunctiveSet.lean, original lines 1-119.
   Modifications: source-command excerpt; canonical header, reduced imports, and capacity scopes.
   Retained proofs and required notices preserve attribution. Apache-2.0 license:
   Library/ConceptDynamics/foundation2026firstorder.md.
   Retirement: direct Mathlib reference when the repository pin supplies a
   proved-equivalent interface and its faithful bridge elaborates. -/

@[expose] public section

class Adjoin (β : outParam Type*) (α : Type*) where
  adjoin : β → α → α
export Adjoin (adjoin)

instance (α : Type*) : Adjoin α (Set α) := ⟨insert⟩

instance (α : Type*) : Adjoin α (List α) := ⟨List.cons⟩

instance (α : Type*) [DecidableEq α] : Adjoin α (Finset α) := ⟨insert⟩

class AdjunctiveSet (β : outParam Type*) (α : Type*) extends Membership β α, HasSubset α, EmptyCollection α, Adjoin β α where
  subset_iff {a b : α} : a ⊆ b ↔ ∀ x ∈ a, x ∈ b
  not_mem_empty (x : β) : ¬x ∈ (∅ : α)
  mem_cons_iff {x z : β} {a : α} : x ∈ adjoin z a ↔ x = z ∨ x ∈ a

attribute [simp] AdjunctiveSet.not_mem_empty AdjunctiveSet.mem_cons_iff

instance Set.adjunctiveSet : AdjunctiveSet α (Set α) where
  Subset := (· ⊆ ·)
  subset_iff := iff_of_eq Set.subset_def
  not_mem_empty := by simp
  mem_cons_iff := by simp [Adjoin.adjoin]

instance List.adjunctiveSet : AdjunctiveSet α (List α) where
  subset_iff := List.subset_def
  not_mem_empty := by simp
  mem_cons_iff := by simp [Adjoin.adjoin]

instance Finset.adjunctiveSet [DecidableEq α] : AdjunctiveSet α (Finset α) where
  Subset := (· ⊆ ·)
  subset_iff := Finset.subset_iff
  not_mem_empty := by simp
  mem_cons_iff := by simp [Adjoin.adjoin]

namespace AdjunctiveSet

variable {β α : Type*} [AdjunctiveSet β α]

def set : α → Set β := fun a ↦ {x | x ∈ a}

@[simp] lemma mem_set_iff {x : β} {a : α} : x ∈ (set a : Set β) ↔ x ∈ a := by simp [set]

lemma subset_iff_set_subset_set {a b : α} : a ⊆ b ↔ set a ⊆ set b := by simp [subset_iff, set]

@[simp, refl] lemma subset_refl (a : α) : a ⊆ a := subset_iff_set_subset_set.mpr (Set.Subset.refl _)

@[simp] lemma subset_cons (a : α) (x : β) : a ⊆ adjoin x a := by simp [subset_iff, mem_cons_iff]; tauto

@[simp] lemma set_cons (z : β) (a : α) : set (adjoin z a) = insert z (set a) := by ext; simp [set]

end AdjunctiveSet

namespace Set

variable {α : Type*}

end Set

end
