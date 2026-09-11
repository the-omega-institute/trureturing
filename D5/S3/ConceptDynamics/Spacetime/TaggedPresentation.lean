/- GID: D5/S3/ConceptDynamics/Spacetime/TaggedPresentation
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Spacetime/TaggedPresentation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite typed presentations realize exact HF archives by equivalence. -/

import D5.S3.ConceptDynamics.Spacetime.ComplementCharge
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Finset.Sum
import Mathlib.Algebra.BigOperators.Ring.Finset

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.Spacetime.TaggedPresentation

open D5.S0.History.Spacetime.HFEncoding
open D5.S0.History.Spacetime.ArchiveCarrier
open ComplementCharge
noncomputable section

variable {α : Type} [Fintype α] {d : Nat}

/-- The actual finite set of HF names, without a second archive carrier. -/
def events (code : α ↪ HF) : Finset HF := Finset.univ.map code

/-- Every typed event corresponds to exactly one member of the literal HF archive. -/
def eventEquiv (code : α ↪ HF) : α ≃ ↥(events code) :=
  Equiv.ofBijective (fun x => ⟨code x, Finset.mem_map.mpr ⟨x, Finset.mem_univ _, rfl⟩⟩)
    ⟨fun _ _ h => code.injective (congrArg Subtype.val h), by
      rintro ⟨x, hx⟩
      obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hx
      exact ⟨a, rfl⟩⟩

@[simp] theorem eventEquiv_val (code : α ↪ HF) (x : α) :
    (eventEquiv code x).val = code x := rfl

@[simp] theorem events_card (code : α ↪ HF) :
    (events code).card = Fintype.card α := by simp [events]

/-- Transport attributes and a proved strict causal relation to the exact HF set. -/
def archiveOf (code : α ↪ HF) (attr : α → Attributes d) (rel : α → α → Prop)
    (hi : ∀ x, ¬ rel x x) (ht : ∀ x y z, rel x y → rel y z → rel x z)
    (hc : ∀ x y, rel x y → (attr x).time < (attr y).time) : Archive d where
  events := events code
  attributes x := attr ((eventEquiv code).symm x)
  causal x y := rel ((eventEquiv code).symm x) ((eventEquiv code).symm y)
  irrefl _ := hi _
  trans _ _ _ := ht _ _ _
  time_lt _ _ := hc _ _

variable (code : α ↪ HF) (attr : α → Attributes d) (rel : α → α → Prop)
  (hi : ∀ x, ¬ rel x x) (ht : ∀ x y z, rel x y → rel y z → rel x z)
  (hc : ∀ x y, rel x y → (attr x).time < (attr y).time)

@[simp] theorem attributes_eventEquiv (x : α) :
    (archiveOf code attr rel hi ht hc).attributes (eventEquiv code x) = attr x := by
  simp [archiveOf]

@[simp] theorem causal_eventEquiv (x y : α) :
    (archiveOf code attr rel hi ht hc).causal (eventEquiv code x) (eventEquiv code y) ↔
      rel x y := by simp [archiveOf]

/-- Current and selected sets are transported by the same event equivalence. -/
def contextOf (current : Finset α) : Context d where
  archive := archiveOf code attr rel hi ht hc
  current := current.map (eventEquiv code).toEmbedding

def selectionOf (current selected : Finset α) (hs : selected ⊆ current) :
    Selection (contextOf code attr rel hi ht hc current) :=
  ⟨selected.map (eventEquiv code).toEmbedding, Finset.map_subset_map.mpr hs⟩

theorem charge_map (current selected : Finset α) :
    charge (contextOf code attr rel hi ht hc current)
      (selected.map (eventEquiv code).toEmbedding) =
      ∑ x ∈ selected, (if (attr x).positive then (1 : Int) else -1) := by
  simp [charge, contribution, contextOf, archiveOf]

/-- Forgetting the subtype after reindexing gives exactly the prescribed HF image. -/
theorem names_map (s : Finset α) :
    (s.map (eventEquiv code).toEmbedding).map (Function.Embedding.subtype _) = s.map code := by
  rw [Finset.map_map]
  rfl

end
end D5.S3.ConceptDynamics.Spacetime.TaggedPresentation
