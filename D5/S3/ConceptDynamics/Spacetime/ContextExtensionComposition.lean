/- GID: D5/S3/ConceptDynamics/Spacetime/ContextExtensionComposition
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Spacetime/ContextExtensionComposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sequential context embeddings compose, and their new-region charges add. -/

/-
All public theorems are bind-only; no escape witness is claimed.
Module admission_basis: rule-11-upstream-wrapper. The concrete repository API
requirement is context_extension_composition_spec: compose Definition 11 embeddings,
transport selections and q, and add successive Proposition 8 charge defects.
This is a companion API requirement, not an independent source coverage claim.
Exact reuse: ArchiveEmbedding.comp, Finset.map_map, Finset.map_sdiff,
Finset.sdiff_union_sdiff_cancel, Finset.sum_union, and the complement transport API.
Companion consumer -> prerequisite edges:
mapSelection_comp -> mapEvent_comp (definitionally);
newRegion_charge_comp -> newRegion_comp, newRegion_comp_disjoint;
q_map_comp -> mapSelection_comp, ContextExtensionComplement.q_map;
context_extension_composition_spec -> mapSelection_comp, newRegion_comp,
  newRegion_comp_disjoint, newRegion_charge_comp, q_map_comp,
  ContextExtensionComplement.map_charge.
All statements concern arbitrary finite contexts; utility: none.
-/

import D5.S3.ConceptDynamics.Spacetime.ContextExtensionComplement
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.Spacetime.ContextExtensionComposition

open D5.S0.History.Spacetime.ArchiveCarrier
open D5.S3.ConceptDynamics.Spacetime.ComplementCharge
open D5.S3.ConceptDynamics.Spacetime.ContextExtensionComplement
noncomputable section
open scoped Classical
open scoped BigOperators

/-- Composition of context embeddings preserves the current-region condition. -/
def ContextEmbedding.comp {d : Nat} {C D E : Context d}
    (j : ContextEmbedding C D) (k : ContextEmbedding D E) : ContextEmbedding C E where
  archiveEmbedding := ArchiveEmbedding.comp j.archiveEmbedding k.archiveEmbedding
  current_iff e := (k.current_iff (mapEvent j e)).trans (j.current_iff e)

@[simp] theorem mapEvent_comp {d : Nat} {C D E : Context d}
    (j : ContextEmbedding C D) (k : ContextEmbedding D E) (e : C.Event) :
    mapEvent (ContextEmbedding.comp j k) e = mapEvent k (mapEvent j e) := rfl

theorem mapSelection_comp {d : Nat} {C D E : Context d}
    (j : ContextEmbedding C D) (k : ContextEmbedding D E) (a : Selection C) :
    mapSelection (ContextEmbedding.comp j k) a = mapSelection k (mapSelection j a) := by
  apply Subtype.ext
  change a.val.map (mapEvent (ContextEmbedding.comp j k)) =
    (a.val.map (mapEvent j)).map (mapEvent k)
  rw [Finset.map_map]
  rfl

theorem newRegion_comp {d : Nat} {C D E : Context d}
    (j : ContextEmbedding C D) (k : ContextEmbedding D E) :
    newRegion (ContextEmbedding.comp j k) =
      newRegion k ∪ (newRegion j).map (mapEvent k) := by
  simpa only [newRegion, Finset.map_sdiff, Finset.map_map, mapEvent,
    ContextEmbedding.comp, ArchiveEmbedding.comp] using
    (Finset.sdiff_union_sdiff_cancel k.current_map_subset
      (Finset.map_subset_map.mpr j.current_map_subset)).symm

theorem newRegion_comp_disjoint {d : Nat} {C D E : Context d}
    (j : ContextEmbedding C D) (k : ContextEmbedding D E) :
    Disjoint (newRegion k) ((newRegion j).map (mapEvent k)) := by
  exact Finset.disjoint_of_subset_right
    (Finset.map_subset_map.mpr Finset.sdiff_subset) Finset.sdiff_disjoint

theorem newRegion_charge_comp {d : Nat} {C D E : Context d}
    (j : ContextEmbedding C D) (k : ContextEmbedding D E) :
    charge E (newRegion (ContextEmbedding.comp j k)) =
      charge E (newRegion k) + charge E ((newRegion j).map (mapEvent k)) := by
  rw [newRegion_comp j k]
  change (∑ e ∈ (newRegion k ∪ (newRegion j).map (mapEvent k)), contribution E e) =
    (∑ e ∈ newRegion k, contribution E e) +
      (∑ e ∈ (newRegion j).map (mapEvent k), contribution E e)
  rw [Finset.sum_union (newRegion_comp_disjoint j k)]

theorem q_map_comp {d : Nat} {C D E : Context d}
    (j : ContextEmbedding C D) (k : ContextEmbedding D E) (a : Selection C) :
    q ⟨E, mapSelection k (mapSelection j a)⟩ = q ⟨C, a⟩ := by
  rw [← mapSelection_comp j k a]
  exact q_map (ContextEmbedding.comp j k) a

theorem context_extension_composition_spec {d : Nat} {C D E : Context d}
    (j : ContextEmbedding C D) (k : ContextEmbedding D E) (a : Selection C) :
    mapSelection (ContextEmbedding.comp j k) a = mapSelection k (mapSelection j a) ∧
      newRegion (ContextEmbedding.comp j k) =
        newRegion k ∪ (newRegion j).map (mapEvent k) ∧
      Disjoint (newRegion k) ((newRegion j).map (mapEvent k)) ∧
      charge E (newRegion (ContextEmbedding.comp j k)) =
        charge E (newRegion k) + charge D (newRegion j) ∧
      q ⟨E, mapSelection k (mapSelection j a)⟩ = q ⟨C, a⟩ := by
  refine ⟨mapSelection_comp j k a, newRegion_comp j k,
    newRegion_comp_disjoint j k, ?_, q_map_comp j k a⟩
  simpa only [map_charge] using newRegion_charge_comp j k

#print axioms context_extension_composition_spec

end
end D5.S3.ConceptDynamics.Spacetime.ContextExtensionComposition
