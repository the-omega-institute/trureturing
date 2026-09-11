/- GID: D5/S3/ConceptDynamics/Spacetime/ContextExtensionComposition
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Spacetime/ContextExtensionComposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sequential context embeddings compose, and their new-region charges add. -/

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
  current_map_subset := by
    intro z hz
    obtain ⟨e, he, rfl⟩ := Finset.mem_map.mp hz
    apply k.current_map_subset
    exact Finset.mem_map.mpr ⟨mapEvent j e,
      j.current_map_subset (Finset.mem_map.mpr ⟨e, he, rfl⟩), rfl⟩

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
  ext e
  simp only [newRegion, Finset.mem_sdiff, Finset.mem_union, mapEvent_comp]
  constructor
  · intro he
    by_cases hk : e ∈ D.current.map (mapEvent k)
    · right
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hk
      have hy_not : y ∉ C.current.map (mapEvent j) := by
        intro hxy
        obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hxy
        exact he.2 (Finset.mem_map.mpr ⟨x, hx, rfl⟩)
      exact Finset.mem_map.mpr ⟨y, Finset.mem_sdiff.mpr ⟨hy, hy_not⟩, rfl⟩
    · left
      exact ⟨he.1, hk⟩
  · intro he
    rcases he with he | he
    · exact ⟨he.1, by
        intro hcomp
        obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hcomp
        apply he.2
        exact Finset.mem_map.mpr ⟨mapEvent j x,
          j.current_map_subset (Finset.mem_map.mpr ⟨x, hx, rfl⟩), rfl⟩⟩
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp he
      have hy' := Finset.mem_sdiff.mp hy
      refine ⟨k.current_map_subset (Finset.mem_map.mpr ⟨y, hy'.1, rfl⟩), ?_⟩
      intro hcomp
      obtain ⟨x, hx, hxe⟩ := Finset.mem_map.mp hcomp
      have hxy : mapEvent k (mapEvent j x) = mapEvent k y := by
        simpa using hxe
      have : mapEvent j x = y := (mapEvent k).injective hxy
      exact hy'.2 (Finset.mem_map.mpr ⟨x, hx, this⟩)

theorem newRegion_comp_disjoint {d : Nat} {C D E : Context d}
    (j : ContextEmbedding C D) (k : ContextEmbedding D E) :
    Disjoint (newRegion k) ((newRegion j).map (mapEvent k)) := by
  refine Finset.disjoint_left.2 ?_
  intro e heK heJ
  obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp heJ
  exact (Finset.mem_sdiff.mp heK).2
    (Finset.mem_map.mpr ⟨y, (Finset.mem_sdiff.mp hy).1, rfl⟩)

theorem newRegion_charge_comp {d : Nat} {C D E : Context d}
    (j : ContextEmbedding C D) (k : ContextEmbedding D E) :
    charge E (newRegion (ContextEmbedding.comp j k)) =
      charge E (newRegion k) + charge E ((newRegion j).map (mapEvent k)) := by
  rw [newRegion_comp j k]
  change (∑ e ∈ (newRegion k ∪ (newRegion j).map (mapEvent k)), contribution E e) =
    (∑ e ∈ newRegion k, contribution E e) +
      (∑ e ∈ (newRegion j).map (mapEvent k), contribution E e)
  rw [Finset.sum_union (newRegion_comp_disjoint j k)]

theorem newRegion_charge_map {d : Nat} {C D : Context d}
    (j : ContextEmbedding C D) (s : Finset C.Event) :
    charge D (s.map (mapEvent j)) = charge C s := by
  rw [charge, charge, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro e he
  simp [contribution, j.archiveEmbedding.attributes_eq]

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
        charge E (newRegion k) + charge E ((newRegion j).map (mapEvent k)) ∧
      q ⟨E, mapSelection k (mapSelection j a)⟩ = q ⟨C, a⟩ := by
  exact ⟨mapSelection_comp j k a, newRegion_comp j k,
    newRegion_comp_disjoint j k, newRegion_charge_comp j k,
    q_map_comp j k a⟩

#print axioms context_extension_composition_spec

end
end D5.S3.ConceptDynamics.Spacetime.ContextExtensionComposition
