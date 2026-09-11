/- GID: D5/S3/ConceptDynamics/Spacetime/ContextExtensionComplement
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Spacetime/ContextExtensionComplement
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A finite context embedding decomposes transported complements into the old complement and the new current region; atom sha256:20ec8078362e29e89f35f4c3a5d47fdb2453b0b2f3448564613f86b9524f9f92 -/

/-
proof_shape: content; admission_basis: escape-witness.
escape_witness: complement_decomposition is proved by a finite membership split
on whether a target event lies in the transported old current region and, when it
does, whether its unique preimage lies in the selected old set. The resulting
disjoint finite-set identity is used on the live path of the complete conjunction,
which also transports the signed sum and records the exactness, readout, and
balance consequences.
-/

import D5.S3.ConceptDynamics.Spacetime.ComplementCharge
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.Spacetime.ContextExtensionComplement

open D5.S0.History.Spacetime.ArchiveCarrier
open ComplementCharge
noncomputable section
open scoped Classical
open scoped BigOperators

/- A context embedding extends an archive embedding with the only current-region
   condition needed for transport: every old current event lands in the new
   current region. -/
structure ContextEmbedding {d : Nat} (C D : Context d) where
  archiveEmbedding : ArchiveEmbedding C.archive D.archive
  current_map_subset :
    C.current.map archiveEmbedding.eventMap ⊆ D.current

abbrev mapEvent {d : Nat} {C D : Context d}
    (j : ContextEmbedding C D) : C.Event ↪ D.Event :=
  j.archiveEmbedding.eventMap

def mapSelection {d : Nat} {C D : Context d}
    (j : ContextEmbedding C D) (a : Selection C) : Selection D :=
  ⟨a.val.map (mapEvent j), by
    exact (Finset.map_subset_map.mpr a.property).trans j.current_map_subset⟩

def newRegion {d : Nat} {C D : Context d}
    (j : ContextEmbedding C D) : Finset D.Event :=
  D.current \ C.current.map (mapEvent j)

theorem map_readout {d : Nat} {C D : Context d}
    (j : ContextEmbedding C D) (a : Selection C) :
    readout (mapSelection j a) = readout a := by
  change charge D (a.val.map (mapEvent j)) = charge C a.val
  rw [charge, charge, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro e he
  simp [contribution, j.archiveEmbedding.attributes_eq]

theorem q_map {d : Nat} {C D : Context d}
    (j : ContextEmbedding C D) (a : Selection C) :
    q ⟨D, mapSelection j a⟩ = q ⟨C, a⟩ := by
  exact map_readout j a

theorem complement_map_disjoint_newRegion {d : Nat} {C D : Context d}
    (j : ContextEmbedding C D) (a : Selection C) :
    Disjoint ((C.current \ a.val).map (mapEvent j)) (newRegion j) := by
  refine Finset.disjoint_left.2 ?_
  intro e heOld heNew
  obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp heOld
  exact (Finset.mem_sdiff.mp heNew).2
    (Finset.mem_map.mpr ⟨x, (Finset.mem_sdiff.mp hx).1, rfl⟩)

theorem complement_decomposition {d : Nat} {C D : Context d}
    (j : ContextEmbedding C D) (a : Selection C) :
    D.current \ a.val.map (mapEvent j) =
      (C.current \ a.val).map (mapEvent j) ∪ newRegion j := by
  ext e
  simp only [Finset.mem_sdiff, Finset.mem_union, newRegion]
  constructor
  · intro he
    by_cases hmap : e ∈ C.current.map (mapEvent j)
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hmap
      by_cases hsel : x ∈ a.val
      · exact (he.2 (Finset.mem_map.mpr ⟨x, hsel, rfl⟩)).elim
      · exact Or.inl (Finset.mem_map.mpr
          ⟨x, Finset.mem_sdiff.mpr ⟨hx, hsel⟩, rfl⟩)
    · exact Or.inr ⟨he.1, hmap⟩
  · intro he
    rcases he with he | he
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp he
      exact ⟨j.current_map_subset (Finset.mem_map.mpr ⟨x, (Finset.mem_sdiff.mp hx).1, rfl⟩), by
        intro hsel
        obtain ⟨y, hy, hxy⟩ := Finset.mem_map.mp hsel
        exact (Finset.mem_sdiff.mp hx).2
          ((mapEvent j).injective hxy ▸ hy)⟩
    · exact ⟨he.1, fun hsel => he.2
        ((Finset.map_subset_map.mpr a.property) hsel)⟩

theorem complement_charge_difference {d : Nat} {C D : Context d}
    (j : ContextEmbedding C D) (a : Selection C) :
    readout (complement (mapSelection j a)) - readout (complement a) =
      charge D (newRegion j) := by
  change (∑ e ∈ (D.current \ a.val.map (mapEvent j)), contribution D e) -
      (∑ e ∈ (C.current \ a.val), contribution C e) =
      ∑ e ∈ newRegion j, contribution D e
  rw [complement_decomposition j a]
  rw [Finset.sum_union (complement_map_disjoint_newRegion j a)]
  rw [Finset.sum_map]
  simp only [contribution, j.archiveEmbedding.attributes_eq]
  ring

theorem q_complement_charge_difference {d : Nat} {C D : Context d}
    (j : ContextEmbedding C D) (a : Selection C) :
    q ⟨D, complement (mapSelection j a)⟩ - q ⟨C, complement a⟩ =
      charge D (newRegion j) := by
  exact complement_charge_difference j a

theorem complement_decomposition_exact_iff {d : Nat} {C D : Context d}
    (j : ContextEmbedding C D) (a : Selection C) :
    D.current \ a.val.map (mapEvent j) =
      (C.current \ a.val).map (mapEvent j) ↔
      newRegion j = ∅ := by
  constructor
  · intro h
    change D.current \ C.current.map (mapEvent j) = ∅
    apply Finset.sdiff_eq_empty_iff_subset.mpr
    intro e he
    by_cases hsel : e ∈ a.val.map (mapEvent j)
    · exact (Finset.map_subset_map.mpr a.property) hsel
    have hmem : e ∈ D.current \ a.val.map (mapEvent j) :=
      Finset.mem_sdiff.mpr ⟨he, hsel⟩
    rw [h] at hmem
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hmem
    exact Finset.mem_map.mpr ⟨x, (Finset.mem_sdiff.mp hx).1, rfl⟩
  · intro h
    rw [complement_decomposition j a, h]
    simp

theorem complement_readout_exchange_iff {d : Nat} {C D : Context d}
    (j : ContextEmbedding C D) (a : Selection C) :
    readout (complement (mapSelection j a)) = readout (complement a) ↔
      charge D (newRegion j) = 0 := by
  rw [← sub_eq_zero, complement_charge_difference]

theorem q_complement_readout_exchange_iff {d : Nat} {C D : Context d}
    (j : ContextEmbedding C D) (a : Selection C) :
    q ⟨D, complement (mapSelection j a)⟩ = q ⟨C, complement a⟩ ↔
      charge D (newRegion j) = 0 := by
  exact complement_readout_exchange_iff j a

theorem balanced_newRegion_charge_zero {d : Nat} {C D : Context d}
    (j : ContextEmbedding C D) (hC : Balanced C) (hD : Balanced D) :
    charge D (newRegion j) = 0 := by
  have hdecomp : D.current = C.current.map (mapEvent j) ∪ newRegion j := by
    simpa [emptySelection] using (complement_decomposition j (emptySelection C))
  have hdisj : Disjoint (C.current.map (mapEvent j)) (newRegion j) := by
    simpa [emptySelection] using
      (complement_map_disjoint_newRegion j (emptySelection C))
  have hsum : background D =
      charge D (C.current.map (mapEvent j)) + charge D (newRegion j) := by
    rw [background, hdecomp]
    simp only [charge]
    rw [Finset.sum_union hdisj]
  have htransport : charge D (C.current.map (mapEvent j)) = background C := by
    change readout (mapSelection j (fullSelection C)) = background C
    rw [map_readout]
    rfl
  change background D = 0 at hD
  rw [hsum, htransport, hC] at hD
  simpa using hD

/-- The complete proposition packages transport, the disjoint complement split,
    its charge defect, and the exactness and balance consequences. -/
theorem context_extension_complement_spec {d : Nat} {C D : Context d}
    (j : ContextEmbedding C D) (a : Selection C) :
    q ⟨D, mapSelection j a⟩ = q ⟨C, a⟩ ∧
      D.current \ a.val.map (mapEvent j) =
        (C.current \ a.val).map (mapEvent j) ∪ newRegion j ∧
      Disjoint ((C.current \ a.val).map (mapEvent j)) (newRegion j) ∧
      q ⟨D, complement (mapSelection j a)⟩ -
          q ⟨C, complement a⟩ = charge D (newRegion j) ∧
      (D.current \ a.val.map (mapEvent j) =
          (C.current \ a.val).map (mapEvent j) ↔
        newRegion j = ∅) ∧
      (q ⟨D, complement (mapSelection j a)⟩ =
          q ⟨C, complement a⟩ ↔
        charge D (newRegion j) = 0) ∧
      (Balanced C → Balanced D → charge D (newRegion j) = 0) := by
  refine ⟨q_map j a, complement_decomposition j a,
    complement_map_disjoint_newRegion j a,
    q_complement_charge_difference j a,
    complement_decomposition_exact_iff j a,
    q_complement_readout_exchange_iff j a, ?_⟩
  exact fun hC hD => balanced_newRegion_charge_zero j hC hD

end
end D5.S3.ConceptDynamics.Spacetime.ContextExtensionComplement
