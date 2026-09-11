/- GID: D5/S3/ConceptDynamics/Spacetime/ContextExtensionComplement
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Spacetime/ContextExtensionComplement
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A finite context embedding decomposes transported complements into the old complement and the new current region; atom sha256:20ec8078362e29e89f35f4c3a5d47fdb2453b0b2f3448564613f86b9524f9f92 -/

/-
All public theorems are bind-only; no escape witness is claimed.
Module admission_basis: rule-11-upstream-wrapper. The required source clauses are
Definition 11's exact current-image guard and Proposition 8's transport, disjoint
complement split, charge defect, and exactness/balance criteria (atom
sha256:20ec8078362e29e89f35f4c3a5d47fdb2453b0b2f3448564613f86b9524f9f92).
The set/finset bridge below directly applies the frozen RelativeComplement API;
charge transport is the required specialization of Finset.sum_map.
Companion consumer -> prerequisite edges:
current_map_subset -> current_image_eq; mapSelection -> current_map_subset;
map_readout -> map_charge; q_map -> map_readout;
complement_charge_difference -> complement_decomposition,
  complement_map_disjoint_newRegion, map_charge;
q_complement_charge_difference -> complement_charge_difference;
complement_decomposition_exact_iff -> complement_decomposition,
  complement_map_disjoint_newRegion;
complement_readout_exchange_iff -> complement_charge_difference;
q_complement_readout_exchange_iff -> complement_readout_exchange_iff;
balanced_newRegion_charge_zero -> complement_charge_difference;
context_extension_complement_spec -> its seven named component theorems.
The preregistered downstream consumer
ContextExtensionComposition.context_extension_composition_spec uses this
transport and charge API. All results quantify over arbitrary finite contexts;
utility: none (no bounded computation, checker, numeric reduction, or instance).
-/

import D5.S3.ConceptDynamics.Spacetime.ComplementCharge
import D5.S3.ConceptDynamics.Negation.RelativeComplement
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.Spacetime.ContextExtensionComplement

open D5.S0.History.Spacetime.ArchiveCarrier
open ComplementCharge
open D5.S3.ConceptDynamics.Negation.RelativeComplement
noncomputable section
open scoped Classical
open scoped BigOperators

/-- Definition 11: preserve all archive attributes and causal iff, and preserve
    and reflect current membership on every old event (no reactivation). -/
structure ContextEmbedding {d : Nat} (C D : Context d) where
  archiveEmbedding : ArchiveEmbedding C.archive D.archive
  current_iff : ∀ e, archiveEmbedding.eventMap e ∈ D.current ↔ e ∈ C.current

abbrev mapEvent {d : Nat} {C D : Context d}
    (j : ContextEmbedding C D) : C.Event ↪ D.Event :=
  j.archiveEmbedding.eventMap

/-- The displayed source guard, with the archived event subtype as the domain:
    the image of the whole archive is exactly the range of the event map. -/
theorem current_image_eq {d : Nat} {C D : Context d}
    (j : ContextEmbedding C D) :
    mapEvent j '' (C.current : Set C.Event) =
      (D.current : Set D.Event) ∩ Set.range (mapEvent j) := by
  have h : (C.current : Set C.Event) = mapEvent j ⁻¹' (D.current : Set D.Event) := by
    ext e
    exact (j.current_iff e).symm
  rw [h]
  exact Set.image_preimage_eq_inter_range

/-- Containment is a consequence of the exact guard, not the embedding contract. -/
theorem ContextEmbedding.current_map_subset {d : Nat} {C D : Context d}
    (j : ContextEmbedding C D) : C.current.map (mapEvent j) ⊆ D.current := by
  rw [← Finset.coe_subset, Finset.coe_map, current_image_eq]
  exact Set.inter_subset_left

def mapSelection {d : Nat} {C D : Context d}
    (j : ContextEmbedding C D) (a : Selection C) : Selection D :=
  ⟨a.val.map (mapEvent j), by
    exact (Finset.map_subset_map.mpr a.property).trans j.current_map_subset⟩

def newRegion {d : Nat} {C D : Context d}
    (j : ContextEmbedding C D) : Finset D.Event :=
  D.current \ C.current.map (mapEvent j)

/-- Attribute preservation reindexes the charge of any finite archived subset. -/
theorem map_charge {d : Nat} {C D : Context d}
    (j : ContextEmbedding C D) (s : Finset C.Event) :
    charge D (s.map (mapEvent j)) = charge C s := by
  simp only [charge, Finset.sum_map, contribution, j.archiveEmbedding.attributes_eq]

theorem map_readout {d : Nat} {C D : Context d}
    (j : ContextEmbedding C D) (a : Selection C) :
    readout (mapSelection j a) = readout a :=
  map_charge j a.val

theorem q_map {d : Nat} {C D : Context d}
    (j : ContextEmbedding C D) (a : Selection C) :
    q ⟨D, mapSelection j a⟩ = q ⟨C, a⟩ := by
  exact map_readout j a

theorem complement_map_disjoint_newRegion {d : Nat} {C D : Context d}
    (j : ContextEmbedding C D) (a : Selection C) :
    Disjoint ((C.current \ a.val).map (mapEvent j)) (newRegion j) := by
  apply Finset.disjoint_coe.mp
  simpa only [Finset.map_sdiff, newRegion, Finset.coe_sdiff, relativeComplement] using
    (relativeComplement_domain_extension_disjoint
      (A := (a.val.map (mapEvent j) : Set D.Event))
      (U := (C.current.map (mapEvent j) : Set D.Event)) (V := (D.current : Set D.Event)))

theorem complement_decomposition {d : Nat} {C D : Context d}
    (j : ContextEmbedding C D) (a : Selection C) :
    D.current \ a.val.map (mapEvent j) =
      (C.current \ a.val).map (mapEvent j) ∪ newRegion j := by
  apply Finset.coe_injective
  simpa only [Finset.map_sdiff, newRegion, Finset.coe_union, Finset.coe_sdiff,
    relativeComplement] using
    (relativeComplement_domain_extension
      (Finset.coe_subset.mpr (Finset.map_subset_map.mpr a.property))
      (Finset.coe_subset.mpr j.current_map_subset))

theorem complement_charge_difference {d : Nat} {C D : Context d}
    (j : ContextEmbedding C D) (a : Selection C) :
    readout (complement (mapSelection j a)) - readout (complement a) =
      charge D (newRegion j) := by
  change charge D (D.current \ a.val.map (mapEvent j)) -
    charge C (C.current \ a.val) = charge D (newRegion j)
  rw [complement_decomposition j a, charge,
    Finset.sum_union (complement_map_disjoint_newRegion j a)]
  change charge D ((C.current \ a.val).map (mapEvent j)) +
    charge D (newRegion j) - charge C (C.current \ a.val) = _
  rw [map_charge]
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
  rw [complement_decomposition j a, Finset.union_eq_left]
  exact ⟨fun h => (complement_map_disjoint_newRegion j a).eq_bot_of_ge h,
    fun h => h ▸ Finset.empty_subset _⟩

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
  change background C = 0 at hC
  change background D = 0 at hD
  simpa only [complement_readout, map_readout, empty_readout, hC, hD, sub_self] using
    (complement_charge_difference j (emptySelection C)).symm

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
