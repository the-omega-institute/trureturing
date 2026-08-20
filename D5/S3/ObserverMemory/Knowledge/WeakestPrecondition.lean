/- GID: D5/S3/ObserverMemory/Knowledge/WeakestPrecondition
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Knowledge/WeakestPrecondition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Weakest preconditions are inverse images and have the largest guaranteeing domain. -/

import Mathlib.Data.Set.Function

/- Library-search audit trail (2026-08-20):
   * Repository searches for `wp_minimal`, weakest-precondition names, and the
     preimage/subset statement shape found no covering D5 declaration.
   * Pinned Mathlib's exact `Set.mapsTo_iff_subset_preimage` identifies the
     pointwise guarantee with inclusion in an inverse image; it is applied
     below rather than reproved.
   * Pinned Mathlib has no program-logic declaration packaging both that
     characterization and the largest-domain clause. -/

namespace D5.S3.ObserverMemory.Knowledge.WeakestPrecondition

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- The weakest precondition of `Q` under `process` is its inverse image. -/
def weakestPrecondition {X Y : Type*} (process : X -> Y) (Q : Set Y) : Set X :=
  process ⁻¹' Q

/-- A precondition guarantees `Q` exactly when it is contained in the inverse
image of `Q`; every guaranteeing precondition is therefore contained in this
largest admissible domain. -/
theorem wp_minimal {X Y : Type*} (process : X -> Y) (Q : Set Y) (P : Set X) :
    ((∀ x, x ∈ P -> process x ∈ Q) ↔ P ⊆ weakestPrecondition process Q) ∧
      ∀ R : Set X, (∀ x, x ∈ R -> process x ∈ Q) ->
        R ⊆ weakestPrecondition process Q := by
  constructor
  · constructor
    · intro hGuarantees
      apply Set.mapsTo_iff_subset_preimage.mp
      intro x hx
      exact hGuarantees x hx
    · intro hSubset x hx
      exact Set.mapsTo_iff_subset_preimage.mpr hSubset hx
  · intro R hR
    have hMapsTo : Set.MapsTo process R Q := hR
    simpa only [weakestPrecondition] using
      (Set.mapsTo_iff_subset_preimage.mp hMapsTo)

/-- A two-state identity process witnesses all quantified domains and the
guarantee relation used in the characterization. -/
example :
    ((∀ x : Fin 2, x ∈ Set.univ -> id x ∈ Set.univ) ↔
        Set.univ ⊆ weakestPrecondition (id : Fin 2 -> Fin 2) Set.univ) ∧
      ∀ R : Set (Fin 2), (∀ x, x ∈ R -> id x ∈ Set.univ) ->
        R ⊆ weakestPrecondition (id : Fin 2 -> Fin 2) Set.univ := by
  exact wp_minimal (id : Fin 2 -> Fin 2) Set.univ Set.univ

#print axioms wp_minimal

end D5.S3.ObserverMemory.Knowledge.WeakestPrecondition
