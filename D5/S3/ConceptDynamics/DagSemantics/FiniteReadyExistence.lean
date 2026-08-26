/- GID: D5/S3/ConceptDynamics/DagSemantics/FiniteReadyExistence
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DagSemantics/FiniteReadyExistence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Every nonempty finite pending set has a ready minimum under a topological linear order. -/

import D5.S3.ConceptDynamics.DagSemantics.ExecutableFrontier
import D5.S3.ConceptDynamics.DagSemantics.StrictDependencyCoordinate
import Mathlib.Data.Finset.Max

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DagSemantics.FiniteReadyExistence

open D5.S3.ConceptDynamics.DagSemantics.ExecutableFrontier
open D5.S3.ConceptDynamics.DagSemantics.StrictDependencyCoordinate

/-- The minimum pending node in a linear topological coordinate has no pending prerequisite. -/
theorem min_pending_ready_over_complement
    {V : Type*} [LinearOrder V]
    {edge : V → V → Prop}
    (edgeForward : StrictDependencyCoordinate edge (id : V → V))
    (pending : Finset V) (pendingNonempty : pending.Nonempty) :
    (pending.min' pendingNonempty) ∈ pending ∧
      ReadyOver edge ((↑pending : Set V)ᶜ) (pending.min' pendingNonempty) := by
  constructor
  · exact Finset.min'_mem pending pendingNonempty
  · intro prerequisite dependency
    have prerequisiteLt : prerequisite < pending.min' pendingNonempty := by
      simpa only [id_eq] using edgeForward dependency
    by_contra prerequisiteOutside
    have prerequisiteIn : prerequisite ∈ pending := by
      simpa using prerequisiteOutside
    have minimumLe : pending.min' pendingNonempty ≤ prerequisite :=
      Finset.min'_le pending prerequisite prerequisiteIn
    exact (not_lt_of_ge minimumLe) prerequisiteLt

/-- Consequently, the complement frontier of a nonempty finite pending set is nonempty. -/
theorem complement_frontier_nonempty
    {V : Type*} [LinearOrder V]
    {edge : V → V → Prop}
    (edgeForward : StrictDependencyCoordinate edge (id : V → V))
    (pending : Finset V) (pendingNonempty : pending.Nonempty) :
    (executableFrontier edge ((↑pending : Set V)ᶜ) (↑pending : Set V)).Nonempty := by
  refine ⟨pending.min' pendingNonempty, ?_⟩
  exact min_pending_ready_over_complement edgeForward pending pendingNonempty

#print axioms min_pending_ready_over_complement
#print axioms complement_frontier_nonempty

end D5.S3.ConceptDynamics.DagSemantics.FiniteReadyExistence
