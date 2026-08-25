/- GID: D5/S3/ConceptDynamics/Epistemic/FiberInteriorEquivalence
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Epistemic/FiberInteriorEquivalence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Interior in the readout partition topology is truth on the current fiber. -/

import D5.S3.ConceptDynamics.Epistemic.PartitionKnowledgeNegativeIntrospection

/- Library-search audit trail (2026-08-25):
   * Exact family primitive hits `partitionTopology` and `fiberKnowledge` are
     imported rather than redeclared. They respectively construct the source's
     readout-induced topology and its quantified fiber predicate.
   * Repository searches for `partitionTopology`, `fiberKnowledge`, `interior`,
     and the quantified body shape found no theorem stating this equivalence.
   * `TopologicalKnowledgeOperator` is adjacent but proves only the four general
     interior laws, not the partition-fiber characterization.
   * Pinned Mathlib's `isOpen_induced_iff`, `isOpen_interior`,
     `interior_subset`, and `interior_maximal` are applied directly. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Epistemic.FiberInteriorEquivalence

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.Epistemic.PartitionKnowledgeNegativeIntrospection

/-- A proposition is interior-true at a state in the readout partition topology
exactly when it is true at every state with the same readout. -/
theorem fiber_interior_equivalence
    {X B : Type*} (readout : Concept X B) (predicate : Set X) (x : X) :
    x ∈ @interior X (partitionTopology readout) predicate ↔
      forall y, readout y = readout x -> y ∈ predicate := by
  letI : TopologicalSpace B := ⊥
  letI : DiscreteTopology B := ⟨rfl⟩
  letI : TopologicalSpace X := partitionTopology readout
  change x ∈ @interior X (partitionTopology readout) predicate ↔
    x ∈ fiberKnowledge readout predicate
  constructor
  · intro xInterior y sameReadout
    have interiorOpen :
        @IsOpen X (partitionTopology readout)
          (@interior X (partitionTopology readout) predicate) :=
      isOpen_interior
    change ∃ coordinates : Set B,
      @IsOpen B (⊥ : TopologicalSpace B) coordinates ∧
        readout ⁻¹' coordinates =
          @interior X (partitionTopology readout) predicate at interiorOpen
    rcases interiorOpen with ⟨coordinates, _coordinatesOpen, preimage_eq⟩
    have xCoordinate : readout x ∈ coordinates := by
      change x ∈ readout ⁻¹' coordinates
      rw [preimage_eq]
      exact xInterior
    have yInterior :
        y ∈ @interior X (partitionTopology readout) predicate := by
      rw [← preimage_eq]
      change readout y ∈ coordinates
      rw [sameReadout]
      exact xCoordinate
    exact interior_subset yInterior
  · intro fiberTruth
    let fiber : Set X := {y | readout y = readout x}
    have fiberOpen : @IsOpen X (partitionTopology readout) fiber := by
      change ∃ coordinates : Set B,
        @IsOpen B (⊥ : TopologicalSpace B) coordinates ∧
          readout ⁻¹' coordinates = fiber
      refine ⟨{readout x}, isOpen_discrete _, ?_⟩
      ext y
      change readout y = readout x ↔ readout y = readout x
      rfl
    have fiberSubset : fiber ⊆ predicate := by
      intro y yFiber
      exact fiberTruth y yFiber
    exact interior_maximal fiberSubset fiberOpen (by simp [fiber])

#print axioms fiber_interior_equivalence

end D5.S3.ConceptDynamics.Epistemic.FiberInteriorEquivalence
