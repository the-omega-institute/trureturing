/- GID: D5/S3/ConceptDynamics/ObservationTopology/RedundantCoordinateTopology
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ObservationTopology/RedundantCoordinateTopology
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A joined coordinate changes topology exactly when it is not recoverable. -/

import D5.S3.ConceptDynamics.ObservationTopology.ObservationOrderEquivalence
import D5.S3.ConceptDynamics.ObservationTopology.PrimitiveEscapeStrictRefinement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.ObservationTopology.RedundantCoordinateTopology

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.Epistemic.PartitionKnowledgeNegativeIntrospection
open D5.S3.ConceptDynamics.ObservationTopology.PartitionTopologyKernel
open D5.S3.ConceptDynamics.ObservationTopology.ObservationOrderEquivalence
open D5.S3.ConceptDynamics.ObservationTopology.PrimitiveEscapeStrictRefinement
open D5.S3.ConceptDynamics.Restoration.TargetRecoveryCriterion

/-- A coordinate already recoverable from the current readout is topologically
redundant after joining. -/
theorem redundant_coordinate_topology_eq
    {X Current Candidate : Type*}
    (current : Concept X Current) (candidate : Concept X Candidate)
    (redundant : Refines candidate current) :
    partitionTopology (conceptJoin current candidate) =
      partitionTopology current := by
  rcases redundant with ⟨recover, recovery⟩
  apply partitionTopology_eq_of_kernel_iff
  intro x y
  constructor
  · intro sameJoin
    exact congrArg Prod.fst sameJoin
  · intro sameCurrent
    apply Prod.ext sameCurrent
    rw [recovery]
    exact congrArg recover sameCurrent

/-- On an inhabited source, equality of the joined and current observation
topologies is exactly recoverability of the added coordinate. -/
theorem join_topology_eq_iff_coordinate_redundant
    {X Current Candidate : Type*} [Nonempty X]
    (current : Concept X Current) (candidate : Concept X Candidate) :
    partitionTopology (conceptJoin current candidate) =
        partitionTopology current ↔
      Refines candidate current := by
  constructor
  · intro topologyEqual
    apply (target_recovery_criterion current candidate).1.mpr
    intro x y sameCurrent
    have currentInseparable :
        @Inseparable X (partitionTopology current) x y :=
      (partition_inseparable_iff_kernel current x y).2 sameCurrent
    have joinInseparable :
        @Inseparable X (partitionTopology (conceptJoin current candidate)) x y := by
      exact topologyEqual.symm ▸ currentInseparable
    have sameJoin :=
      (partition_inseparable_iff_kernel
        (conceptJoin current candidate) x y).1 joinInseparable
    exact congrArg Prod.snd sameJoin
  · exact redundant_coordinate_topology_eq current candidate

/-- Adding a coordinate strictly refines the observation topology exactly when
that coordinate cannot already be recovered from the current readout. -/
theorem coordinate_inadequate_iff_strict_join_refinement
    {X Current Candidate : Type*} [Nonempty X]
    (current : Concept X Current) (candidate : Concept X Candidate) :
    (¬Refines candidate current) ↔
      StrictObservationRefinement (partitionTopology current)
        (partitionTopology (conceptJoin current candidate)) := by
  have oldOpenInJoin :
      ObservationOpenInclusion (partitionTopology current)
        (partitionTopology (conceptJoin current candidate)) :=
    refines_implies_partition_open_inclusion current
      (conceptJoin current candidate)
      (concept_join_universal current candidate
        (conceptJoin current candidate)).1
  constructor
  · intro inadequate
    have topologyDifferent :
        partitionTopology (conceptJoin current candidate) ≠
          partitionTopology current := by
      intro topologyEqual
      exact inadequate
        ((join_topology_eq_iff_coordinate_redundant current candidate).1
          topologyEqual)
    have witness : ∃ set,
        @IsOpen X (partitionTopology (conceptJoin current candidate)) set ∧
          ¬ @IsOpen X (partitionTopology current) set := by
      by_contra noWitness
      have reverseInclusion :
          ObservationOpenInclusion
            (partitionTopology (conceptJoin current candidate))
            (partitionTopology current) := by
        intro set setOpen
        by_contra notOpen
        exact noWitness ⟨set, setOpen, notOpen⟩
      apply topologyDifferent
      apply TopologicalSpace.ext_iff.mpr
      intro set
      exact ⟨reverseInclusion set, oldOpenInJoin set⟩
    exact ⟨oldOpenInJoin, witness⟩
  · intro strict redundant
    have topologyEqual := redundant_coordinate_topology_eq current candidate redundant
    rcases strict.2 with ⟨set, setOpenJoin, setNotOpenCurrent⟩
    apply setNotOpenCurrent
    exact topologyEqual ▸ setOpenJoin

#print axioms join_topology_eq_iff_coordinate_redundant
#print axioms coordinate_inadequate_iff_strict_join_refinement

end D5.S3.ConceptDynamics.ObservationTopology.RedundantCoordinateTopology
