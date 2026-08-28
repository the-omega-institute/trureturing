/- GID: D5/S3/ConceptDynamics/ObservationTopology/MultiTargetObservationTopology
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ObservationTopology/MultiTargetObservationTopology
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Joint-target continuity and separation deficits decompose into component targets. -/

import D5.S3.ConceptDynamics.ObservationTopology.TargetContinuityFactorization
import D5.S3.ConceptDynamics.ObservationTopology.ResidualSeparationTopology
import D5.S3.ConceptDynamics.ObservationTopology.PartitionTopologyKernel
import D5.S3.ConceptDynamics.Refinement.MultiTargetMinimalSufficiency

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.ObservationTopology.MultiTargetObservationTopology

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.Refinement.MultiTargetMinimalSufficiency
open D5.S3.ConceptDynamics.Epistemic.PartitionKnowledgeNegativeIntrospection
open D5.S3.ConceptDynamics.ObservationTopology.TargetContinuityFactorization
open D5.S3.ConceptDynamics.ObservationTopology.ResidualSeparationTopology

/-- A dependent joint target is continuous from a readout partition topology
exactly when every component target is continuous. -/
theorem jointTarget_continuous_iff_components
    {X Index Coordinate : Type*} {Target : Index → Type*}
    (readout : Concept X Coordinate)
    (targets : ∀ index, Concept X (Target index)) :
    @Continuous X (∀ index, Target index) (partitionTopology readout) ⊥
        (jointTarget targets) ↔
      ∀ index,
        @Continuous X (Target index) (partitionTopology readout) ⊥
          (targets index) := by
  constructor
  · intro jointContinuous index
    apply (continuous_partition_iff_fiber_constant readout (targets index)).2
    intro x y sameReadout
    have jointConstant :=
      (continuous_partition_iff_fiber_constant readout
        (jointTarget targets)).1 jointContinuous sameReadout
    exact congrFun jointConstant index
  · intro componentContinuous
    apply (continuous_partition_iff_fiber_constant readout
      (jointTarget targets)).2
    intro x y sameReadout
    funext index
    exact (continuous_partition_iff_fiber_constant readout
      (targets index)).1 (componentContinuous index) sameReadout

/-- A pair is a separation deficit for the joint target exactly when it is a
deficit for at least one component target. -/
theorem mem_jointTarget_separationDeficit_iff
    {X Index Current : Type*} {Target : Index → Type*}
    (current : Concept X Current)
    (targets : ∀ index, Concept X (Target index))
    (pair : X × X) :
    pair ∈ separationDeficit current (jointTarget targets) ↔
      ∃ index, pair ∈ separationDeficit current (targets index) := by
  classical
  rw [← defectRelation_eq_separationDeficit current (jointTarget targets)]
  constructor
  · rintro ⟨sameCurrent, jointDifferent⟩
    have componentDifferent :
        ∃ index, targets index pair.1 ≠ targets index pair.2 := by
      by_contra noComponent
      apply jointDifferent
      funext index
      by_contra different
      exact noComponent ⟨index, different⟩
    rcases componentDifferent with ⟨index, different⟩
    refine ⟨index, ?_⟩
    rw [← defectRelation_eq_separationDeficit current (targets index)]
    exact ⟨sameCurrent, different⟩
  · rintro ⟨index, componentDeficit⟩
    rw [← defectRelation_eq_separationDeficit current (targets index)] at componentDeficit
    refine ⟨componentDeficit.1, ?_⟩
    intro jointEqual
    exact componentDeficit.2 (congrFun jointEqual index)

/-- The joint-target separation deficit is the union of the component deficits. -/
theorem jointTarget_separationDeficit_eq_iUnion
    {X Index Current : Type*} {Target : Index → Type*}
    (current : Concept X Current)
    (targets : ∀ index, Concept X (Target index)) :
    separationDeficit current (jointTarget targets) =
      ⋃ index, separationDeficit current (targets index) := by
  ext pair
  rw [mem_jointTarget_separationDeficit_iff]
  constructor
  · exact Set.mem_iUnion.2
  · exact Set.mem_iUnion.1

/-- Joint-target separation is complete exactly when every component deficit is
empty. -/
theorem jointTarget_separationDeficit_empty_iff_components
    {X Index Current : Type*} {Target : Index → Type*}
    (current : Concept X Current)
    (targets : ∀ index, Concept X (Target index)) :
    separationDeficit current (jointTarget targets) = ∅ ↔
      ∀ index, separationDeficit current (targets index) = ∅ := by
  rw [jointTarget_separationDeficit_eq_iUnion]
  constructor
  · intro unionEmpty index
    ext pair
    constructor
    · intro componentMember
      have unionMember :
          pair ∈ ⋃ index, separationDeficit current (targets index) :=
        Set.mem_iUnion.2 ⟨index, componentMember⟩
      rw [unionEmpty] at unionMember
      exact unionMember
    · intro impossible
      exact impossible.elim
  · intro componentsEmpty
    ext pair
    constructor
    · intro unionMember
      rcases Set.mem_iUnion.1 unionMember with ⟨index, componentMember⟩
      rw [componentsEmpty index] at componentMember
      exact componentMember
    · intro impossible
      exact impossible.elim

#print axioms jointTarget_continuous_iff_components
#print axioms jointTarget_separationDeficit_eq_iUnion

end D5.S3.ConceptDynamics.ObservationTopology.MultiTargetObservationTopology
