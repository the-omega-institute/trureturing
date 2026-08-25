/- GID: D5/S3/ConceptDynamics/ObservationTopology/TargetContinuityFactorization
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ObservationTopology/TargetContinuityFactorization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: On an inhabited source, recoverability is continuity into the discrete target. -/

import D5.S3.ConceptDynamics.ObservationTopology.PartitionTopologyKernel
import D5.S3.ConceptDynamics.Restoration.TargetRecoveryCriterion

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.ObservationTopology.TargetContinuityFactorization
open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.Epistemic.PartitionKnowledgeNegativeIntrospection
open D5.S3.ConceptDynamics.ObservationTopology.PartitionTopologyKernel
open D5.S3.ConceptDynamics.Restoration.TargetRecoveryCriterion

theorem continuous_partition_iff_fiber_constant
    {X Coordinate Target : Type*} (readout : Concept X Coordinate)
    (target : Concept X Target) :
    @Continuous X Target (partitionTopology readout) ⊥ target <->
      forall ⦃x y : X⦄, readout x = readout y -> target x = target y := by
  letI : TopologicalSpace Target := ⊥
  letI : DiscreteTopology Target := ⟨rfl⟩
  constructor
  · intro targetContinuous x y sameReadout
    have sourceInseparable : @Inseparable X (partitionTopology readout) x y :=
      (partition_inseparable_iff_kernel readout x y).2 sameReadout
    have preimageOpen :
        @IsOpen X (partitionTopology readout) (target ⁻¹' {target x}) :=
      (@continuous_def X Target (partitionTopology readout) ⊥ target).1
        targetContinuous _ (isOpen_discrete _)
    have xInPreimage : x ∈ target ⁻¹' {target x} := by simp
    have yInPreimage : y ∈ target ⁻¹' {target x} :=
      ((@Inseparable.mem_open_iff X (partitionTopology readout)
        x y (target ⁻¹' {target x}) sourceInseparable preimageOpen).mp
          xInPreimage)
    have targetYX : target y = target x := by simpa using yInPreimage
    exact targetYX.symm
  · intro fiberConstant
    letI : TopologicalSpace Coordinate := ⊥
    letI : DiscreteTopology Coordinate := ⟨rfl⟩
    rw [continuous_def]
    intro targetOpen _targetOpen
    rw [partitionTopology, isOpen_induced_iff]
    let coordinates : Set Coordinate :=
      {coordinate | exists x, readout x = coordinate ∧ target x ∈ targetOpen}
    refine ⟨coordinates, ?_, ?_⟩
    · exact isOpen_discrete _
    · ext x
      change (exists y, readout y = readout x ∧ target y ∈ targetOpen) <->
        target x ∈ targetOpen
      constructor
      · rintro ⟨y, sameCoordinate, hy⟩
        have sameTarget : target y = target x := fiberConstant sameCoordinate
        rw [sameTarget] at hy
        exact hy
      · intro hx; exact ⟨x, rfl, hx⟩

theorem target_factors_iff_continuous_partition
    {X Coordinate Target : Type*} [Nonempty X]
    (readout : Concept X Coordinate) (target : Concept X Target) :
    Refines target readout <->
      @Continuous X Target (partitionTopology readout) ⊥ target := by
  constructor
  · rintro ⟨recover, recovery⟩
    apply (continuous_partition_iff_fiber_constant readout target).2
    intro x y sameReadout
    rw [recovery]
    exact congrArg recover sameReadout
  · intro targetContinuous
    exact (target_recovery_criterion readout target).1.mpr
      ((continuous_partition_iff_fiber_constant readout target).1 targetContinuous)

#print axioms target_factors_iff_continuous_partition
end D5.S3.ConceptDynamics.ObservationTopology.TargetContinuityFactorization
