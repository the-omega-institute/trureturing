/- GID: D5/S3/ConceptDynamics/ObservationTopology/PartitionTopologyKernel
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ObservationTopology/PartitionTopologyKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Inseparability in a readout partition topology is exactly equality in the readout kernel. -/

import D5.S3.ConceptDynamics.Epistemic.PartitionKnowledgeNegativeIntrospection
import Mathlib.Topology.Inseparable

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.ObservationTopology.PartitionTopologyKernel
open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.Epistemic.PartitionKnowledgeNegativeIntrospection

theorem partition_inseparable_iff_kernel
    {X B : Type*} (readout : Concept X B) (x y : X) :
    @Inseparable X (partitionTopology readout) x y <-> readout x = readout y := by
  letI : TopologicalSpace B := ⊥
  letI : DiscreteTopology B := ⟨rfl⟩
  constructor
  · intro inseparable
    by_contra different
    let fiber : Set X := readout ⁻¹' {readout x}
    have fiberOpen : @IsOpen X (partitionTopology readout) fiber := by
      rw [partitionTopology, isOpen_induced_iff]
      exact ⟨{readout x}, isOpen_discrete _, rfl⟩
    have xInFiber : x ∈ fiber := by simp [fiber]
    have yNotInFiber : y ∉ fiber := by
      intro yInFiber
      have equality : readout y = readout x := by simpa [fiber] using yInFiber
      exact different equality.symm
    exact yNotInFiber
      ((@Inseparable.mem_open_iff X (partitionTopology readout)
        x y fiber inseparable fiberOpen).mp xInFiber)
  · intro sameReadout
    apply (@inseparable_iff_forall_isOpen X (partitionTopology readout) x y).2
    intro set setOpen
    rw [partitionTopology, isOpen_induced_iff] at setOpen
    rcases setOpen with ⟨coordinates, _coordinatesOpen, rfl⟩
    simpa only [Set.mem_preimage, sameReadout]

theorem partitionTopology_eq_of_kernel_iff
    {X B C : Type*} (first : Concept X B) (second : Concept X C)
    (kernelIff : forall x y, first x = first y <-> second x = second y) :
    partitionTopology first = partitionTopology second := by
  letI : TopologicalSpace B := ⊥
  letI : DiscreteTopology B := ⟨rfl⟩
  letI : TopologicalSpace C := ⊥
  letI : DiscreteTopology C := ⟨rfl⟩
  apply TopologicalSpace.ext_iff.mpr
  intro set
  constructor
  · intro firstOpen
    rw [partitionTopology, isOpen_induced_iff] at firstOpen ⊢
    rcases firstOpen with ⟨coordinates, _coordinatesOpen, rfl⟩
    let secondCoordinates : Set C :=
      {coordinate | exists x, second x = coordinate ∧ first x ∈ coordinates}
    refine ⟨secondCoordinates, isOpen_discrete _, ?_⟩
    ext x
    change (exists y, second y = second x ∧ first y ∈ coordinates) <->
      first x ∈ coordinates
    constructor
    · rintro ⟨y, sameSecond, hy⟩
      have sameFirst : first y = first x := (kernelIff y x).2 sameSecond
      rw [sameFirst] at hy
      exact hy
    · intro hx; exact ⟨x, rfl, hx⟩
  · intro secondOpen
    rw [partitionTopology, isOpen_induced_iff] at secondOpen ⊢
    rcases secondOpen with ⟨coordinates, _coordinatesOpen, rfl⟩
    let firstCoordinates : Set B :=
      {coordinate | exists x, first x = coordinate ∧ second x ∈ coordinates}
    refine ⟨firstCoordinates, isOpen_discrete _, ?_⟩
    ext x
    change (exists y, first y = first x ∧ second y ∈ coordinates) <->
      second x ∈ coordinates
    constructor
    · rintro ⟨y, sameFirst, hy⟩
      have sameSecond : second y = second x := (kernelIff y x).1 sameFirst
      rw [sameSecond] at hy
      exact hy
    · intro hx; exact ⟨x, rfl, hx⟩

#print axioms partition_inseparable_iff_kernel
#print axioms partitionTopology_eq_of_kernel_iff
end D5.S3.ConceptDynamics.ObservationTopology.PartitionTopologyKernel
