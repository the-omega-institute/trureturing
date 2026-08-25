/- GID: D5/S3/ConceptDynamics/ObservationTopology/PartitionTopologyKernel
   generality: G
   mirror-B: none(waiver:formal-unit-only)
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
    exact yNotInFiber ((inseparable.mem_open_iff fiberOpen).mp xInFiber)
  · intro sameReadout
    rw [inseparable_iff_forall_isOpen]
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
    change first x ∈ coordinates <->
      exists y, second y = second x ∧ first y ∈ coordinates
    constructor
    · intro hx; exact ⟨x, rfl, hx⟩
    · rintro ⟨y, sameSecond, hy⟩
      have sameFirst : first y = first x := (kernelIff y x).2 sameSecond
      rw [sameFirst] at hy
      exact hy
  · intro secondOpen
    rw [partitionTopology, isOpen_induced_iff] at secondOpen ⊢
    rcases secondOpen with ⟨coordinates, _coordinatesOpen, rfl⟩
    let firstCoordinates : Set B :=
      {coordinate | exists x, first x = coordinate ∧ second x ∈ coordinates}
    refine ⟨firstCoordinates, isOpen_discrete _, ?_⟩
    ext x
    change second x ∈ coordinates <->
      exists y, first y = first x ∧ second y ∈ coordinates
    constructor
    · intro hx; exact ⟨x, rfl, hx⟩
    · rintro ⟨y, sameFirst, hy⟩
      have sameSecond : second y = second x := (kernelIff y x).1 sameFirst
      rw [sameSecond] at hy
      exact hy

#print axioms partition_inseparable_iff_kernel
#print axioms partitionTopology_eq_of_kernel_iff
end D5.S3.ConceptDynamics.ObservationTopology.PartitionTopologyKernel
