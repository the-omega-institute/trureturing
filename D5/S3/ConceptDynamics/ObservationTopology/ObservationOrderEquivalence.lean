/- GID: D5/S3/ConceptDynamics/ObservationTopology/ObservationOrderEquivalence
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ObservationTopology/ObservationOrderEquivalence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Factorization equals partition-open inclusion; defects are antitone. -/

import D5.S3.ConceptDynamics.ObservationTopology.ResidualSeparationTopology
import D5.S3.ConceptDynamics.ObservationTopology.TargetContinuityFactorization
import D5.S3.ConceptDynamics.Topology.ContinuousRefinementObservationTopology

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.ObservationTopology.ObservationOrderEquivalence

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.TargetRisk.RefinementRiskCostTradeoff
open D5.S3.ConceptDynamics.Epistemic.PartitionKnowledgeNegativeIntrospection
open D5.S3.ConceptDynamics.ObservationTopology.PartitionTopologyKernel
open D5.S3.ConceptDynamics.ObservationTopology.ResidualSeparationTopology
open D5.S3.ConceptDynamics.Restoration.TargetRecoveryCriterion
open D5.S3.ConceptDynamics.Topology.ContinuousRefinementObservationTopology

/-- `fine` is observation-topologically at least as informative as `coarse`. -/
def ObservationOpenInclusion {X : Type*}
    (coarse fine : TopologicalSpace X) : Prop :=
  ∀ set, @IsOpen X coarse set → @IsOpen X fine set

/-- Factorization through a finer readout transports every coarse observable
open set to the finer partition topology. -/
theorem refines_implies_partition_open_inclusion
    {X Coarse Fine : Type*}
    (coarse : Concept X Coarse) (fine : Concept X Fine)
    (refinement : Refines coarse fine) :
    ObservationOpenInclusion (partitionTopology coarse)
      (partitionTopology fine) := by
  rcases refinement with ⟨factor, factorization⟩
  letI : TopologicalSpace Coarse := ⊥
  letI : DiscreteTopology Coarse := ⟨rfl⟩
  letI : TopologicalSpace Fine := ⊥
  letI : DiscreteTopology Fine := ⟨rfl⟩
  have factorContinuous : @Continuous Fine Coarse ⊥ ⊥ factor := by
    rw [continuous_def]
    intro set _setOpen
    exact isOpen_discrete _
  simpa only [ObservationOpenInclusion, partitionTopology] using
    (continuous_refinement_observation_topology
      (coarse := coarse) (refined := fine) (projection := factor)
      factorization factorContinuous)

/-- On an inhabited source, inclusion of partition-open sets recovers the
underlying readout factorization. -/
theorem partition_open_inclusion_implies_refines
    {X Coarse Fine : Type*} [Nonempty X]
    (coarse : Concept X Coarse) (fine : Concept X Fine)
    (openInclusion : ObservationOpenInclusion (partitionTopology coarse)
      (partitionTopology fine)) :
    Refines coarse fine := by
  apply (target_recovery_criterion fine coarse).1.mpr
  intro x y sameFine
  by_contra differentCoarse
  let coarseFiber : Set X := coarse ⁻¹' {coarse x}
  have coarseFiberOpen : @IsOpen X (partitionTopology coarse) coarseFiber := by
    letI : TopologicalSpace Coarse := ⊥
    letI : DiscreteTopology Coarse := ⟨rfl⟩
    rw [partitionTopology, isOpen_induced_iff]
    exact ⟨{coarse x}, isOpen_discrete _, rfl⟩
  have fineFiberOpen : @IsOpen X (partitionTopology fine) coarseFiber :=
    openInclusion coarseFiber coarseFiberOpen
  have fineInseparable : @Inseparable X (partitionTopology fine) x y :=
    (partition_inseparable_iff_kernel fine x y).2 sameFine
  have xInFiber : x ∈ coarseFiber := by simp [coarseFiber]
  have yInFiber : y ∈ coarseFiber :=
    ((@Inseparable.mem_open_iff X (partitionTopology fine)
      x y coarseFiber fineInseparable fineFiberOpen).mp xInFiber)
  have sameCoarse : coarse y = coarse x := by
    simpa [coarseFiber] using yInFiber
  exact differentCoarse sameCoarse.symm

/-- Readout refinement is exactly inclusion of the corresponding partition
observation topologies. -/
theorem refines_iff_partition_open_inclusion
    {X Coarse Fine : Type*} [Nonempty X]
    (coarse : Concept X Coarse) (fine : Concept X Fine) :
    Refines coarse fine ↔
      ObservationOpenInclusion (partitionTopology coarse)
        (partitionTopology fine) := by
  constructor
  · exact refines_implies_partition_open_inclusion coarse fine
  · exact partition_open_inclusion_implies_refines coarse fine

/-- Finer readouts cannot create target defects that were absent from a coarser
readout. Defect sets are antitone in the information order. -/
theorem defectRelation_antitone_of_refines
    {X Coarse Fine Target : Type*}
    (coarse : Concept X Coarse) (fine : Concept X Fine)
    (target : Concept X Target) (refinement : Refines coarse fine) :
    defectRelation fine target ⊆ defectRelation coarse target := by
  rcases refinement with ⟨factor, factorization⟩
  rintro ⟨x, y⟩ ⟨sameFine, targetDifferent⟩
  refine ⟨?_, targetDifferent⟩
  rw [factorization]
  exact congrArg factor sameFine

/-- The same antitonicity law in topological separation-deficit form. -/
theorem separationDeficit_antitone_of_refines
    {X Coarse Fine Target : Type*}
    (coarse : Concept X Coarse) (fine : Concept X Fine)
    (target : Concept X Target) (refinement : Refines coarse fine) :
    separationDeficit fine target ⊆ separationDeficit coarse target := by
  rw [← defectRelation_eq_separationDeficit fine target,
    ← defectRelation_eq_separationDeficit coarse target]
  exact defectRelation_antitone_of_refines coarse fine target refinement

#print axioms refines_iff_partition_open_inclusion
#print axioms defectRelation_antitone_of_refines

end D5.S3.ConceptDynamics.ObservationTopology.ObservationOrderEquivalence
