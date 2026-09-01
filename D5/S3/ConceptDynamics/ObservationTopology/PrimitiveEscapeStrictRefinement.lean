/- GID: D5/S3/ConceptDynamics/ObservationTopology/PrimitiveEscapeStrictRefinement
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ObservationTopology/PrimitiveEscapeStrictRefinement
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Primitive escape is exactly strict refinement of family observation topology. -/

import D5.S3.ConceptDynamics.ObservationTopology.SemanticClosureTopologyInvariance
import D5.S3.ConceptDynamics.Topology.ContinuousRefinementObservationTopology

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.ObservationTopology.PrimitiveEscapeStrictRefinement
open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
open D5.S3.ConceptDynamics.DefinitionEscape.DefinitionKernelGalois
open D5.S3.ConceptDynamics.Epistemic.PartitionKnowledgeNegativeIntrospection
open D5.S3.ConceptDynamics.ObservationTopology.PartitionTopologyKernel
open D5.S3.ConceptDynamics.ObservationTopology.SemanticClosureTopologyInvariance
open D5.S3.ConceptDynamics.Topology.ContinuousRefinementObservationTopology

def StrictObservationRefinement {X : Type*}
    (coarse fine : TopologicalSpace X) : Prop :=
  (forall set, @IsOpen X coarse set -> @IsOpen X fine set) ∧
    exists set, @IsOpen X fine set ∧ ¬ @IsOpen X coarse set

def extendedFamilyReadout
    {X InputOutput Output : Type*} (Gamma : Set (Concept X InputOutput))
    (candidate : Concept X Output) :
    Concept X ((forall definition : Gamma, InputOutput) × Output) :=
  conceptJoin (jointReadout (fun definition : Gamma => definition.1)) candidate

theorem primitiveEscape_iff_strict_topology_refinement
    {X InputOutput Output : Type*} [Nonempty X]
    (Gamma : Set (Concept X InputOutput)) (candidate : Concept X Output) :
    PrimitiveEscape Gamma candidate <->
      StrictObservationRefinement
        (partitionTopology (jointReadout (fun definition : Gamma => definition.1)))
        (partitionTopology (extendedFamilyReadout Gamma candidate)) := by
  let oldReadout : Concept X (forall definition : Gamma, InputOutput) :=
    jointReadout (fun definition : Gamma => definition.1)
  let fineReadout : Concept X ((forall definition : Gamma, InputOutput) × Output) :=
    extendedFamilyReadout Gamma candidate
  have oldOpenInFine : forall set,
      @IsOpen X (partitionTopology oldReadout) set ->
        @IsOpen X (partitionTopology fineReadout) set := by
    letI : TopologicalSpace (forall definition : Gamma, InputOutput) := ⊥
    letI : DiscreteTopology (forall definition : Gamma, InputOutput) := ⟨rfl⟩
    letI : TopologicalSpace ((forall definition : Gamma, InputOutput) × Output) := ⊥
    letI : DiscreteTopology ((forall definition : Gamma, InputOutput) × Output) := ⟨rfl⟩
    have projectionContinuous :
        @Continuous ((forall definition : Gamma, InputOutput) × Output)
          (forall definition : Gamma, InputOutput) ⊥ ⊥ Prod.fst := by
      rw [continuous_def]
      intro set _
      exact isOpen_discrete _
    simpa only [oldReadout, fineReadout, partitionTopology,
      extendedFamilyReadout] using
      (continuous_refinement_observation_topology
        (coarse := oldReadout) (refined := fineReadout) (projection := Prod.fst)
        (factorization := by funext x; rfl) projectionContinuous)
  constructor
  · intro primitive
    rcases (not_mem_semanticClosure_iff_kernel_witness Gamma candidate).1 primitive with
      ⟨x, y, oldDefinitionsAgree, candidateDifferent⟩
    have oldAgree : oldReadout x = oldReadout y := by
      funext definition
      change definition.1 x = definition.1 y
      exact oldDefinitionsAgree definition
    let witnessOpen : Set X := {state | candidate state = candidate x}
    have witnessOpenFine : @IsOpen X (partitionTopology fineReadout) witnessOpen := by
      letI : TopologicalSpace ((forall definition : Gamma, InputOutput) × Output) := ⊥
      letI : DiscreteTopology ((forall definition : Gamma, InputOutput) × Output) := ⟨rfl⟩
      change @IsOpen X
        (TopologicalSpace.induced
          (show X -> ((forall definition : Gamma, InputOutput) × Output) from fineReadout) ⊥)
        witnessOpen
      rw [isOpen_induced_iff]
      refine ⟨{coordinate | coordinate.2 = candidate x}, isOpen_discrete _, ?_⟩
      ext state
      rfl
    have witnessNotOpenOld : ¬ @IsOpen X (partitionTopology oldReadout) witnessOpen := by
      intro witnessOpenOld
      have oldInseparable : @Inseparable X (partitionTopology oldReadout) x y :=
        (partition_inseparable_iff_kernel oldReadout x y).2 oldAgree
      have xInWitness : x ∈ witnessOpen := rfl
      have yInWitness : y ∈ witnessOpen :=
        ((@Inseparable.mem_open_iff X (partitionTopology oldReadout)
          x y witnessOpen oldInseparable witnessOpenOld).mp xInWitness)
      exact candidateDifferent yInWitness.symm
    exact ⟨oldOpenInFine, witnessOpen, witnessOpenFine, witnessNotOpenOld⟩
  · intro strict primitiveFailure
    have candidateFiberConstant :=
      (mem_semanticClosure_iff_fiber_constant Gamma candidate).1 primitiveFailure
    have sameTopology : partitionTopology fineReadout = partitionTopology oldReadout := by
      apply partitionTopology_eq_of_kernel_iff fineReadout oldReadout
      intro x y
      constructor
      · intro fineAgree
        exact congrArg Prod.fst fineAgree
      · intro oldAgree
        apply Prod.ext oldAgree
        apply candidateFiberConstant
        intro definition
        change definition.1 x = definition.1 y
        exact congrFun oldAgree definition
    rcases strict.2 with ⟨set, setOpenFine, setNotOpenOld⟩
    apply setNotOpenOld
    change @IsOpen X (partitionTopology oldReadout) set
    rw [← sameTopology]
    exact setOpenFine

theorem productiveSeparation_implies_strict_topology_refinement
    {X Current InputOutput Target Output : Type*} [Nonempty X]
    (Gamma : Set (Concept X InputOutput)) (current : Concept X Current)
    (target : Concept X Target) (candidate : Concept X Output)
    (productive : ProductiveSeparation Gamma current target candidate) :
    StrictObservationRefinement
      (partitionTopology (jointReadout (fun definition : Gamma => definition.1)))
      (partitionTopology (extendedFamilyReadout Gamma candidate)) :=
  (primitiveEscape_iff_strict_topology_refinement Gamma candidate).1
    (productiveSeparation_implies_primitiveEscape
      Gamma current target candidate productive)

#print axioms primitiveEscape_iff_strict_topology_refinement
#print axioms productiveSeparation_implies_strict_topology_refinement
end D5.S3.ConceptDynamics.ObservationTopology.PrimitiveEscapeStrictRefinement
