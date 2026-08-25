/- GID: D5/S3/ConceptDynamics/ObservationTopology/SemanticClosureTopologyInvariance
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ObservationTopology/SemanticClosureTopologyInvariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Semantic closure adds recoverable readouts without changing family observation topology. -/

import D5.S3.ConceptDynamics.ObservationTopology.PartitionTopologyKernel
import D5.S3.ConceptDynamics.DefinitionEscape.DefinitionKernelGalois

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.ObservationTopology.SemanticClosureTopologyInvariance
open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
open D5.S3.ConceptDynamics.DefinitionEscape.DefinitionKernelGalois
open D5.S3.ConceptDynamics.Epistemic.PartitionKnowledgeNegativeIntrospection
open D5.S3.ConceptDynamics.ObservationTopology.PartitionTopologyKernel

def familyReadout {X Output : Type*} (Gamma : Set (Concept X Output)) :
    Concept X (forall definition : Gamma, Output) :=
  jointReadout (fun definition : Gamma => definition.1)

theorem partitionTopology_definitionClosure_eq
    {X Output : Type*} (Gamma : Set (Concept X Output)) :
    partitionTopology (familyReadout (DefinitionClosure Gamma)) =
      partitionTopology (familyReadout Gamma) := by
  apply partitionTopology_eq_of_kernel_iff
    (familyReadout (DefinitionClosure Gamma)) (familyReadout Gamma)
  intro x y
  have kernelEquality := jointKernel_definitionClosure Gamma
  constructor
  · intro closedReadoutEqual
    have pairInClosedKernel :
        (x, y) ∈ jointKernel
          (fun definition : DefinitionClosure Gamma => definition.1) := by
      apply Set.mem_iInter.2
      intro definition
      exact congrFun closedReadoutEqual definition
    have pairInOldKernel :
        (x, y) ∈ jointKernel (fun definition : Gamma => definition.1) := by
      rw [← kernelEquality]
      exact pairInClosedKernel
    funext definition
    exact Set.mem_iInter.1 pairInOldKernel definition
  · intro oldReadoutEqual
    have pairInOldKernel :
        (x, y) ∈ jointKernel (fun definition : Gamma => definition.1) := by
      apply Set.mem_iInter.2
      intro definition
      exact congrFun oldReadoutEqual definition
    have pairInClosedKernel :
        (x, y) ∈ jointKernel
          (fun definition : DefinitionClosure Gamma => definition.1) := by
      rw [kernelEquality]
      exact pairInOldKernel
    funext definition
    exact Set.mem_iInter.1 pairInClosedKernel definition

theorem partitionTopology_definitionClosure_idempotent
    {X Output : Type*} (Gamma : Set (Concept X Output)) :
    partitionTopology
        (familyReadout (DefinitionClosure (DefinitionClosure Gamma))) =
      partitionTopology (familyReadout Gamma) := by
  calc
    partitionTopology
        (familyReadout (DefinitionClosure (DefinitionClosure Gamma))) =
      partitionTopology (familyReadout (DefinitionClosure Gamma)) :=
        partitionTopology_definitionClosure_eq (DefinitionClosure Gamma)
    _ = partitionTopology (familyReadout Gamma) :=
        partitionTopology_definitionClosure_eq Gamma

#print axioms partitionTopology_definitionClosure_eq
end D5.S3.ConceptDynamics.ObservationTopology.SemanticClosureTopologyInvariance
