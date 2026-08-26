/- GID: D5/S3/ConceptDynamics/ObservationTopology/DiagonalTopologicalEscape
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ObservationTopology/DiagonalTopologicalEscape
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Complete relative diagonals force discontinuity and strict refinement. -/

import D5.S3.ConceptDynamics.DefinitionEscape.RelativeSemanticDiagonal
import D5.S3.ConceptDynamics.ObservationTopology.RedundantCoordinateTopology

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.ObservationTopology.DiagonalTopologicalEscape

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.TargetRisk.RefinementRiskCostTradeoff
open D5.S3.ConceptDynamics.DefinitionEscape.LatentAdequacyCriterion
open D5.S3.ConceptDynamics.DefinitionEscape.RelativeSemanticDiagonal
open D5.S3.ConceptDynamics.Epistemic.PartitionKnowledgeNegativeIntrospection
open D5.S3.ConceptDynamics.ObservationTopology.ResidualSeparationTopology
open D5.S3.ConceptDynamics.ObservationTopology.TargetContinuityFactorization
open D5.S3.ConceptDynamics.ObservationTopology.PrimitiveEscapeStrictRefinement
open D5.S3.ConceptDynamics.ObservationTopology.RedundantCoordinateTopology
open D5.S3.ConceptDynamics.Restoration.TargetRecoveryCriterion

/-- A complete decoder catalog produces a relative diagonal target that is not
continuous from the latent partition topology to its discrete output. -/
theorem complete_diagonal_not_continuous
    {Address Coordinate Output : Type*} [Nonempty Address]
    (twist : Output → Output)
    (latent : Concept Address Coordinate)
    (decoderCatalog : Address → Coordinate → Output)
    (fixedPointFree : ∀ output, twist output ≠ output)
    (complete : Function.Surjective decoderCatalog) :
    ¬ @Continuous Address Output (partitionTopology latent) ⊥
      (relativeSemanticDiagonal twist latent decoderCatalog) := by
  intro targetContinuous
  have factors :
      Refines (relativeSemanticDiagonal twist latent decoderCatalog) latent :=
    (target_factors_iff_continuous_partition latent
      (relativeSemanticDiagonal twist latent decoderCatalog)).2 targetContinuous
  exact
    (relative_semantic_diagonal_target_inadequate_of_surjective
      twist latent decoderCatalog fixedPointFree complete) factors

/-- The same diagonal has a concrete topological separation deficit in the old
observation topology. -/
theorem complete_diagonal_separationDeficit_nonempty
    {Address Coordinate Output : Type*} [Nonempty Address]
    (twist : Output → Output)
    (latent : Concept Address Coordinate)
    (decoderCatalog : Address → Coordinate → Output)
    (fixedPointFree : ∀ output, twist output ≠ output)
    (complete : Function.Surjective decoderCatalog) :
    (separationDeficit latent
      (relativeSemanticDiagonal twist latent decoderCatalog)).Nonempty := by
  have inadequate :
      ¬Refines (relativeSemanticDiagonal twist latent decoderCatalog) latent := by
    simpa only [TargetAdequate] using
      (relative_semantic_diagonal_target_inadequate_of_surjective
        twist latent decoderCatalog fixedPointFree complete)
  have defectNonempty :
      (defectRelation latent
        (relativeSemanticDiagonal twist latent decoderCatalog)).Nonempty :=
    (target_recovery_criterion latent
      (relativeSemanticDiagonal twist latent decoderCatalog)).2.2.2.mp inadequate
  rw [defectRelation_eq_separationDeficit] at defectNonempty
  exact defectNonempty

/-- Promoting the complete-catalog diagonal target to a new coordinate strictly
refines the latent observation topology. -/
theorem complete_diagonal_strict_topology_refinement
    {Address Coordinate Output : Type*} [Nonempty Address]
    (twist : Output → Output)
    (latent : Concept Address Coordinate)
    (decoderCatalog : Address → Coordinate → Output)
    (fixedPointFree : ∀ output, twist output ≠ output)
    (complete : Function.Surjective decoderCatalog) :
    StrictObservationRefinement (partitionTopology latent)
      (partitionTopology
        (conceptJoin latent
          (relativeSemanticDiagonal twist latent decoderCatalog))) := by
  apply (coordinate_inadequate_iff_strict_join_refinement latent
    (relativeSemanticDiagonal twist latent decoderCatalog)).1
  simpa only [TargetAdequate] using
    (relative_semantic_diagonal_target_inadequate_of_surjective
      twist latent decoderCatalog fixedPointFree complete)

/-- Complete relative diagonalization has four simultaneous settlements:
non-factorization, discontinuity, a nonempty separation deficit, and strict
observation-topology refinement after adjoining the target. -/
theorem complete_diagonal_topological_settlement
    {Address Coordinate Output : Type*} [Nonempty Address]
    (twist : Output → Output)
    (latent : Concept Address Coordinate)
    (decoderCatalog : Address → Coordinate → Output)
    (fixedPointFree : ∀ output, twist output ≠ output)
    (complete : Function.Surjective decoderCatalog) :
    (¬Refines (relativeSemanticDiagonal twist latent decoderCatalog) latent) ∧
    (¬ @Continuous Address Output (partitionTopology latent) ⊥
      (relativeSemanticDiagonal twist latent decoderCatalog)) ∧
    (separationDeficit latent
      (relativeSemanticDiagonal twist latent decoderCatalog)).Nonempty ∧
    StrictObservationRefinement (partitionTopology latent)
      (partitionTopology
        (conceptJoin latent
          (relativeSemanticDiagonal twist latent decoderCatalog))) := by
  refine ⟨?_, complete_diagonal_not_continuous twist latent decoderCatalog
    fixedPointFree complete, complete_diagonal_separationDeficit_nonempty
    twist latent decoderCatalog fixedPointFree complete,
    complete_diagonal_strict_topology_refinement twist latent decoderCatalog
      fixedPointFree complete⟩
  simpa only [TargetAdequate] using
    (relative_semantic_diagonal_target_inadequate_of_surjective
      twist latent decoderCatalog fixedPointFree complete)

#print axioms complete_diagonal_not_continuous
#print axioms complete_diagonal_topological_settlement

end D5.S3.ConceptDynamics.ObservationTopology.DiagonalTopologicalEscape
