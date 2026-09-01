/- GID: D5/S3/ConceptDynamics/DefinitionEscapeMonotonicity/SubfamilyReadoutRefinement
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DefinitionEscapeMonotonicity/SubfamilyReadoutRefinement
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Every dependent subfamily readout factors through the complete family readout. -/

import D5.S3.ConceptDynamics.ConceptJoinUniversal
import D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion

/- Library-search audit trail (2026-09-01):
   * Repository searches found `indexed_readout_monotonicity` for finite index
     sets and `restricting_sensor_family_enlarges_kernel` for a common output
     type. Neither covers an arbitrary set-indexed dependent family.
   * `full_family_inadequacy_persists_to_subfamilies` proves the downstream
     target-inadequacy consequence, but does not expose the readout refinement.
   * Pinned Mathlib provides `Function.FactorsThrough` and
     `Function.factorsThrough_iff`; no declaration packages this dependent
     coordinate restriction. Searches of the other pinned Lean packages found
     no matching readout-refinement theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DefinitionEscapeMonotonicity.SubfamilyReadoutRefinement

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion

universe u v w

/-- The complete dependent readout refines the readout of every selected
subfamily by coordinate restriction. -/
theorem subfamily_readout_refined_by_full_family
    {I : Type u} {X : Type v} {V : I -> Type w}
    (q : forall i, Concept X (V i)) (J : Set I) :
    Refines
      (jointReadout (fun member : J => q member.1))
      (jointReadout q) := by
  refine ⟨fun readings member => readings member.1, ?_⟩
  funext x member
  rfl

#print axioms subfamily_readout_refined_by_full_family

end D5.S3.ConceptDynamics.DefinitionEscapeMonotonicity.SubfamilyReadoutRefinement
