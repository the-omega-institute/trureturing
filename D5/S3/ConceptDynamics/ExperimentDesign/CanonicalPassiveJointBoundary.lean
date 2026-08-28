/- GID: D5/S3/ConceptDynamics/ExperimentDesign/CanonicalPassiveJointBoundary
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ExperimentDesign/CanonicalPassiveJointBoundary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Adaptivity lowers cost without crossing the canonical passive joint boundary. -/

import D5.S3.ConceptDynamics.ExperimentBoundary.PassiveJointBoundaryObstruction

/- Library-search audit trail (2026-08-26):
   * Exact frozen family hit `adaptive_cost_reduction_and_passive_boundary`
     states the complete source claim and is applied directly.
   * Body-shape searches hit the canonical `jointReadout`, `PassiveProtocol`,
     and `runPassiveProtocol` family primitives; none is redeclared here.
   * Pinned Mathlib has no declaration for this repository-specific protocol
     family or its combined cost and passive-boundary conclusion. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.ExperimentDesign.CanonicalPassiveJointBoundary

open D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification
open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound
open D5.S3.ConceptDynamics.ExperimentBoundary.PassiveJointBoundaryObstruction
open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion

universe u v w z

/-- Adaptivity has a strict cost witness, but a target outside the complete
passive joint readout remains outside every transcript of a deterministic
adaptive protocol using that same family. Crossing the boundary requires
leaving the fixed experiments, object, intervention behavior, observation
carrier, or admitted domain. -/
theorem canonical_adaptive_cost_reduction_and_passive_boundary
    {Experiment : Type u} {Response : Experiment -> Type v}
    {State : Type w} {Target : Type z}
    (readout : forall experiment, State -> Response experiment)
    (target : Concept State Target)
    (notRefines : ¬Refines target (jointReadout readout)) :
    residueAdaptiveDepth < residueStaticDepth ∧
      ¬ ∃ protocol : PassiveProtocol Experiment Response,
        Refines target (runPassiveProtocol readout protocol) := by
  exact adaptive_cost_reduction_and_passive_boundary readout target notRefines

#print axioms canonical_adaptive_cost_reduction_and_passive_boundary

end D5.S3.ConceptDynamics.ExperimentDesign.CanonicalPassiveJointBoundary
