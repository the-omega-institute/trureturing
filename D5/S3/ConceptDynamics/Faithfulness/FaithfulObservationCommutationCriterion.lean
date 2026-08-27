/- GID: D5/S3/ConceptDynamics/Faithfulness/FaithfulObservationCommutationCriterion
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Faithfulness/FaithfulObservationCommutationCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Joint faithfulness turns observed composite agreement into process commutation. -/

import D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion

/- Library-search audit trail (2026-08-27):
   * Name and body-shape searches found the canonical dependent `jointReadout`
     in `JointFaithfulnessLeibnizCriterion`; it is imported rather than redeclared.
   * Repository searches found no theorem concluding equality of two composite
     processes from coordinatewise equality under a jointly injective family.
   * Pinned Mathlib provides `Function.Injective` and function extensionality,
     but no exact theorem involving the repository-local dependent readout. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Faithfulness.FaithfulObservationCommutationCriterion

open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion

/-- If every coordinate gives the same reading after two opposite process
orders, a jointly faithful readout identifies the resulting states at every
input and hence identifies the two composite processes. -/
theorem faithful_observation_commutation_criterion
    {I X : Type*} {Output : I -> Type*}
    (readout : forall i, X -> Output i)
    (first second : X -> X)
    (faithful : Function.Injective (jointReadout readout))
    (visibleCommutation : forall i x,
      readout i (first (second x)) = readout i (second (first x))) :
    first ∘ second = second ∘ first := by
  funext x
  apply faithful
  funext i
  exact visibleCommutation i x

#print axioms faithful_observation_commutation_criterion

end D5.S3.ConceptDynamics.Faithfulness.FaithfulObservationCommutationCriterion
