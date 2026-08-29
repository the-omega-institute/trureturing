/- GID: D5/S3/ConceptDynamics/DefinitionEscapeRegrade/SemanticSketchTargetLaunderingBridge
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DefinitionEscapeRegrade/SemanticSketchTargetLaunderingBridge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Exact temporal bridge relates sketch and body laundering. -/

import D5.S3.ConceptDynamics.DefinitionEscapeRegrade.SemanticTargetLaunderingBundleElimination

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

namespace D5.S3.ConceptDynamics.DefinitionEscape.Adjudication

open D5.S3.ConceptDynamics.Governance.TargetLaunderingCriterion

/- Library-search audit trail (2026-08-29):
   * Exact searches for the target equivalence and its defining symbols found
     no Mathlib declaration and no theorem in `D5/` with this conclusion.
   * The imported frozen 57.2-C module is the unique source of
     `RegradeSemantics`, `RegradeTemporalBridge`, and both laundering
     predicates. This module adds only the requested bridge theorem. -/

/-- Under the explicit temporal bridge, freeze-visible sketch laundering is
exactly body-level laundering together with the sketch's report timestamp. -/
theorem semantic_sketch_target_laundering_iff_body_and_timestamp
    {Commitment Evidence Verdict Time TargetChain Domain Epsilon Condition
      Comparator Baseline WeightSpec : Type u}
    {Report : Type v}
    [LT Time]
    (S :
      RegradeSemantics Commitment Evidence Verdict Time
        (ProtectedCoordinates TargetChain Domain Epsilon Condition Comparator
          Baseline WeightSpec)
        Report)
    (oldK newK : Commitment)
    (Z : Evidence)
    (regrade : SemanticRegrade S)
    (bridge : RegradeTemporalBridge S) :
    SemanticSketchTargetLaunderingAt S oldK newK Z regrade <->
      SemanticTargetLaunderingAt S oldK newK Z regrade /\
        S.reportOccurredAt regrade.report = S.freezeTime newK := by
  have temporal_iff :
      FreezeVisibleSemanticRegrade S regrade <->
        PostArrivalSemanticRegrade S regrade := by
    simpa only [FreezeVisibleSemanticRegrade, PostArrivalSemanticRegrade] using
      bridge.visibility_iff_arrival
        (S.reportRevised regrade.report) (S.reportEvidence regrade.report)
  constructor
  · rintro ⟨located, visible, occurred, attributed, changed⟩
    exact ⟨⟨located, temporal_iff.mp visible, attributed, changed⟩, occurred⟩
  · rintro ⟨⟨located, arrived, attributed, changed⟩, occurred⟩
    exact ⟨located, temporal_iff.mpr arrived, occurred, attributed, changed⟩

namespace SemanticSketchTargetLaunderingBridgeWitness

open SemanticTargetLaunderingFiniteWitness

example : Bool := false

example : RegradeTemporalBridge booleanSemantics where
  visibility_iff_arrival := by
    intro _ _
    change True <-> (0 : Nat) < 1
    decide

example :
    SemanticSketchTargetLaunderingAt
      booleanSemantics false true () regrade := by
  let bridge : RegradeTemporalBridge booleanSemantics := by
    constructor
    intro _ _
    change True <-> (0 : Nat) < 1
    decide
  rw [semantic_sketch_target_laundering_iff_body_and_timestamp
    booleanSemantics false true () regrade bridge]
  refine ⟨?_, rfl⟩
  rw [semantic_target_laundering_iff_protected_coordinates_ne]
  refine ⟨⟨rfl, rfl, rfl⟩, ?_, rfl, ?_⟩
  · change (0 : Nat) < 1
    decide
  · intro equalCoordinates
    have targetChainEq :=
      congrArg ProtectedCoordinates.targetChain equalCoordinates
    exact Bool.false_ne_true targetChainEq

end SemanticSketchTargetLaunderingBridgeWitness

#print axioms semantic_sketch_target_laundering_iff_body_and_timestamp

end D5.S3.ConceptDynamics.DefinitionEscape.Adjudication
