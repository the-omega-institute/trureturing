/- GID: D5/S3/ConceptDynamics/DefinitionEscapeRegrade/SemanticTargetLaunderingBundleElimination
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DefinitionEscapeRegrade/SemanticTargetLaunderingBundleElimination
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Body-level semantic target laundering eliminates its coordinate witness bundle. -/

import D5.S3.ConceptDynamics.DefinitionEscapeRegrade.CoordinateWitnessBundle

/- Library-search audit trail (2026-08-29):
   * Exact searches in `origin/dev`, `D5`, and `Blueprint` found no declaration
     of `RegradeSemantics`, `SemanticRegrade`, `SemanticTargetLaunderingAt`, or
     the target bundle-elimination equivalence.
   * The semantic carriers and predicates below transcribe the definition
     skeletons from DECT 57.2.3--57.2.4. They interpret the frozen
     `ProtectedCoordinates` carrier and do not copy any of its seven fields.
   * The only proof dependency is the frozen 57.2-B theorem
     `has_closed_coordinate_witness_bundle_iff_ne`; no new Mathlib lemma or
     target-laundering criterion is proved here. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

namespace D5.S3.ConceptDynamics.DefinitionEscape.Adjudication

open D5.S3.ConceptDynamics.Governance.TargetLaunderingCriterion

/-- An interpreter for protected coordinates, evaluation, evidence timing, and
the fields of an existing regrade-report carrier. -/
structure RegradeSemantics
    (Commitment Evidence Verdict Time Coordinate : Type u)
    (Report : Type v) where
  «protected» : Commitment -> Coordinate
  evaluate : Commitment -> Evidence -> Verdict
  arrival : Evidence -> Time
  freezeTime : Commitment -> Time
  visibleAtFreeze : Commitment -> Evidence -> Prop
  reportOriginal : Report -> Commitment
  reportRevised : Report -> Commitment
  reportEvidence : Report -> Evidence
  reportVerdict : Report -> Verdict
  reportAttributedTo : Report -> Commitment
  reportOccurredAt : Report -> Time
  reportVerdictCorrect :
    forall report,
      reportVerdict report =
        evaluate (reportRevised report) (reportEvidence report)

/-- A regrade report together with the actual original evaluation of the same
evidence. -/
structure SemanticRegrade
    {Commitment Evidence Verdict Time Coordinate : Type u}
    {Report : Type v}
    (S : RegradeSemantics Commitment Evidence Verdict Time Coordinate Report)
    where
  report : Report
  originalVerdict : Verdict
  originalVerdictCorrect :
    originalVerdict =
      S.evaluate (S.reportOriginal report) (S.reportEvidence report)

/-- The report identifies the supplied original commitment, revised
commitment, and evidence. -/
def SemanticRegradeAt
    {Commitment Evidence Verdict Time Coordinate : Type u}
    {Report : Type v}
    {S : RegradeSemantics Commitment Evidence Verdict Time Coordinate Report}
    (regrade : SemanticRegrade S)
    (oldK newK : Commitment)
    (Z : Evidence) : Prop :=
  S.reportOriginal regrade.report = oldK /\
    S.reportRevised regrade.report = newK /\
    S.reportEvidence regrade.report = Z

/-- The regraded evidence arrived strictly before the revised commitment was
frozen. -/
def PostArrivalSemanticRegrade
    {Commitment Evidence Verdict Time Coordinate : Type u}
    {Report : Type v}
    [LT Time]
    (S : RegradeSemantics Commitment Evidence Verdict Time Coordinate Report)
    (regrade : SemanticRegrade S) : Prop :=
  S.arrival (S.reportEvidence regrade.report) <
    S.freezeTime (S.reportRevised regrade.report)

/-- The regraded evidence is visible at the revised commitment's freeze. -/
def FreezeVisibleSemanticRegrade
    {Commitment Evidence Verdict Time Coordinate : Type u}
    {Report : Type v}
    (S : RegradeSemantics Commitment Evidence Verdict Time Coordinate Report)
    (regrade : SemanticRegrade S) : Prop :=
  S.visibleAtFreeze
    (S.reportRevised regrade.report)
    (S.reportEvidence regrade.report)

/-- The explicit bridge between freeze visibility and strict arrival time. -/
structure RegradeTemporalBridge
    {Commitment Evidence Verdict Time Coordinate : Type u}
    {Report : Type v}
    [LT Time]
    (S : RegradeSemantics Commitment Evidence Verdict Time Coordinate Report) :
    Prop where
  visibility_iff_arrival :
    forall K Z,
      S.visibleAtFreeze K Z <-> S.arrival Z < S.freezeTime K

/-- Body-level laundering combines report identity, strict arrival, original
attribution, and a closed nonempty witness bundle for protected change. -/
def SemanticTargetLaunderingAt
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
    (regrade : SemanticRegrade S) : Prop :=
  SemanticRegradeAt regrade oldK newK Z /\
    PostArrivalSemanticRegrade S regrade /\
    S.reportAttributedTo regrade.report = oldK /\
    HasClosedCoordinateWitnessBundle
      (S.«protected» oldK) (S.«protected» newK)

/-- The freeze-visible sketch additionally fixes the report timestamp to the
revised commitment's freeze time. -/
def SemanticSketchTargetLaunderingAt
    {Commitment Evidence Verdict Time TargetChain Domain Epsilon Condition
      Comparator Baseline WeightSpec : Type u}
    {Report : Type v}
    (S :
      RegradeSemantics Commitment Evidence Verdict Time
        (ProtectedCoordinates TargetChain Domain Epsilon Condition Comparator
          Baseline WeightSpec)
        Report)
    (oldK newK : Commitment)
    (Z : Evidence)
    (regrade : SemanticRegrade S) : Prop :=
  SemanticRegradeAt regrade oldK newK Z /\
    FreezeVisibleSemanticRegrade S regrade /\
    S.reportOccurredAt regrade.report = S.freezeTime newK /\
    S.reportAttributedTo regrade.report = oldK /\
    HasClosedCoordinateWitnessBundle
      (S.«protected» oldK) (S.«protected» newK)

/-- A Boolean laundering decision carrying a proof of its exact meaning. -/
structure TargetLaunderingDecision
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
    (regrade : SemanticRegrade S) where
  verdict : Bool
  correct :
    verdict = true <->
      SemanticTargetLaunderingAt S oldK newK Z regrade

set_option linter.unusedDecidableInType false in
/-- Body-level semantic target laundering is equivalent to report identity,
strict arrival, original attribution, and inequality of protected coordinates. -/
theorem semantic_target_laundering_iff_protected_coordinates_ne
    {Commitment Evidence Verdict Time TargetChain Domain Epsilon Condition
      Comparator Baseline WeightSpec : Type u}
    {Report : Type v}
    [LT Time]
    [DecidableEq TargetChain]
    [DecidableEq Domain]
    [DecidableEq Epsilon]
    [DecidableEq Condition]
    [DecidableEq Comparator]
    [DecidableEq Baseline]
    [DecidableEq WeightSpec]
    (S :
      RegradeSemantics Commitment Evidence Verdict Time
        (ProtectedCoordinates TargetChain Domain Epsilon Condition Comparator
          Baseline WeightSpec)
        Report)
    (oldK newK : Commitment)
    (Z : Evidence)
    (regrade : SemanticRegrade S) :
    SemanticTargetLaunderingAt S oldK newK Z regrade <->
      SemanticRegradeAt regrade oldK newK Z /\
        PostArrivalSemanticRegrade S regrade /\
        S.reportAttributedTo regrade.report = oldK /\
        S.«protected» oldK ≠ S.«protected» newK := by
  simp only [SemanticTargetLaunderingAt,
    has_closed_coordinate_witness_bundle_iff_ne]

namespace SemanticTargetLaunderingFiniteWitness

abbrev BooleanCoordinates :=
  ProtectedCoordinates Bool Bool Bool Bool Bool Bool Bool

def coordinates (commitment : Bool) : BooleanCoordinates where
  targetChain := commitment
  domain := false
  epsilon := false
  conditions := false
  comparator := false
  baseline := false
  weightSpec := false

def booleanSemantics :
    RegradeSemantics Bool Unit Unit Nat BooleanCoordinates Unit where
  «protected» := coordinates
  evaluate := fun _ _ => ()
  arrival := fun _ => 0
  freezeTime := fun _ => 1
  visibleAtFreeze := fun _ _ => True
  reportOriginal := fun _ => false
  reportRevised := fun _ => true
  reportEvidence := fun _ => ()
  reportVerdict := fun _ => ()
  reportAttributedTo := fun _ => false
  reportOccurredAt := fun _ => 1
  reportVerdictCorrect := by
    intro report
    cases report
    rfl

def regrade : SemanticRegrade booleanSemantics where
  report := ()
  originalVerdict := ()
  originalVerdictCorrect := rfl

example : Bool := false

example : coordinates false ≠ coordinates true := by
  intro equalCoordinates
  have targetChainEq :=
    congrArg ProtectedCoordinates.targetChain equalCoordinates
  exact Bool.false_ne_true targetChainEq

example :
    SemanticTargetLaunderingAt
      booleanSemantics false true () regrade := by
  rw [semantic_target_laundering_iff_protected_coordinates_ne]
  refine ⟨?_, ?_, rfl, ?_⟩
  · exact ⟨rfl, rfl, rfl⟩
  · change (0 : Nat) < 1
    decide
  · intro equalCoordinates
    have targetChainEq :=
      congrArg ProtectedCoordinates.targetChain equalCoordinates
    exact Bool.false_ne_true targetChainEq

end SemanticTargetLaunderingFiniteWitness

#print axioms semantic_target_laundering_iff_protected_coordinates_ne

end D5.S3.ConceptDynamics.DefinitionEscape.Adjudication
