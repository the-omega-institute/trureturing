/- GID: D5/S3/ConceptDynamics/DefinitionEscapeRegrade/SemanticTargetLaunderingDecision
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DefinitionEscapeRegrade/SemanticTargetLaunderingDecision
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Exact laundering decisions for existing regrade carriers. -/

import D5.S3.ConceptDynamics.DefinitionEscapeRegrade.SemanticTargetLaunderingBundleElimination

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

namespace D5.S3.ConceptDynamics.DefinitionEscape.Adjudication

open D5.S3.ConceptDynamics.Governance.TargetLaunderingCriterion

/- Library-search audit trail (2026-08-29):
   * Exact searches in `origin/dev`, `D5`, and `Blueprint` found no declaration
     of `prospectiveRegradeSemantics` or a theorem constructing
     `TargetLaunderingDecision`.
   * The standard interpreter below transcribes DECT 57.2.5 and directly uses
     the frozen `ProspectiveCommitment`, `protectedCoordinates`, and
     `RegradeReport` carriers instead of declaring replacement records.
   * The decision proof imports the frozen 57.2-C characterization and its
     transitive 57.2-A extensionality dependency. It adds no laundering
     criterion and assumes no verdict equality decision. -/

/-- The standard semantic interpreter for the existing prospective-commitment
and regrade-report carriers. -/
def prospectiveRegradeSemantics
    {EventId Evidence Round Artifact Time TargetChain Domain Epsilon Condition
      Comparator TestPlan Baseline WeightSpec Verdict : Type u}
    [LinearOrder EventId]
    [Preorder Time]
    [DecidableEq Artifact]
    {n : Round}
    (arrival : Evidence -> Time)
    (evaluate :
      ProspectiveCommitment EventId Evidence Round Artifact Time TargetChain
        Domain Epsilon Condition Comparator TestPlan Baseline WeightSpec n ->
      Evidence -> Verdict) :
    RegradeSemantics
      (ProspectiveCommitment EventId Evidence Round Artifact Time TargetChain
        Domain Epsilon Condition Comparator TestPlan Baseline WeightSpec n)
      Evidence
      Verdict
      Time
      (ProtectedCoordinates TargetChain Domain Epsilon Condition Comparator
        Baseline WeightSpec)
      (RegradeReport
        (ProspectiveCommitment EventId Evidence Round Artifact Time TargetChain
          Domain Epsilon Condition Comparator TestPlan Baseline WeightSpec n)
        Evidence Verdict Time evaluate) where
  «protected» := protectedCoordinates
  evaluate := evaluate
  arrival := arrival
  freezeTime := fun K => K.adjudication.frozenAt
  visibleAtFreeze := fun K Z =>
    Z ∈ K.adjudication.filtration.seen K.adjudication.freezeEvent
  reportOriginal := fun report => report.original
  reportRevised := fun report => report.revised
  reportEvidence := fun report => report.evidence
  reportVerdict := fun report => report.regradedVerdict
  reportAttributedTo := fun report => report.attributedTo
  reportOccurredAt := fun report => report.occurredAt
  reportVerdictCorrect := fun report => report.regradesOldRound

set_option linter.unusedDecidableInType false in
/-- Decidable commitment, evidence, protected-coordinate equalities, and strict
time comparison suffice to construct a certified laundering decision. -/
theorem target_laundering_decision_nonempty
    {Commitment Evidence Verdict Time TargetChain Domain Epsilon Condition
      Comparator Baseline WeightSpec : Type u}
    {Report : Type v}
    [LT Time]
    [DecidableEq Commitment]
    [DecidableEq Evidence]
    [DecidableEq TargetChain]
    [DecidableEq Domain]
    [DecidableEq Epsilon]
    [DecidableEq Condition]
    [DecidableEq Comparator]
    [DecidableEq Baseline]
    [DecidableEq WeightSpec]
    [DecidableRel (fun a b : Time => a < b)]
    (S :
      RegradeSemantics Commitment Evidence Verdict Time
        (ProtectedCoordinates TargetChain Domain Epsilon Condition Comparator
          Baseline WeightSpec)
        Report)
    (oldK newK : Commitment)
    (Z : Evidence)
    (regrade : SemanticRegrade S) :
    Nonempty (TargetLaunderingDecision S oldK newK Z regrade) := by
  letI :
      DecidableEq
        (ProtectedCoordinates TargetChain Domain Epsilon Condition Comparator
          Baseline WeightSpec) := fun oldCoordinates newCoordinates =>
    if hTargetChain :
        oldCoordinates.targetChain = newCoordinates.targetChain then
      if hDomain : oldCoordinates.domain = newCoordinates.domain then
        if hEpsilon : oldCoordinates.epsilon = newCoordinates.epsilon then
          if hConditions :
              oldCoordinates.conditions = newCoordinates.conditions then
            if hComparator :
                oldCoordinates.comparator = newCoordinates.comparator then
              if hBaseline :
                  oldCoordinates.baseline = newCoordinates.baseline then
                if hWeightSpec :
                    oldCoordinates.weightSpec = newCoordinates.weightSpec then
                  isTrue <|
                    (protected_coordinate_dependent_extensionality
                      oldCoordinates newCoordinates).mpr (by
                        intro tag
                        cases tag <;> assumption)
                else
                  isFalse (fun hCoordinates =>
                    hWeightSpec (congrArg
                      ProtectedCoordinates.weightSpec hCoordinates))
              else
                isFalse (fun hCoordinates =>
                  hBaseline (congrArg
                    ProtectedCoordinates.baseline hCoordinates))
            else
              isFalse (fun hCoordinates =>
                hComparator (congrArg
                  ProtectedCoordinates.comparator hCoordinates))
          else
            isFalse (fun hCoordinates =>
              hConditions (congrArg
                ProtectedCoordinates.conditions hCoordinates))
        else
          isFalse (fun hCoordinates =>
            hEpsilon (congrArg ProtectedCoordinates.epsilon hCoordinates))
      else
        isFalse (fun hCoordinates =>
          hDomain (congrArg ProtectedCoordinates.domain hCoordinates))
    else
      isFalse (fun hCoordinates =>
        hTargetChain (congrArg
          ProtectedCoordinates.targetChain hCoordinates))
  letI : Decidable (SemanticTargetLaunderingAt S oldK newK Z regrade) := by
    rw [semantic_target_laundering_iff_protected_coordinates_ne]
    unfold SemanticRegradeAt PostArrivalSemanticRegrade
    infer_instance
  exact ⟨{
    verdict := decide (SemanticTargetLaunderingAt S oldK newK Z regrade)
    correct := by simp }⟩

set_option linter.unusedDecidableInType false in
/-- The general decision theorem applies directly through the standard
interpreter to the existing prospective-commitment and report carriers. -/
theorem prospective_target_laundering_decision_nonempty
    {EventId Evidence Round Artifact Time TargetChain Domain Epsilon Condition
      Comparator TestPlan Baseline WeightSpec Verdict : Type u}
    [LinearOrder EventId]
    [Preorder Time]
    [DecidableEq Artifact]
    {n : Round}
    [DecidableEq
      (ProspectiveCommitment EventId Evidence Round Artifact Time TargetChain
        Domain Epsilon Condition Comparator TestPlan Baseline WeightSpec n)]
    [DecidableEq Evidence]
    [DecidableEq TargetChain]
    [DecidableEq Domain]
    [DecidableEq Epsilon]
    [DecidableEq Condition]
    [DecidableEq Comparator]
    [DecidableEq Baseline]
    [DecidableEq WeightSpec]
    [DecidableRel (fun a b : Time => a < b)]
    (arrival : Evidence -> Time)
    (evaluate :
      ProspectiveCommitment EventId Evidence Round Artifact Time TargetChain
        Domain Epsilon Condition Comparator TestPlan Baseline WeightSpec n ->
      Evidence -> Verdict)
    (oldK newK :
      ProspectiveCommitment EventId Evidence Round Artifact Time TargetChain
        Domain Epsilon Condition Comparator TestPlan Baseline WeightSpec n)
    (Z : Evidence)
    (regrade :
      SemanticRegrade (prospectiveRegradeSemantics arrival evaluate)) :
    Nonempty
      (TargetLaunderingDecision
        (prospectiveRegradeSemantics arrival evaluate)
        oldK newK Z regrade) :=
  target_laundering_decision_nonempty
    (prospectiveRegradeSemantics arrival evaluate)
    oldK newK Z regrade

namespace SemanticTargetLaunderingDecisionFiniteWitness

open SemanticTargetLaunderingFiniteWitness

example :
    Nonempty
      (TargetLaunderingDecision
        booleanSemantics false true () regrade) :=
  target_laundering_decision_nonempty
    booleanSemantics false true () regrade

end SemanticTargetLaunderingDecisionFiniteWitness

#print axioms target_laundering_decision_nonempty
#print axioms prospective_target_laundering_decision_nonempty

end D5.S3.ConceptDynamics.DefinitionEscape.Adjudication
