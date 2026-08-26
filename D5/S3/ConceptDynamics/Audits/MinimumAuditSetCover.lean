/- GID: D5/S3/ConceptDynamics/Audits/MinimumAuditSetCover
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Audits/MinimumAuditSetCover
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Minimum target-complete audit suites are minimum defect set covers. -/

import D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
import D5.S3.ConceptDynamics.TargetRisk.RefinementRiskCostTradeoff

/- Library-search audit trail (2026-08-27):
   * Exact family primitives `jointReadout` and `defectRelation` construct the
     selected audit channel and the target-relative defect carrier.
   * `FiniteExperimentCoverCriterion.finite_experiment_cover_criterion` gives
     the corresponding finite-state unordered-pair feasibility equivalence.
     `MinimumCompleteObserverSetCover.minimum_complete_observer_is_set_cover`
     and `MinimumCompleteSetCover.minimum_complete_budget_iff_minimum_cover`
     optimize over the full distinct-pair carrier rather than `defectRelation`.
   * Searches for target-relative minimum audit cardinality and the displayed
     union-of-test-covers shape found no exact D5 or pinned-Mathlib theorem.
     No new definition or abbreviation is introduced. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.ConceptDynamics.Audits.MinimumAuditSetCover

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
open D5.S3.ConceptDynamics.TargetRisk.RefinementRiskCostTradeoff

universe u v w z

/-- A finite suite is cardinality-minimal among target-complete audit suites
exactly when it is cardinality-minimal among covers of the canonical defect
relation by the suites' test-separation sets. -/
theorem minimum_audit_set_is_set_cover
    {X : Type u} {Current : Type v} {Target : Type w}
    {Test : Type z} {Response : Test -> Type*}
    (current : Concept X Current) (target : Concept X Target)
    (test : (audit : Test) -> Concept X (Response audit))
    (selected : Finset Test) :
    let complete : Finset Test -> Prop := fun suite =>
      forall x y,
        (current x,
            jointReadout
              (fun audit : {candidate // candidate ∈ suite} =>
                test audit.1) x) =
          (current y,
            jointReadout
              (fun audit : {candidate // candidate ∈ suite} =>
                test audit.1) y) ->
        target x = target y
    let covers : Finset Test -> Prop := fun suite =>
      (⋃ audit : {candidate // candidate ∈ suite},
          defectRelation current target ∩
            {pair | test audit.1 pair.1 ≠ test audit.1 pair.2}) =
        defectRelation current target
    (complete selected ∧
        forall candidate, complete candidate ->
          selected.card ≤ candidate.card) ↔
      (covers selected ∧
        forall candidate, covers candidate ->
          selected.card ≤ candidate.card) := by
  classical
  dsimp only
  have coverCriterion (suite : Finset Test) :
      (forall x y,
          (current x,
              jointReadout
                (fun audit : {candidate // candidate ∈ suite} =>
                  test audit.1) x) =
            (current y,
              jointReadout
                (fun audit : {candidate // candidate ∈ suite} =>
                  test audit.1) y) ->
          target x = target y) ↔
        (⋃ audit : {candidate // candidate ∈ suite},
            defectRelation current target ∩
              {pair | test audit.1 pair.1 ≠ test audit.1 pair.2}) =
          defectRelation current target := by
    constructor
    · intro identifies
      apply Set.Subset.antisymm
      · intro pair covered
        obtain ⟨audit, pairDefect, _separated⟩ := Set.mem_iUnion.mp covered
        exact pairDefect
      · intro pair pairDefect
        apply Set.mem_iUnion.mpr
        by_contra notCovered
        have allSame :
            forall audit : {candidate // candidate ∈ suite},
              test audit.1 pair.1 = test audit.1 pair.2 := by
          intro audit
          by_contra separated
          apply notCovered
          exact ⟨audit, pairDefect, separated⟩
        have sameEvidence :
            (current pair.1,
                jointReadout
                  (fun audit : {candidate // candidate ∈ suite} =>
                    test audit.1) pair.1) =
              (current pair.2,
                jointReadout
                  (fun audit : {candidate // candidate ∈ suite} =>
                    test audit.1) pair.2) := by
          apply Prod.ext pairDefect.1
          funext audit
          exact allSame audit
        exact pairDefect.2
          (identifies pair.1 pair.2 sameEvidence)
    · intro covers x y sameEvidence
      by_contra targetDifferent
      have pairDefect : (x, y) ∈ defectRelation current target :=
        ⟨congrArg Prod.fst sameEvidence, targetDifferent⟩
      have covered :
          (x, y) ∈ ⋃ audit : {candidate // candidate ∈ suite},
            defectRelation current target ∩
              {pair | test audit.1 pair.1 ≠ test audit.1 pair.2} := by
        rw [covers]
        exact pairDefect
      obtain ⟨audit, _pairDefect, separated⟩ := Set.mem_iUnion.mp covered
      exact separated (congrFun (congrArg Prod.snd sameEvidence) audit)
  constructor
  · rintro ⟨completeSelected, minimumComplete⟩
    refine ⟨(coverCriterion selected).mp completeSelected, ?_⟩
    intro candidate coversCandidate
    exact minimumComplete candidate
      ((coverCriterion candidate).mpr coversCandidate)
  · rintro ⟨coversSelected, minimumCover⟩
    refine ⟨(coverCriterion selected).mpr coversSelected, ?_⟩
    intro candidate completeCandidate
    exact minimumCover candidate
      ((coverCriterion candidate).mp completeCandidate)

#print axioms minimum_audit_set_is_set_cover

end D5.S3.ConceptDynamics.Audits.MinimumAuditSetCover
