/- GID: D5/S3/ConceptDynamics/Evidence/ActualEvidenceRefinementStability
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Evidence/ActualEvidenceRefinementStability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Actual refinement preserves stable truth and falsity and can resolve uncertainty. -/

import D5.S3.ConceptDynamics.ConceptJoinUniversal
import D5.S3.ConceptDynamics.Epistemic.RobustKnowledgeRefinementMonotonicity

/- Library-search audit trail (2026-08-25):
   * Exact family hits `Refines`, `conceptJoin`, `robustKnowledge`, and
     `robust_knowledge_monotone_under_refinement` provide the source refinement
     order, the canonical paired readout, and stable-truth monotonicity. They are
     imported rather than redeclared.
   * Applying the same monotonicity theorem to the pointwise negation of the
     predicate gives the stable-false clause on the identical source carrier.
   * `EvidenceFourPhaseLaw` is adjacent but assumes a finite fiber and decidable
     predicate, while this atom has neither restriction. `VacuousOmniscience`
     supplies an adjacent empty-fiber warning but not this actual-anchor theorem.
   * Body-shape searches for admissible evidence fibers, anchored refinement,
     and true/false/undecided refinement outcomes found no exact combined theorem
     in the repository or pinned Mathlib. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Evidence.ActualEvidenceRefinementStability

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.Epistemic.RobustKnowledgeConjunction
open D5.S3.ConceptDynamics.Epistemic.RobustKnowledgeRefinementMonotonicity

/-- An admissible actual anchor witnesses both its coarse and refined fibers.
Stable truth and stable falsity on the coarse fiber persist on the refined one.
Moreover, two conflicting witnesses in one coarse fiber canonically generate a
stably true refinement, a stably false refinement, and an undecided refinement. -/
theorem actual_evidence_refinement_stability
    {X B B' : Type*} (admissible : X -> Prop)
    (coarseEvidence : Concept X B) (refinedEvidence : Concept X B')
    (predicate : X -> Prop) (anchor : X)
    (anchorAdmissible : admissible anchor)
    (refinement : Refines coarseEvidence refinedEvidence) :
    (∃ state, admissible state ∧
      coarseEvidence state = coarseEvidence anchor) ∧
    (∃ state, admissible state ∧
      refinedEvidence state = refinedEvidence anchor) ∧
    ((∀ state, admissible state ∧
        coarseEvidence state = coarseEvidence anchor -> predicate state) ->
      ∀ state, admissible state ∧
        refinedEvidence state = refinedEvidence anchor -> predicate state) ∧
    ((∀ state, admissible state ∧
        coarseEvidence state = coarseEvidence anchor -> ¬predicate state) ->
      ∀ state, admissible state ∧
        refinedEvidence state = refinedEvidence anchor -> ¬predicate state) ∧
    ∀ trueWitness falseWitness,
      admissible trueWitness -> admissible falseWitness ->
      coarseEvidence trueWitness = coarseEvidence falseWitness ->
      predicate trueWitness -> ¬predicate falseWitness ->
      let trueRefinement :=
        conceptJoin coarseEvidence (fun state => state = trueWitness)
      let falseRefinement :=
        conceptJoin coarseEvidence (fun state => state = falseWitness)
      let unresolvedRefinement :=
        conceptJoin coarseEvidence (fun _ => True)
      ((∃ state, admissible state ∧
          trueRefinement state = trueRefinement trueWitness) ∧
        ∀ state, admissible state ∧
          trueRefinement state = trueRefinement trueWitness -> predicate state) ∧
      ((∃ state, admissible state ∧
          falseRefinement state = falseRefinement falseWitness) ∧
        ∀ state, admissible state ∧
          falseRefinement state = falseRefinement falseWitness -> ¬predicate state) ∧
      ∃ trueState falseState,
        admissible trueState ∧
        unresolvedRefinement trueState = unresolvedRefinement trueWitness ∧
        admissible falseState ∧
        unresolvedRefinement falseState = unresolvedRefinement trueWitness ∧
        predicate trueState ∧ ¬predicate falseState := by
  have stableTrue :
      (∀ state, admissible state ∧
          coarseEvidence state = coarseEvidence anchor -> predicate state) ->
        ∀ state, admissible state ∧
          refinedEvidence state = refinedEvidence anchor -> predicate state := by
    intro coarseStable
    have coarseKnowledge :
        robustKnowledge admissible coarseEvidence predicate anchor :=
      ⟨anchorAdmissible, coarseStable anchor ⟨anchorAdmissible, rfl⟩, coarseStable⟩
    exact (robust_knowledge_monotone_under_refinement admissible coarseEvidence
      refinedEvidence predicate anchor refinement coarseKnowledge).2.2
  have stableFalse :
      (∀ state, admissible state ∧
          coarseEvidence state = coarseEvidence anchor -> ¬predicate state) ->
        ∀ state, admissible state ∧
          refinedEvidence state = refinedEvidence anchor -> ¬predicate state := by
    intro coarseStable
    have coarseKnowledge :
        robustKnowledge admissible coarseEvidence (fun state => ¬predicate state) anchor :=
      ⟨anchorAdmissible, coarseStable anchor ⟨anchorAdmissible, rfl⟩, coarseStable⟩
    exact (robust_knowledge_monotone_under_refinement admissible coarseEvidence
      refinedEvidence (fun state => ¬predicate state) anchor refinement
        coarseKnowledge).2.2
  refine ⟨⟨anchor, anchorAdmissible, rfl⟩,
    ⟨anchor, anchorAdmissible, rfl⟩, stableTrue, stableFalse, ?_⟩
  intro trueWitness falseWitness trueAdmissible falseAdmissible sameCoarse
    trueHolds falseFails
  dsimp only
  refine ⟨⟨⟨trueWitness, trueAdmissible, rfl⟩, ?_⟩,
    ⟨⟨falseWitness, falseAdmissible, rfl⟩, ?_⟩, ?_⟩
  · intro state stateInTrueFiber
    have propositionEquality :
        (state = trueWitness) = (trueWitness = trueWitness) :=
      congrArg Prod.snd stateInTrueFiber.2
    have stateEquals : state = trueWitness := by
      rw [propositionEquality]
    subst state
    exact trueHolds
  · intro state stateInFalseFiber
    have propositionEquality :
        (state = falseWitness) = (falseWitness = falseWitness) :=
      congrArg Prod.snd stateInFalseFiber.2
    have stateEquals : state = falseWitness := by
      rw [propositionEquality]
    subst state
    exact falseFails
  · refine ⟨trueWitness, falseWitness, trueAdmissible, rfl,
      falseAdmissible, ?_, trueHolds, falseFails⟩
    apply Prod.ext
    · exact sameCoarse.symm
    · rfl

#print axioms actual_evidence_refinement_stability

end D5.S3.ConceptDynamics.Evidence.ActualEvidenceRefinementStability
