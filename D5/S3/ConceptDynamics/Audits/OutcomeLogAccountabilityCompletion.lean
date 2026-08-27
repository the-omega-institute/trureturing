/- GID: D5/S3/ConceptDynamics/Audits/OutcomeLogAccountabilityCompletion
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Audits/OutcomeLogAccountabilityCompletion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Outcome-only logs omit accountability, whose canonical completion is least. -/

import D5.S3.ConceptDynamics.NormativeStructure.HistorySensitiveOutcomeReductionObstruction
import D5.S3.ConceptDynamics.ConceptJoinUniversal

/- Library-search audit trail (2026-08-27):
   * Body-shape searches for the four-channel nested join found the adjacent
     procedure-audit modules. They use the canonical `conceptJoin` primitive but
     do not combine a general outcome-only obstruction with the least completion.
   * Exact repository hit
     `history_sensitive_evaluation_not_outcome_reducible` proves the general
     same-outcome, different-evaluation obstruction and is applied directly.
   * Exact repository hit `concept_join_universal` supplies both completion
     projections and its universal least-common-refinement clause.
   * Pinned Mathlib hit `Function.factorsThrough_iff` underlies the imported
     obstruction. No repository or pinned-library theorem combines both public
     halves of this statement. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Audits.OutcomeLogAccountabilityCompletion

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.NormativeStructure.HistorySensitiveOutcomeReductionObstruction

/-- If two states have the same decision but different actors or rules, every
log that factors through the decision omits the full decision-rule-actor-source
readout. Joining any log with that accountability readout preserves both and is
the least common refinement. -/
theorem outcome_log_obstruction_and_accountability_completion
    {Z Decision Rule Actor Provenance : Type*}
    (decision : Concept Z Decision) (rule : Concept Z Rule)
    (actor : Concept Z Actor) (provenance : Concept Z Provenance)
    {left right : Z} (sameDecision : decision left = decision right)
    (differentAccountability :
      actor left ≠ actor right ∨ rule left ≠ rule right) :
    (forall {Log : Type*} (log : Concept Z Log),
      Refines log decision ->
        Not (Refines
          (conceptJoin (conceptJoin (conceptJoin decision rule) actor) provenance)
          log)) ∧
    forall {Log : Type*} (log : Concept Z Log),
      Refines log
          (conceptJoin log
            (conceptJoin (conceptJoin (conceptJoin decision rule) actor) provenance)) ∧
        Refines
          (conceptJoin (conceptJoin (conceptJoin decision rule) actor) provenance)
          (conceptJoin log
            (conceptJoin (conceptJoin (conceptJoin decision rule) actor) provenance)) ∧
        forall {Candidate : Type*} (candidate : Concept Z Candidate),
          Refines log candidate ->
            Refines
                (conceptJoin (conceptJoin (conceptJoin decision rule) actor) provenance)
                candidate ->
              Refines
                (conceptJoin log
                  (conceptJoin (conceptJoin (conceptJoin decision rule) actor) provenance))
                candidate := by
  constructor
  · intro Log log logOnlyRecordsDecision
    apply history_sensitive_evaluation_not_outcome_reducible log
      (conceptJoin (conceptJoin (conceptJoin decision rule) actor) provenance)
    refine ⟨left, right, ?_, ?_⟩
    · rcases logOnlyRecordsDecision with ⟨factor, factorization⟩
      rw [factorization]
      exact congrArg factor sameDecision
    · intro sameAccountability
      rcases differentAccountability with differentActor | differentRule
      · exact differentActor (congrArg (fun value => value.1.2) sameAccountability)
      · exact differentRule (congrArg (fun value => value.1.1.2) sameAccountability)
  · intro Log log
    let accountability :=
      conceptJoin (conceptJoin (conceptJoin decision rule) actor) provenance
    refine ⟨
      (concept_join_universal log accountability (conceptJoin log accountability)).1,
      (concept_join_universal log accountability (conceptJoin log accountability)).2.1,
      ?_⟩
    intro Candidate candidate logRefines accountabilityRefines
    exact (concept_join_universal log accountability candidate).2.2
      logRefines accountabilityRefines

/-- The source premises are inhabited by a constant decision and a varying rule. -/
example :
    exists left right : Bool,
      (fun _ : Bool => ()) left = (fun _ : Bool => ()) right ∧
        ((fun _ : Bool => ()) left ≠ (fun _ : Bool => ()) right ∨
          (id : Bool -> Bool) left ≠ (id : Bool -> Bool) right) := by
  exact ⟨false, true, rfl, Or.inr Bool.false_ne_true⟩

#print axioms outcome_log_obstruction_and_accountability_completion

end D5.S3.ConceptDynamics.Audits.OutcomeLogAccountabilityCompletion
