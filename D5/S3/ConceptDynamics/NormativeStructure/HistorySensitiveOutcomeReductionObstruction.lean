/- GID: D5/S3/ConceptDynamics/NormativeStructure/HistorySensitiveOutcomeReductionObstruction
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/NormativeStructure/HistorySensitiveOutcomeReductionObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Paths with one outcome and different evaluations obstruct outcome-only representation. -/

import D5.S3.ConceptDynamics.ConceptFiberDecomposition
import Mathlib.Logic.Function.Basic

/- Library-search audit trail (2026-08-22):
   * Exact repository hit `Concept` is the frozen family readout carrier and is
     imported directly for both endpoint and normative evaluation maps.
   * Exact pinned-Mathlib hit `Function.factorsThrough_iff` characterizes
     whole-codomain factorization by constancy on endpoint fibers and is applied
     directly below.
   * `Refinement.InductiveSufficiency` is adjacent but factors through the
     realized endpoint image; `AnswerabilityCriterion` packages additional
     clauses. Neither is this exact outcome-function obstruction.
   * Searches for history-sensitive evaluation, equal endpoints with different
     evaluations, and outcome-only normative representation found no exact
     repository theorem.
   * `loogle` and `leansearch` executables were absent from PATH. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.NormativeStructure.HistorySensitiveOutcomeReductionObstruction

open D5.S3.ConceptDynamics.ConceptFiberDecomposition

/-- If two process paths have the same endpoint but different normative
evaluations, the evaluation cannot be represented by any function of the
endpoint alone. -/
theorem history_sensitive_evaluation_not_outcome_reducible
    {Path Outcome Evaluation : Type*}
    (endpoint : Concept Path Outcome) (evaluation : Concept Path Evaluation)
    (historySensitive : ∃ first second : Path,
      endpoint first = endpoint second ∧ evaluation first ≠ evaluation second) :
    ¬∃ outcomeEvaluation : Outcome → Evaluation,
      evaluation = outcomeEvaluation ∘ endpoint := by
  rcases historySensitive with
    ⟨first, second, sameOutcome, differentEvaluation⟩
  letI : Nonempty Evaluation := ⟨evaluation first⟩
  intro outcomeReduction
  have constantOnOutcomeFibers : Function.FactorsThrough evaluation endpoint :=
    (Function.factorsThrough_iff (f := endpoint) evaluation).2 outcomeReduction
  exact differentEvaluation (constantOnOutcomeFibers sameOutcome)

/-- A constant endpoint and identity evaluation on two paths witness the
history-sensitive premise. -/
example :
    let endpoint : Concept Bool Unit := fun _ => ()
    let evaluation : Concept Bool Bool := id
    ∃ first second : Bool,
      endpoint first = endpoint second ∧ evaluation first ≠ evaluation second := by
  exact ⟨false, true, rfl, Bool.false_ne_true⟩

#print axioms history_sensitive_evaluation_not_outcome_reducible

end D5.S3.ConceptDynamics.NormativeStructure.HistorySensitiveOutcomeReductionObstruction
