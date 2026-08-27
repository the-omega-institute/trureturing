/- GID: D5/S3/ConceptDynamics/NormativeStructure/HistorySensitiveOutcomeReductionComplete
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/NormativeStructure/HistorySensitiveOutcomeReductionComplete
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: History sensitivity obstructs reduction; its defect is a kernel difference. -/

import D5.S3.ConceptDynamics.NormativeStructure.HistorySensitiveOutcomeReductionObstruction
import D5.S3.ConceptDynamics.TargetRisk.RefinementRiskCostTradeoff

/- Library-search audit trail (2026-08-27):
   * The frozen repository theorem
     `history_sensitive_evaluation_not_outcome_reducible` is the exact
     non-factorization clause and is imported directly.
   * The canonical `defectRelation` primitive is the source-shaped relation
     for equal endpoints and unequal evaluations; it is imported rather than
     redeclared.
   * `Setoid.ker_def` is the pinned Mathlib bridge from equality kernels to
     function application. No bundled theorem for the kernel difference was
     found in D5 or Mathlib.
   * `loogle` and `leansearch` were unavailable on PATH.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.NormativeStructure.HistorySensitiveOutcomeReductionComplete

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.NormativeStructure.HistorySensitiveOutcomeReductionObstruction
open D5.S3.ConceptDynamics.TargetRisk.RefinementRiskCostTradeoff

/-- The frozen obstruction theorem together with the source's canonical
kernel-difference defect relation. -/
theorem history_sensitive_evaluation_not_outcome_reducible_with_defect
    {Path Outcome Evaluation : Type*}
    (endpoint : Concept Path Outcome) (evaluation : Concept Path Evaluation)
    (historySensitive : ∃ first second : Path,
      endpoint first = endpoint second ∧ evaluation first ≠ evaluation second) :
    (¬∃ outcomeEvaluation : Outcome → Evaluation,
      evaluation = outcomeEvaluation ∘ endpoint) ∧
      defectRelation endpoint evaluation =
        ({pair : Path × Path | Setoid.ker endpoint pair.1 pair.2} : Set (Path × Path)) \
          {pair : Path × Path | Setoid.ker evaluation pair.1 pair.2} := by
  constructor
  · exact history_sensitive_evaluation_not_outcome_reducible endpoint evaluation
      historySensitive
  · ext pair
    simp only [defectRelation, Set.mem_setOf_eq, Set.mem_sdiff, Setoid.ker_def]

#print axioms history_sensitive_evaluation_not_outcome_reducible_with_defect

end D5.S3.ConceptDynamics.NormativeStructure.HistorySensitiveOutcomeReductionComplete
