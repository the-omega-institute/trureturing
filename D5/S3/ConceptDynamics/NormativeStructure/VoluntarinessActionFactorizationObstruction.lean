/- GID: D5/S3/ConceptDynamics/NormativeStructure/VoluntarinessActionFactorizationObstruction
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/NormativeStructure/VoluntarinessActionFactorizationObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Equal actions with different voluntariness status obstruct action-only evaluation. -/

import D5.S3.ConceptDynamics.NormativeStructure.HistorySensitiveOutcomeReductionObstruction

/- Library-search audit trail (2026-08-23):
   * Exact repository hit
     `history_sensitive_evaluation_not_outcome_reducible` proves the general
     equal-endpoint, different-evaluation obstruction on the canonical `Concept`
     carrier. It is imported and directly applied below.
   * That frozen family theorem already applies pinned Mathlib's exact
     `Function.factorsThrough_iff`; no factorization argument is reproved here.
   * `loogle` and `leansearch` are absent. Related provenance countermodels are
     less exact than the imported general theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.NormativeStructure.VoluntarinessActionFactorizationObstruction

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.NormativeStructure.HistorySensitiveOutcomeReductionObstruction

/-- If a freely chosen path and a coerced path produce the same action but have
different normative voluntariness status, voluntariness cannot be recovered
from the action alone. -/
theorem action_result_does_not_identify_voluntariness
    {Path Action AuthorizationStatus : Type*}
    (action : Concept Path Action)
    (voluntariness : Concept Path AuthorizationStatus)
    (freelyChosen coerced : Path)
    (sameAction : action freelyChosen = action coerced)
    (differentStatus : voluntariness freelyChosen ≠ voluntariness coerced) :
    ¬ ∃ actionEvaluation : Action -> AuthorizationStatus,
      voluntariness = actionEvaluation ∘ action := by
  exact history_sensitive_evaluation_not_outcome_reducible
    action voluntariness
    ⟨freelyChosen, coerced, sameAction, differentStatus⟩

example :
    ¬ ∃ actionEvaluation : Unit -> Bool,
      (id : Concept Bool Bool) =
        actionEvaluation ∘ (fun _ : Bool => ()) := by
  exact action_result_does_not_identify_voluntariness
    (fun _ : Bool => ()) id false true rfl Bool.false_ne_true

#print axioms action_result_does_not_identify_voluntariness

end D5.S3.ConceptDynamics.NormativeStructure.VoluntarinessActionFactorizationObstruction
