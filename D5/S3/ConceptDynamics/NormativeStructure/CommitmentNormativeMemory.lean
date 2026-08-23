/- GID: D5/S3/ConceptDynamics/NormativeStructure/CommitmentNormativeMemory
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/NormativeStructure/CommitmentNormativeMemory
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Different committed permissions at one physical endpoint require normative memory. -/

import D5.S3.ConceptDynamics.NormativeStructure.HistorySensitiveOutcomeReductionObstruction

/- Library-search audit trail (2026-08-23):
   * Exact frozen repository hit
     `history_sensitive_evaluation_not_outcome_reducible` states that equal
     endpoints with unequal evaluations obstruct endpoint-only factorization on
     the canonical `Concept` carrier. It is imported and directly applied.
   * The imported family theorem already applies pinned Mathlib's exact
     `Function.factorsThrough_iff`; no factorization argument is repeated here.
   * Repository searches for committed permission sets and normative memory
     found no more specific accepted theorem. `loogle` and `leansearch` were
     unavailable on PATH. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.NormativeStructure.CommitmentNormativeMemory

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.NormativeStructure.HistorySensitiveOutcomeReductionObstruction

/-- Equal physical endpoints with different committed future permissions rule
out representing those permissions as a function of physical state alone. -/
theorem committed_permissions_do_not_factor_through_physical_state
    {History PhysicalState Policy : Type*}
    (endpoint : Concept History PhysicalState)
    (committedPermissions : Concept History (Set Policy))
    (first second : History)
    (samePhysicalState : endpoint first = endpoint second)
    (differentPermissions :
      committedPermissions first ≠ committedPermissions second) :
    ¬ ∃ statePermissions : PhysicalState -> Set Policy,
      committedPermissions = statePermissions ∘ endpoint := by
  exact history_sensitive_evaluation_not_outcome_reducible
    endpoint committedPermissions
    ⟨first, second, samePhysicalState, differentPermissions⟩

#print axioms committed_permissions_do_not_factor_through_physical_state

end D5.S3.ConceptDynamics.NormativeStructure.CommitmentNormativeMemory
