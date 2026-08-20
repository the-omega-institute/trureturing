/- GID: D5/S3/ConceptDynamics/LegitimacyCorrectness
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/LegitimacyCorrectness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Authorization provenance can pass while a result target fails. -/

import D5.S3.ConceptDynamics.ConceptFiberDecomposition

/- Library-search audit trail (2026-08-21):
   * `rg -n 'legitimacy.*correctness|authorization.*result' D5 --glob '*.lean'`
     found no theorem exposing both source audit channels.
   * The canonical `Concept` alias is imported and used for the source result
     and target maps; no sibling readout type is declared here.
   * Pinned Mathlib searches for an authorization/result separation theorem
     found no exact hit, so the countermodel is constructed from the source
     authorization and result primitives. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.LegitimacyCorrectness

open D5.S3.ConceptDynamics.ConceptFiberDecomposition

/-- The result audit compares an actual result map with its target map. -/
def resultAudit {Input Result : Type*}
    (target actual : Concept Input Result) : Prop :=
  ∀ input, actual input = target input

/-- The provenance audit checks that every executed action is authorized. -/
def authorizationAudit {Input Action : Type*}
    (authorize : Input → Action → Prop)
    (executed : Input → Action) : Prop :=
  ∀ input, authorize input (executed input)

/-- A program may pass its authorization audit while failing its factual
target audit. The two audits therefore carry independent source semantics. -/
theorem authorized_process_can_fail_factually
    {Input Action Result : Type*}
    (input : Input) (action : Action)
    (correctResult incorrectResult : Result)
    (different : incorrectResult ≠ correctResult) :
    ∃ authorize : Input → Action → Prop,
      ∃ target actual : Concept Input Result,
        authorizationAudit authorize (fun _ => action) ∧
          ¬ resultAudit target actual := by
  refine ⟨fun _ _ => True, fun _ => correctResult, fun _ => incorrectResult, ?_, ?_⟩
  · intro _
    trivial
  · intro hAudit
    exact different (hAudit input)

/-- The public hypotheses and conclusion have a concrete two-result model. -/
example :
    ∃ authorize : Unit → Unit → Prop,
      ∃ target actual : Concept Unit Bool,
        authorizationAudit authorize (fun _ => ()) ∧
          ¬ resultAudit target actual := by
  exact authorized_process_can_fail_factually () () true false Bool.false_ne_true

#print axioms authorized_process_can_fail_factually

end D5.S3.ConceptDynamics.LegitimacyCorrectness
