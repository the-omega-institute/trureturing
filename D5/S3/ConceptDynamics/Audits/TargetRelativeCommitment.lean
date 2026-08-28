/- GID: D5/S3/ConceptDynamics/Audits/TargetRelativeCommitment
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/Audits/TargetRelativeCommitment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: One commitment can protect balance while exposing three other history targets. -/

import Mathlib.Logic.Equiv.Bool

/- Library-search audit trail (2026-08-25):
   * Searches for commitment interfaces, target-relative edits, balance, order,
     identity, and authorization found no D5 declaration with all source clauses.
   * A body-shape search for `H history = H (edit history)` implying equality of
     a target after the same edit found no repository primitive to import.
   * Pinned Mathlib's `Bool.not_injective` and `Bool.not_ne_self` are the exact
     Boolean facts used for commitment detection and changed target values.
   * The edit, commitment, and four targets are public constructions from the
     five history coordinates; no target-shaped definition is introduced.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Audits.TargetRelativeCommitment

/-- A single Boolean commitment can nonvacuously detect balance edits while one
undetected edit changes event order, identity source, and contract authorization.
Consequently the same interface is not tamper-proof independently of its target. -/
theorem commitment_protection_is_target_relative :
    let History := Bool × Bool × Bool × Bool × Bool
    let edit : History -> History := fun history =>
      if history.1 then
        (history.1, !history.2.1, history.2.2.1,
          history.2.2.2.1, history.2.2.2.2)
      else
        (history.1, history.2.1, !history.2.2.1,
          !history.2.2.2.1, !history.2.2.2.2)
    let commitment : History -> Bool := fun history => !history.2.1
    let balanceTarget : History -> Bool := fun history => history.2.1
    let eventOrderTarget : History -> Bool := fun history => history.2.2.1
    let identitySourceTarget : History -> Bool := fun history => history.2.2.2.1
    let contractAuthorizationTarget : History -> Bool := fun history => history.2.2.2.2
    let otherEdit : History := (false, false, false, false, false)
    (∀ history,
      commitment history = commitment (edit history) ->
        balanceTarget history = balanceTarget (edit history)) ∧
    commitment otherEdit = commitment (edit otherEdit) ∧
    eventOrderTarget otherEdit ≠ eventOrderTarget (edit otherEdit) ∧
    identitySourceTarget otherEdit ≠ identitySourceTarget (edit otherEdit) ∧
    contractAuthorizationTarget otherEdit ≠
      contractAuthorizationTarget (edit otherEdit) ∧
    ¬ ∀ target : History -> Bool, ∀ history,
      commitment history = commitment (edit history) ->
        target history = target (edit history) := by
  dsimp
  refine ⟨?_, rfl, by decide, by decide, by decide, ?_⟩
  · intro history collision
    exact Bool.not_injective collision
  · intro allTargets
    have orderPreserved := allTargets
      (fun history => history.2.2.1) (false, false, false, false, false) rfl
    exact Bool.false_ne_true orderPreserved

#print axioms commitment_protection_is_target_relative

end D5.S3.ConceptDynamics.Audits.TargetRelativeCommitment
