import LeanInformationAudit.Tests.RegistrationGates.DeclaredRegistration

namespace LeanInformationAudit.Tests.DeclaredJoin
open Lean Meta TemplateBinding

private def observe (label : String) (ok : Bool) : MetaM Unit :=
  (if ok then logInfo else logError) m!"[{if ok then "PASS" else "FAIL"}] {label}"

run_meta do
  let env ← getEnv
  let source := `LeanInformationAudit.Tests.RegistrationGates.DeclaredSource
  let producer := `LeanInformationAudit.Tests.RegistrationGates.DeclaredRegistration
  let theoremName := ``DeclaredSource.original
  let some event := (inventory env).find? (·.key.theoremName == theoremName)
    | throwError "setup: imported registration event missing"
  let some record := (records env).find? (·.occurrence.key == event.key)
    | throwError "setup: imported binding record missing"
  observe "imported_theorem_registration_owns_binding"
    (event.key.registrationModule == producer && record.bindingOwner == some producer &&
      (env.getModuleIdxFor? theoremName).map (env.header.moduleNames[·]!) == some source &&
      (record.result matches .declaredValidated _))
  let joined ← assessJoined
  let selected := joined.filter (·.occurrence.key == event.key)
  observe "inline_join_precedes_assessment"
    (selected.size == 1 && selected[0]?.any fun row =>
      row.bindingOwner == some producer && (row.result matches .declaredValidated _))
  let claim : TemplateBindingClaim := {
    key := event.key, arena := event.arena, descriptor := record.descriptor, owner := producer }
  let good := joinClaims #[(producer, event)] #[(producer, claim)]
  observe "binding_join_keeps_independent_occurrences"
    (match good with
      | .ok result => result.size == 1 && result[0]?.any (·.2.isSome)
      | .error _ => false)
  let duplicate := joinClaims #[(producer, event), (producer, event)] #[]
  observe "duplicate_undeclared_inventory_rejected"
    (duplicate matches .error "incomplete_closure:dtr.duplicate_occurrence")
  let wrongEvent := joinClaims #[(source, event)] #[]
  observe "foreign_origin_inventory_rejected"
    (wrongEvent matches .error "incomplete_closure:dtr.event_owner")
  let wrongOwner := joinClaims #[(producer, event)] #[(source, claim)]
  let duplicated := joinClaims #[(producer, event)] #[(producer, claim), (producer, claim)]
  let dangling := joinClaims #[(producer, event)] #[(producer, { claim with key :=
    { claim.key with theoremName := `LeanInformationAudit.Tests.DeclaredJoin.absent } })]
  let changedArena := joinClaims #[(producer, event)] #[(producer, { claim with arena := mkConst ``Bool })]
  let correct := (wrongOwner matches .error "incomplete_closure:dtr.claim_owner") &&
    (duplicated matches .error "unclassified_form:dtr.duplicate_claim") &&
    (dangling matches .error "unclassified_form:dtr.dangling_claim") &&
    (changedArena matches .error "unclassified_form:dtr.claim_occurrence")
  observe "inline_ownership_and_uniqueness" correct

end LeanInformationAudit.Tests.DeclaredJoin
