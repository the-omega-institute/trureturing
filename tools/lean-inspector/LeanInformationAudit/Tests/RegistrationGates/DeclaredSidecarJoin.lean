import LeanInformationAudit.Tests.RegistrationGates.DeclaredSidecar

namespace LeanInformationAudit.Tests.DeclaredSidecarJoin
open Lean Meta TemplateBinding

private def observe (label : String) (ok : Bool) : MetaM Unit :=
  (if ok then logInfo else logError) m!"[{if ok then "PASS" else "FAIL"}] {label}"

run_meta do
  let env ← getEnv
  let source := `LeanInformationAudit.Tests.RegistrationGates.DeclaredSidecarSource
  let sidecar := `LeanInformationAudit.Tests.RegistrationGates.DeclaredSidecar
  let theoremName := ``DeclaredSidecarSource.original
  let some event := (inventory env).find? (·.key.theoremName == theoremName)
    | throwError "setup: imported source event missing"
  let some original := (records env).find? fun row =>
      row.occurrence.key == event.key && row.bindingOwner.isNone
    | throwError "setup: original provisional record missing"
  let some overlay := (records env).find? fun row =>
      row.occurrence.key == event.key && row.bindingOwner == some sidecar
    | throwError "setup: independently imported sidecar record missing"
  let sameOriginal := original.occurrence.key.registrationModule == source &&
    original.occurrence.unitName == overlay.occurrence.unitName &&
    original.occurrence.realizationName == overlay.occurrence.realizationName &&
    original.occurrence.statementIdentity == overlay.occurrence.statementIdentity &&
    (original.result matches .undeclared)
  observe "frozen_sidecar_validates_original_occurrence"
    (sameOriginal && (overlay.result matches .declaredValidated _))
  let joined ← assessJoined
  let selected := joined.filter (·.occurrence.key == event.key)
  observe "sidecar_join_precedes_assessment"
    (selected.size == 1 && selected[0]?.any fun row =>
      row.bindingOwner == some sidecar && (row.result matches .declaredValidated _))
  let claim : TemplateBindingClaim := {
    key := event.key, arena := event.arena, descriptor := overlay.descriptor, owner := sidecar }
  let good := joinClaims #[(source, event)] #[(sidecar, claim)]
  observe "binding_join_keeps_independent_occurrences"
    (match good with
      | .ok result => result.size == 1 && result[0]?.any (·.2.isSome)
      | .error _ => false)
  let duplicate := joinClaims #[(source, event), (source, event)] #[]
  observe "duplicate_undeclared_inventory_rejected"
    (duplicate matches .error "incomplete_closure:dtr.duplicate_occurrence")
  let wrongEvent := joinClaims #[(sidecar, event)] #[]
  observe "sidecar_origin_inventory_rejected"
    (wrongEvent matches .error "incomplete_closure:dtr.event_owner")
  let wrongOwner := joinClaims #[(source, event)] #[(source, claim)]
  let duplicated := joinClaims #[(source, event)] #[(sidecar, claim), (sidecar, claim)]
  let dangling := joinClaims #[(source, event)] #[(sidecar, { claim with key :=
    { claim.key with theoremName := `LeanInformationAudit.Tests.DeclaredSidecarJoin.absent } })]
  let changedArena := joinClaims #[(source, event)] #[(sidecar, { claim with arena := mkConst ``Bool })]
  let correct := (wrongOwner matches .error "incomplete_closure:dtr.claim_owner") &&
    (duplicated matches .error "unclassified_form:dtr.duplicate_claim") &&
    (dangling matches .error "unclassified_form:dtr.dangling_claim") &&
    (changedArena matches .error "unclassified_form:dtr.claim_occurrence")
  observe "sidecar_ownership_and_uniqueness" correct

end LeanInformationAudit.Tests.DeclaredSidecarJoin
