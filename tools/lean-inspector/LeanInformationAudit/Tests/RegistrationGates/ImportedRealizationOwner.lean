import D5.S3.ConceptDynamics.InformationEscape.InformationRoot

namespace LeanInformationAudit.Tests.ImportedRealizationOwner
open Lean Meta

private def foreignDeclaration : Nat := 0

private def rejection (event : TemplateOccurrenceEvent) : MetaM Bool := do
  try
    TemplateBinding.validateEvent event
    return false
  catch error =>
    return (← error.toMessageData.toString) == "incomplete_closure:dtr.event_unit_owner"

run_meta do
  let env ← getEnv
  let root := `D5.S3.ConceptDynamics.InformationEscape.InformationRoot
  let events := (TemplateBinding.inventory env).filter (·.key.registrationModule == root)
  unless events.size == 11 do throwError "setup: expected eleven original root occurrences"
  let mut accepted : Nat := 0
  for event in events do
    try
      TemplateBinding.validateEvent event
      accepted := accepted + 1
    catch _ => pure ()
  (if accepted == 11 then logInfo else logError) m!"[{if accepted == 11 then "PASS" else "FAIL"}] \
    imported_realizations_keep_original_owner accepted={accepted}"
  let event := events[0]!
  let badRealization ← rejection { event with realizationName := ``foreignDeclaration }
  let badUnit ← rejection { event with unitName := ``foreignDeclaration }
  (if badRealization then logInfo else logError) m!"[{if badRealization then "PASS" else "FAIL"}] imported_realization_wrong_owner_rejected"
  (if badUnit then logInfo else logError) m!"[{if badUnit then "PASS" else "FAIL"}] generated_unit_wrong_owner_rejected"

end LeanInformationAudit.Tests.ImportedRealizationOwner
