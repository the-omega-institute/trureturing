import LeanInformationAudit.Registry

open Lean Lean.Meta LeanInformationAudit

namespace LeanInformationAudit.Tests.Occurrence.RootCatalog.Ownership

-- This helper is imported by observers, never by the registration producers.
private def foreignDeclaration : Nat := 0

def rejectsOwner (event : TemplateOccurrenceEvent) : MetaM Unit := do
  let env ← getEnv
  unless env.contains event.unitName && env.contains event.realizationName do
    throwError "wrong-owner control requires existing declarations, not missing names"
  let message ← try
    TemplateBinding.validateEvent event
    pure "accepted"
  catch error => error.toMessageData.toString
  unless message == "incomplete_closure:dtr.event_unit_owner" do
    throwError "wrong-owner control: {message}"

/-- The same ownership assertions serve synthetic roots and actual production
roots. Neither expected count nor expected owner is taken from the inventory. -/
def checkImportedOwners (root : Name) (expected : Nat) : MetaM Unit := do
  let env ← getEnv
  let some foreignOwner := RegistrationReifier.declaringModuleOf env ``foreignDeclaration
    | throwError "wrong-owner control requires an imported native declaration"
  unless foreignOwner != root do throwError "wrong-owner control uses the registration owner"
  let events := (TemplateBinding.inventory env).filter
    (·.key.registrationModule == root)
  unless expected > 0 && events.size == expected do
    throwError "imported owner setup: {root}: expected={expected} actual={events.size}"
  for event in events do
    TemplateBinding.validateEvent event
    rejectsOwner { event with realizationName := ``foreignDeclaration }
    rejectsOwner { event with unitName := ``foreignDeclaration }
  logInfo m!"[PASS] imported_realizations_keep_original_owner root={root} accepted={expected}"
  logInfo m!"[PASS] imported_realization_wrong_owner_rejected root={root} rejected={expected}"
  logInfo m!"[PASS] generated_unit_wrong_owner_rejected root={root} rejected={expected}"

end LeanInformationAudit.Tests.Occurrence.RootCatalog.Ownership
