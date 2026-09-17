import LeanInformationAudit.Syntax

namespace LeanInformationAudit.Tests
open Lean Meta Elab Command

/-- Exact occurrence keys come from the independently retained semantic registry.
The binding inventory and record publication must both cover each key once. -/
def assertUndeclaredInventory (env : Environment) (owner : Name) (expected : Nat) : MetaM Bool := do
  let entries := (InformationRegistry.entries env).filter (·.registrationModuleName == owner)
  let events := (TemplateBinding.inventory env).filter (·.key.registrationModule == owner)
  let records := (TemplateBinding.records env).filter (·.occurrence.key.registrationModule == owner)
  let mut valid := entries.size == expected && events.size == expected && records.size == expected
  for entry in entries do
    let key : TemplateOccurrenceKey := {
      root := entry.registrationModuleName
      registrationModule := entry.registrationModuleName
      theoremName := entry.theoremName
      objectArena := entry.canonicalObjectArenaName
      «catalog» := entry.effectiveCatalogId }
    let matchedEvents := events.filter (·.key == key)
    let matchedRecords := records.filter (·.occurrence.key == key)
    let mut rowOk := matchedEvents.size == 1 && matchedRecords.size == 1
    if let some event := matchedEvents[0]? then
      rowOk := rowOk && event.unitName == entry.unitName && event.realizationName == entry.realizationName
      if let some record := matchedRecords[0]? then
        rowOk := rowOk && record.occurrence.key == event.key &&
          record.occurrence.unitName == event.unitName && record.occurrence.realizationName == event.realizationName &&
          record.occurrence.statementIdentity == event.statementIdentity && record.descriptor.isNone && record.bindingOwner.isNone
        match record.result with
        | .undeclared =>
          let json ← TemplateBinding.recordJson record
          rowOk := rowOk && json.getObjValAs? String "state" == .ok "undeclared" &&
            json.getObjValAs? String "diagnostic" == .ok (TemplateBinding.missingDeclarationDiagnostic key) &&
            (json.getObjVal? "certificate").toOption.any (fun value => value.compress == "null")
        | _ => rowOk := false
    valid := valid && rowOk
    unless rowOk do logError m!"[FAIL] RewriteInventory/{owner}/{key.theoremName}: exact undeclared binding missing"
  if valid then logInfo m!"[PASS] RewriteInventory/{owner}: occurrences={expected} state=undeclared certificates=0"
  else logError m!"[FAIL] RewriteInventory/{owner}: expected={expected} entries={entries.size} events={events.size} records={records.size}"
  return valid

end LeanInformationAudit.Tests
