import LeanInformationAudit.Registry
import LeanInformationAudit.Tests.Assessment

test_imported_assessment

open Lean LeanInformationAudit

namespace LeanInformationAuditRegTests

/-- Select actual production inputs using independently supplied occurrence keys.
Keep registry order so provenance work is measured on the original workload. -/
def productionEntries (expected : Array SnapshotOccurrence) : CoreM (Array InformationRegistryEntry) := do
  unless expected.size > 0 do throwError "production expectation must be nonempty"
  let env ← getEnv
  let sameOccurrence (entry : InformationRegistryEntry) (row : SnapshotOccurrence) : Bool :=
    entry.theoremName == row.theoremName &&
    entry.canonicalObjectArenaName == row.objectArenaName &&
    entry.registrationModuleName == row.registrationModuleName &&
    entry.statementIdentity == row.statementIdentity
  let entries := (InformationRegistry.entries env).filter fun entry =>
    expected.any (sameOccurrence entry)
  unless entries.size == expected.size do
    throwError "production occurrence count: actual={entries.size} expected={expected.size}"
  for row in expected do
    unless (entries.filter (sameOccurrence · row)).size == 1 do
      throwError "production occurrence not uniquely realized: {row.theoremName}"
  for entry in entries do
    -- Report companions retain the original registration owner. Mathematical
    -- realizations can come from that owner's import closure.
    unless GeneratedDeclarations.ownerOf env entry.unitName == entry.registrationModuleName do
      throwError "production occurrence has wrong unit owner: {entry.unitName}"
  return entries

end LeanInformationAuditRegTests
