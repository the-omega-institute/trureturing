import LeanInformationAudit.Registry

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
    -- The unit is generated in the registration producer. A mathematical
    -- realization can come from that producer's import closure; the existing
    -- checkImportedOwners controls exercise TemplateBinding.validateEvent for it.
    unless (env.getModuleIdxFor? entry.unitName).map (env.header.moduleNames[·.toNat]!) ==
        some entry.registrationModuleName do
      throwError "production occurrence has wrong native unit owner: {entry.unitName}"
  return entries

end LeanInformationAuditRegTests
