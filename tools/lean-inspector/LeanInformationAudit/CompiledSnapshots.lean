import LeanInformationAudit.RegistrationRelations

namespace LeanInformationAudit.CompiledSnapshots
open Lean

private def expectedKey (entry : ExpectedOccurrence) : String :=
  entry.objectArenaName.toString ++ "/" ++ entry.theoremName.toString
private def expectedIdentity (entry : ExpectedOccurrence) : String :=
  expectedKey entry ++ "=" ++ entry.statementIdentity
private def expectedContributor (entry : ExpectedOccurrence) : String :=
  expectedKey entry ++ "=" ++ entry.registrationModuleName.toString
private def actualIdentity (entry : InformationRegistryEntry) : String :=
  entry.occurrenceKeyString ++ "=" ++ entry.statementIdentity
private def actualContributor (entry : InformationRegistryEntry) : String :=
  entry.occurrenceKeyString ++ "=" ++ entry.registrationModuleName.toString

private def compare (root : Name) (component : String)
    (expected actual : Array String) : Except String Unit := do
  unless expected == actual do
    throw s!"IE-C028 AnalysisCertificateMismatch root={root} catalog=registry-snapshot \
      component={component} expected={(toJson expected).compress} actual={(toJson actual).compress}"

/-- Source regeneration retains baseline membership, statement identities and
contributors. Arrays retain multiplicity; duplicates cannot disappear in a set. -/
def baseline (root : Name) (baseline snapshot : Array ExpectedOccurrence) : Except String Unit := do
  let baselineKeys := baseline.map expectedKey |>.qsort (· < ·)
  let retained := snapshot.filter (fun row => baselineKeys.contains (expectedKey row))
  compare root "frozen-baseline-member-set" baselineKeys
    (retained.map expectedKey |>.qsort (· < ·))
  compare root "frozen-baseline-statement-identities"
    (baseline.map expectedIdentity |>.qsort (· < ·))
    (retained.map expectedIdentity |>.qsort (· < ·))
  compare root "frozen-baseline-contributor-modules"
    (baseline.map expectedContributor |>.qsort (· < ·))
    (retained.map expectedContributor |>.qsort (· < ·))

/-- Independent expectations name canonical arenas explicitly and are compared
with the root's complete registry in all three coordinates. -/
def registry (find : Name → Option ConstantInfo) (root : Name)
    (contract : Option RootCatalogContract) (actual : Array InformationRegistryEntry)
    : Except String Unit := do
  if let some contract := contract then
    baseline root (snapshotExpectations root contract.baseline)
      (snapshotExpectations root contract.source)
  let expected ← (contract.map (fun c => snapshotExpectations root c.expected) |>.getD #[]).mapM
    fun entry => do
      unless (find entry.objectArenaName).isSome do
        throw s!"IE-C003 ArenaResolutionFailed: {entry.objectArenaName}"
      return entry
  compare root "member-set" (expected.map expectedKey |>.qsort (· < ·))
    (actual.map InformationRegistryEntry.occurrenceKeyString |>.qsort (· < ·))
  compare root "statement-identities" (expected.map expectedIdentity |>.qsort (· < ·))
    (actual.map actualIdentity |>.qsort (· < ·))
  compare root "contributor-modules" (expected.map expectedContributor |>.qsort (· < ·))
    (actual.map actualContributor |>.qsort (· < ·))

end LeanInformationAudit.CompiledSnapshots
