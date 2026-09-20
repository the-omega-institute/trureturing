import LeanInformationAudit.SealCommand

open Lean Lean.Elab.Command LeanInformationAudit

namespace LeanInformationAudit.Tests.RootBaselineSubset

private def rejects (root : Name) (rows : Array ExpectedOccurrence)
    (component : String) : CommandElabM Unit := do
  let message ← try
    validateFrozenBaselineInSnapshot root rows
    pure "accepted"
  catch error =>
    error.toMessageData.toString
  let messagePrefix := s!"IE-C028 AnalysisCertificateMismatch root={root} " ++
    s!"catalog=registry-snapshot component=frozen-baseline-{component} expected="
  unless message.startsWith messagePrefix && (message.splitOn " actual=").length == 2 do
    throwError "ROOT-B-baseline-subset: wrong failure: {message}"

run_cmd do
  for root in #[frozenInformationRootId, designatedInformationRootId] do
    let some contract := RootCatalogs.find? (← getEnv) root
      | throwError "ROOT-B-baseline-subset: missing root contract"
    let rows := snapshotExpectations root contract.source
    validateFrozenBaselineInSnapshot root rows
    let baselineRow := rows.find? (·.registrationModuleName == frozenInformationRootId)
    let some baselineRow := baselineRow
      | throwError "ROOT-B-baseline-subset: missing test input"
    let sameKey := fun (row : ExpectedOccurrence) =>
      row.objectArenaName == baselineRow.objectArenaName &&
        row.theoremName == baselineRow.theoremName
    rejects root (rows.filter fun row => !sameKey row) "member-set"
    rejects root (rows.map fun row =>
      if sameKey row then { row with statementIdentity := "sha256:corrupt" } else row)
      "statement-identities"
    rejects root (rows.map fun row =>
      if sameKey row then { row with registrationModuleName := `CorruptContributor } else row)
      "contributor-modules"
  logInfo "ROOT-B-baseline-subset: both fixed roots reject missing or changed baseline rows"

end LeanInformationAudit.Tests.RootBaselineSubset
