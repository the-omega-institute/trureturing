import LeanInformationAudit.Tests.Occurrence.RootCatalog.Snapshot

open Lean Lean.Elab.Command LeanInformationAudit
open LeanInformationAudit.Tests.Occurrence.RootCatalog

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
  for contract in #[baselineContract, designatedContract] do
    let original ← getEnv
    try
      modifyEnv (·.setMainModule contract.rootId)
      RootCatalogs.declare contract
      let root := contract.rootId
      let rows := snapshotExpectations root contract.source
      validateFrozenBaselineInSnapshot root rows
      let some baselineRow := rows.find? (·.registrationModuleName == baselineRoot)
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
    finally
      setEnv original
  logInfo "ROOT-B-baseline-subset: both supplied roots reject missing or changed baseline rows"

end LeanInformationAudit.Tests.RootBaselineSubset
