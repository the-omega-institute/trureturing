import LeanInformationAuditAnalysis.Tests.RootContract.Producer

open Lean Lean.Elab.Command LeanInformationAudit

private def rejects (expected source baseline : Array SnapshotOccurrence)
    (component : String) : CommandElabM Unit := do
  let saved ← getEnv
  let message ← try
    RootCatalogs.declare { rootId := saved.header.mainModule, expected, source, baseline }
    validateRegistrySnapshot (← getEnv)
    pure "accepted"
  catch error => error.toMessageData.toString
  finally setEnv saved
  unless (message.splitOn s!"component={component} expected=").length == 2 do
    throwError "root contract negative control failed: {component}: {message}"

run_cmd do
  let some contract := RootCatalogs.find? (← getEnv)
      `LeanInformationAuditAnalysis.Tests.RootContract.Producer
    | throwError "independently supplied producer contract missing"
  let rows := contract.expected
  let badIdentity := rows.map fun row => { row with statementIdentity := "sha256:changed" }
  let badContributor := rows.map fun row => { row with registrationModuleName := `OtherModule }
  rejects rows #[] rows "frozen-baseline-member-set"
  rejects rows badIdentity rows "frozen-baseline-statement-identities"
  rejects rows badContributor rows "frozen-baseline-contributor-modules"
  rejects #[] rows rows "member-set"
  rejects badIdentity rows rows "statement-identities"
  rejects badContributor rows rows "contributor-modules"
