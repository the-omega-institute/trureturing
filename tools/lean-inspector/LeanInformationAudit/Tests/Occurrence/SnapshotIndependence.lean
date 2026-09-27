import LeanInformationAudit.Tests.Occurrence.RootCatalog.Snapshot

open Lean Lean.Elab.Command LeanInformationAudit
open LeanInformationAudit.Tests.Occurrence.RootCatalog

namespace LeanInformationAudit.Tests.SnapshotIndependence

/-- info: supplied snapshot identities survive an empty consumer environment -/
#guard_msgs (info) in
run_cmd do
  let original ← getEnv
  try
    let empty ← liftIO mkEmptyEnvironment
    setEnv (empty.setMainModule designatedRoot)
    RootCatalogs.declare designatedContract
    let env ← getEnv
    let rows := expectedOccurrencesForRoot env designatedRoot
    unless rows.size == 3 && rows.all (fun row =>
        !row.statementIdentity.isEmpty && !row.registrationModuleName.isAnonymous &&
        !env.contains row.theoremName && !env.contains row.objectArenaName) do
      throwError "supplied snapshot identities depend on consumer declarations"
    unless (expectedOccurrencesForRoot env `UnrelatedConsumer).isEmpty do
      throwError "supplied contract leaked into another root"
    logInfo "supplied snapshot identities survive an empty consumer environment"
  finally
    setEnv original

end LeanInformationAudit.Tests.SnapshotIndependence
