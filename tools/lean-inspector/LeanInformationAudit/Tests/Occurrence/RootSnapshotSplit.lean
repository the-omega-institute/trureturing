import LeanInformationAudit.Tests.Occurrence.RootCatalog.Snapshot

open Lean Lean.Elab.Command LeanInformationAudit
open LeanInformationAudit.Tests.Occurrence.RootCatalog

namespace LeanInformationAudit.Tests.RootSnapshotSplit

run_cmd do
  let original ← getEnv
  try
    let empty ← liftIO mkEmptyEnvironment
    setEnv (empty.setMainModule baselineRoot)
    RootCatalogs.declare baselineContract
    modifyEnv (·.setMainModule designatedRoot)
    RootCatalogs.declare designatedContract
    let env ← getEnv
    let baseline := expectedOccurrencesForRoot env baselineRoot
    let designated := expectedOccurrencesForRoot env designatedRoot
    unless baseline.size == 1 && designated.size == 3 do
      throwError "ROOT-B-snapshot-split: expected baseline=1 designated=3"
    unless baseline.all (·.registrationModuleName == baselineRoot) do
      throwError "ROOT-B-snapshot-split: baseline contributor changed"
    let causal := designated.filter (·.registrationModuleName != baselineRoot)
    unless causal.size == 2 && causal.all (fun row =>
        row.objectArenaName == causalRows[0]!.objectArenaName &&
        row.registrationModuleName == causalContributor) do
      throwError "ROOT-B-snapshot-split: causal occurrence identity changed"
    unless (expectedOccurrencesForRoot env `UnrelatedConsumer).isEmpty do
      throwError "ROOT-B-snapshot-split: unrelated root acquired supplied expectations"
  finally
    setEnv original

end LeanInformationAudit.Tests.RootSnapshotSplit
