import LeanInformationAudit.SealCommand

open Lean LeanInformationAudit

namespace LeanInformationAudit.Tests.SnapshotIndependence

/-- info: designated snapshot identities survive an empty consumer environment -/
#guard_msgs (info) in
run_cmd do
  let empty ← Lean.Elab.Command.liftIO <| mkEmptyEnvironment
  let rows := expectedOccurrencesForRoot empty designatedInformationRootId
  unless !rows.isEmpty && rows.all (fun row =>
      !row.statementIdentity.isEmpty && !row.registrationModuleName.isAnonymous) do
    throwError "designated snapshot identities depend on the consumer environment"
  logInfo "designated snapshot identities survive an empty consumer environment"

end LeanInformationAudit.Tests.SnapshotIndependence
