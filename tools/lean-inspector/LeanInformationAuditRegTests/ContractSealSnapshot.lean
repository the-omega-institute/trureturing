import LeanInformationAuditRegTests.ContractAssertions
import LeanInformationAuditRegTests.ContractSealSnapshotRecorded
import LeanInformationAuditRegTests.ContractSealSnapshotTyped

namespace LeanInformationAuditRegTests.ContractSealSnapshot
open Lean Meta Elab Command
open LeanInformationAuditRegTests.ContractGuards

run_meta do
  let recorded ← ContractControl.read ContractSealSnapshotRecorded.result
  let typed ← ContractControl.read ContractSealSnapshotTyped.result
  assertTest "seal.snapshot.recorded_validated"
    ((recorded.getObjValAs? Bool "snapshot_validated").toOption == some true)
  assertTest "seal.snapshot.typed_validated"
    ((typed.getObjValAs? Bool "snapshot_validated").toOption == some true)
  logInfo m!"SEAL_SNAPSHOT_CONTROL {(Json.mkObj [("recorded", recorded), ("typed", typed)]).compress}"

end LeanInformationAuditRegTests.ContractSealSnapshot
