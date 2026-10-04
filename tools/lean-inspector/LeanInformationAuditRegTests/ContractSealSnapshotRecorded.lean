import Reg.Catalogs.PointwiseDisequalityRegistrations.SealedCatalog
import LeanInformationAuditRegTests.ContractSealSnapshotLayout

namespace LeanInformationAuditRegTests.ContractSealSnapshotRecorded
open Lean Meta

run_meta do
  let env := ContractControl.kernelEnvironment (← getEnv)
  unless env.header.trustLevel == 0 && env.toKernelEnv.header.trustLevel == 0 do
    throwError "[FAIL] control.kernel_trust.recorded"
  let value ← withEnv (env.setExporting false) <|
    withOptions (fun _ => (({} : Options).set `maxRecDepth (100000 : Nat)).set
      `maxHeartbeats (2000000 : Nat)) <|
      ContractSealSnapshotLayout.snapshot `Reg.Catalogs.PointwiseDisequalityRegistrations.SealedCatalog
  ContractControl.publish `LeanInformationAuditRegTests.ContractSealSnapshotRecorded.result value

end LeanInformationAuditRegTests.ContractSealSnapshotRecorded
