import LeanInformationAuditRegTests.ContractSealFixtures.Reg.Catalogs.PointwiseDisequality.SealedCatalog
import LeanInformationAuditRegTests.ContractSealSnapshotLayout

namespace LeanInformationAuditRegTests.ContractSealSnapshotTyped
open Lean Meta

run_meta do
  let env := ContractControl.kernelEnvironment (← getEnv)
  unless env.header.trustLevel == 0 && env.toKernelEnv.header.trustLevel == 0 do
    throwError "[FAIL] control.kernel_trust.typed"
  let value ← withEnv (env.setExporting false) <|
    withOptions (fun _ => (({} : Options).set `maxRecDepth (100000 : Nat)).set
      `maxHeartbeats (2000000 : Nat)) <|
      ContractSealSnapshotLayout.snapshot `LeanInformationAuditRegTests.ContractSealFixtures.Reg.Catalogs.PointwiseDisequality.SealedCatalog
  ContractControl.publish `LeanInformationAuditRegTests.ContractSealSnapshotTyped.result value

end LeanInformationAuditRegTests.ContractSealSnapshotTyped
