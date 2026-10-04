import LeanInformationAuditRegTests.ContractPathFixtures.Reg.D5.Mirror.RootCatalog
import LeanInformationAudit.Registry
import LeanInformationAuditRegTests.ContractCatalogLayout

namespace LeanInformationAuditRegTests.ContractCatalogAbsent
open Lean Meta

run_meta do
  let env := ContractControl.kernelEnvironment (← getEnv)
  unless env.header.trustLevel == 0 && env.toKernelEnv.header.trustLevel == 0 do
    throwError "[FAIL] control.kernel_trust.absent"
  let value ← withEnv (env.setExporting false) <|
    withOptions (fun _ => ({} : Options)) <| ContractCatalogLayout.snapshot false
  ContractControl.publish `LeanInformationAuditRegTests.ContractCatalogAbsent.result value

end LeanInformationAuditRegTests.ContractCatalogAbsent
