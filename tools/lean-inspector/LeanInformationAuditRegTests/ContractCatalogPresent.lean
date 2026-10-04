import LeanInformationAuditRegTests.ContractPathFixtures.Reg.Catalogs.Membership.RootCatalog
import LeanInformationAudit.Registry
import LeanInformationAuditRegTests.ContractCatalogLayout

namespace LeanInformationAuditRegTests.ContractCatalogPresent
open Lean Meta

run_meta do
  let env := ContractControl.kernelEnvironment (← getEnv)
  unless env.header.trustLevel == 0 && env.toKernelEnv.header.trustLevel == 0 do
    throwError "[FAIL] control.kernel_trust.present"
  let value ← withEnv (env.setExporting false) <|
    withOptions (fun _ => ({} : Options)) <| ContractCatalogLayout.snapshot true
  ContractControl.publish `LeanInformationAuditRegTests.ContractCatalogPresent.result value

end LeanInformationAuditRegTests.ContractCatalogPresent
