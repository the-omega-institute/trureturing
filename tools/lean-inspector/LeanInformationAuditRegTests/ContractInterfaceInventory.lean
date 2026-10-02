import LeanInformationAudit.Contract.InterfaceGuard
import LeanInformationAudit.Contract.Discovery
import LeanInformationAuditRegTests.ContractBoundaryFixtures.InterfaceMacro
import LeanInformationAuditRegTests.ContractBoundaryFixtures.InterfaceRunMeta
import LeanInformationAuditRegTests.ContractBoundaryFixtures.InterfaceInitialize

namespace LeanInformationAuditRegTests.ContractInterfaceInventory
open Lean Meta Elab Command LeanInformationAudit.Contract
run_meta do
  for fixture in #["InterfaceMacro", "InterfaceRunMeta", "InterfaceInitialize"] do
    let owner := (`LeanInformationAuditRegTests.ContractBoundaryFixtures).str fixture
    let env := (← getEnv).setExporting false
    let source ← IO.FS.readFile (← LeanInformationAudit.Repository.source
      ("tools/lean-inspector/" ++ owner.toString.replace "." "/" ++ ".lean"))
    let entries ← SourceAudit.parse env source owner.toString
    let result := InterfaceGuard.audit env owner entries
    let ok := match result with
      | .error e => e.startsWith "contract.interface:compiled_non_type:"
      | .ok _ => false
    if ok then logInfo m!"[PASS] interface.inventory.{fixture}"
    else logError m!"[FAIL] interface.inventory.{fixture}"
    logInfo m!"CONTRACT_DIAGNOSTIC {repr result}"
end LeanInformationAuditRegTests.ContractInterfaceInventory
