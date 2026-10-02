import LeanInformationAudit.Contract.InterfaceGuard
import LeanInformationAudit.Contract.Discovery
import LeanInformationAuditRegTests.ContractBoundaryFixtures.InterfaceMacro
import LeanInformationAuditRegTests.ContractBoundaryFixtures.InterfaceRunMeta
import LeanInformationAuditRegTests.ContractBoundaryFixtures.InterfaceInitialize

import LeanInformationAuditRegTests.ContractBoundaryFixtures.InterfaceCompanionSpoof

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
run_meta do
  let owner := `LeanInformationAuditRegTests.ContractBoundaryFixtures.InterfaceCompanionSpoof
  let env := (← getEnv).setExporting false
  let source ← IO.FS.readFile (← LeanInformationAudit.Repository.source
    ("tools/lean-inspector/" ++ owner.toString.replace "." "/" ++ ".lean"))
  let entries ← SourceAudit.parse env source owner.toString
  let result := InterfaceGuard.audit env owner entries
  let rejected := match result with
    | .error e => e.startsWith "contract.interface:unattributed_command:"
    | .ok _ => false
  if rejected then logInfo "[PASS] interface.inventory.companion_name_spoof"
  else logError "[FAIL] interface.inventory.companion_name_spoof"
  logInfo m!"CONTRACT_DIAGNOSTIC {repr result}"
end LeanInformationAuditRegTests.ContractInterfaceInventory
