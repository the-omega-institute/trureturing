import LeanInformationAuditRegTests.ContractGuards
import LeanInformationAuditRegTests.ContractTypeCarrierFixture

namespace LeanInformationAuditRegTests.ContractTypeCarrier
open Lean Meta Elab Command LeanInformationAudit.Contract
open LeanInformationAuditRegTests.ContractGuards

run_meta do
  let mut error := "accepted"
  try
    discard <| Discovery.discoverWithStructure #[] #[`LeanInformationAuditRegTests.ContractTypeCarrierFixture]
      fun moduleName => LeanInformationAudit.Repository.source
        ("tools/lean-inspector/" ++ moduleName.toString.replace "." "/" ++ ".lean")
  catch ex => error := ← ex.toMessageData.toString
  assertTest "discovery.alias_through_type_carrier"
    (error.startsWith "contract.cannot_decode:")
  logInfo m!"CONTRACT_DIAGNOSTIC discovery.alias_through_type_carrier {error}"

end LeanInformationAuditRegTests.ContractTypeCarrier
