import LeanInformationAuditRegTests.ContractGuards
import LeanInformationAuditRegTests.ContractNegativeFixtures.Parameters
import LeanInformationAuditRegTests.ContractNegativeFixtures.Forall
import LeanInformationAuditRegTests.ContractNegativeFixtures.Alias
import LeanInformationAuditRegTests.ContractNegativeFixtures.Wrapper
import LeanInformationAuditRegTests.ContractNegativeFixtures.Forwarding
import LeanInformationAuditRegTests.ContractNegativeFixtures.Computed
import LeanInformationAuditRegTests.ContractNegativeFixtures.Update
import LeanInformationAuditRegTests.ContractNegativeFixtures.Opaque
import LeanInformationAuditRegTests.ContractNegativeFixtures.Unsafe
import LeanInformationAuditRegTests.ContractNegativeFixtures.Abbrev
import LeanInformationAuditRegTests.ContractNegativeFixtures.Where

namespace LeanInformationAuditRegTests.ContractDiscoverNegative
open Lean Meta Elab Command LeanInformationAudit.Contract
open LeanInformationAuditRegTests.ContractGuards
run_meta do
  for (fixture, diagnostic) in #[
      ("Parameters", "reference"),
      ("Forall", "reference"),
      ("Alias", "reference"),
      ("Wrapper", "reference"),
      ("Forwarding", "forwarding_or_computed"),
      ("Computed", "forwarding_or_computed"),
      ("Update", "structure_update"),
      ("Opaque", "opaque"),
      ("Unsafe", "unsafe"),
      ("Abbrev", "not_def"),
      ("Where", "structure_literal")] do
    let owner := (`LeanInformationAuditRegTests.ContractNegativeFixtures).str fixture
    let mut error := "accepted"
    try
      discard <| Discovery.discover #[owner] fun moduleName =>
        LeanInformationAudit.Repository.source
          ("tools/lean-inspector/" ++ moduleName.toString.replace "." "/" ++ ".lean")
    catch ex => error := ← ex.toMessageData.toString
    assertTest s!"discovery.negative.{fixture}" (error.startsWith (if diagnostic == "reference" then
        "contract.reg:contract_reference_outside_entry:" else "contract.discovery:" ++ diagnostic))
    logInfo m!"CONTRACT_DIAGNOSTIC discovery.negative.{fixture} {error}"
end LeanInformationAuditRegTests.ContractDiscoverNegative
