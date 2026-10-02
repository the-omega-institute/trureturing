import LeanInformationAuditRegTests.ContractDiscovery
import LeanInformationAuditRegTests.ContractLiteralFixtures.Environment
import LeanInformationAuditRegTests.ContractLiteralFixtures.Macro
import LeanInformationAuditRegTests.ContractLiteralFixtures.Reference
import LeanInformationAuditRegTests.ContractLiteralFixtures.Function
import LeanInformationAuditRegTests.ContractLiteralFixtures.Nested

namespace LeanInformationAuditRegTests.ContractSourceLiteral
open Lean Meta Elab Command LeanInformationAudit.Contract
open LeanInformationAuditRegTests.ContractGuards

run_meta do
  for (fixture, field) in #[("Environment", "rootId"), ("Macro", "rootId"),
      ("Reference", "rootId"), ("Function", "rootId"), ("Nested", "companionPrefix")] do
    let owner := (`LeanInformationAuditRegTests.ContractLiteralFixtures).str fixture
    let mut error := "accepted"
    try
      discard <| Discovery.discover #[owner] fun moduleName =>
        LeanInformationAudit.Repository.source
          ("tools/lean-inspector/" ++ moduleName.toString.replace "." "/" ++ ".lean")
    catch ex => error := ← ex.toMessageData.toString
    assertTest s!"discovery.source_literal.{fixture}"
      (error.startsWith "contract.source_literal:nonliteral:" && (error.splitOn field).length > 1)
    logInfo m!"CONTRACT_DIAGNOSTIC discovery.source_literal.{fixture} {error}"

end LeanInformationAuditRegTests.ContractSourceLiteral
