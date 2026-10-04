import LeanInformationAuditRegTests.ContractDiscovery
import LeanInformationAuditRegTests.ContractLiteralFixtures.Environment
import LeanInformationAuditRegTests.ContractLiteralFixtures.Macro
import LeanInformationAuditRegTests.ContractLiteralFixtures.Reference
import LeanInformationAuditRegTests.ContractLiteralFixtures.Function
import LeanInformationAuditRegTests.ContractLiteralFixtures.Nested
import LeanInformationAuditRegTests.ContractLiteralFixtures.Literals

namespace LeanInformationAuditRegTests.ContractSourceLiteral
open Lean Meta Elab Command LeanInformationAudit.Contract
open LeanInformationAuditRegTests.ContractGuards

run_meta do
  let literals ← Discovery.discoverWithStructure #[] #[`LeanInformationAuditRegTests.ContractLiteralFixtures.Literals]
    fun moduleName => LeanInformationAudit.Repository.source
      ("tools/lean-inspector/" ++ moduleName.toString.replace "." "/" ++ ".lean")
  let some (_, row) := literals.seals[0]? | throwError "setup: literal seal"
  assertTest "discovery.source_literal.constructors"
    (row.rootId == .str (.num .anonymous 7) "root" &&
      row.options.find? `test.integer == some (.ofInt (-5)))
  for (fixture, field) in #[("Environment", "rootId"), ("Macro", "rootId"),
      ("Reference", "rootId"), ("Function", "rootId"), ("Nested", "companionPrefix")] do
    let owner := (`LeanInformationAuditRegTests.ContractLiteralFixtures).str fixture
    let mut error := "accepted"
    try
      discard <| Discovery.discoverWithStructure #[] #[owner] fun moduleName =>
        LeanInformationAudit.Repository.source
          ("tools/lean-inspector/" ++ moduleName.toString.replace "." "/" ++ ".lean")
    catch ex => error := ← ex.toMessageData.toString
    assertTest s!"discovery.source_literal.{fixture}"
      (error.startsWith (if fixture == "Macro" then
        "contract.source_literal:term_expander:" else "contract.source_literal:nonliteral:") && (error.splitOn field).length > 1)
    logInfo m!"CONTRACT_DIAGNOSTIC discovery.source_literal.{fixture} {error}"

end LeanInformationAuditRegTests.ContractSourceLiteral
