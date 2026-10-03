import LeanInformationAuditContract.Catalog
open Lean Meta Elab Tactic

namespace LeanInformationAuditRegTests.ContractLiteralFixtures.Environment
def computedMetadata : LeanInformationAudit.Contract.Seal := {
  rootId := by
    run_tac do
      let env ← getEnv
      closeMainGoal `computedMetadata (toExpr env.header.mainModule)
  options := #[] }
end LeanInformationAuditRegTests.ContractLiteralFixtures.Environment
