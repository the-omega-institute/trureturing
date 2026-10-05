import LeanInformationAuditInterface.Contract.Catalog
open Lean Meta Elab Tactic

namespace LeanInformationAuditRegTests.ContractLiteralFixtures.Environment
def computedMetadata : LeanInformationAudit.Contract.Seal.{0,0} := {
  rootId := by
    run_tac do
      let env ← getEnv
      closeMainGoal `computedMetadata (toExpr env.header.mainModule)
  catalogs := #[], options := #[] }
end LeanInformationAuditRegTests.ContractLiteralFixtures.Environment
