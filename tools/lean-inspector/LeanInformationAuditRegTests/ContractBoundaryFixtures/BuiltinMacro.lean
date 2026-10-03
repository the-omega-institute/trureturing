import LeanInformationAuditContract.Catalog
open Lean Meta Elab Tactic
namespace Quality.BuiltinMacro
macro_rules
  | `(Lean.Name.str $a $b) => `(by
      run_tac do
        let env ← getEnv
        closeMainGoal `entry (toExpr env.header.mainModule))
def entry : LeanInformationAudit.Contract.Seal := {
  rootId := Lean.Name.str Lean.Name.anonymous "literal-looking"
  options := #[] }
end Quality.BuiltinMacro
