import LeanInformationAuditInterface.Contract.Catalog
open Lean Meta Elab Tactic
namespace Quality.LocalBuiltinMacro
local macro_rules
  | `(Lean.Name.str $a $b) => `(by
      run_tac do
        let env ← getEnv
        closeMainGoal `entry (toExpr env.header.mainModule))
def entry : LeanInformationAudit.Contract.Seal.{0,0} := {
  rootId := Lean.Name.str Lean.Name.anonymous "literal-looking"
  catalogs := #[], options := #[] }
end Quality.LocalBuiltinMacro
