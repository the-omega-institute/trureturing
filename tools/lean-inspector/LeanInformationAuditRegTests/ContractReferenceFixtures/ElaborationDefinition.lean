import LeanInformationAuditContract.Catalog
open Lean LeanInformationAudit
namespace ContractReferenceFixtures.ElaborationDefinition
def entry : Contract.Seal := { rootId := `root, options := #[] }
def helper : Unit := by_elab do
  let lhs := mkConst ``entry
  addDecl (.defnDecl {
    name := ``entry |>.str "eq_def"
    levelParams := []
    type := ← Meta.mkEq lhs lhs
    value := ← Meta.mkEqRefl lhs
    hints := .abbrev
    safety := .safe })
  return mkConst ``Unit.unit
end ContractReferenceFixtures.ElaborationDefinition
