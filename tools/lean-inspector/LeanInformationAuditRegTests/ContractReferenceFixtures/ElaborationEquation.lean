import LeanInformationAuditInterface.Contract.Catalog
open Lean LeanInformationAudit
namespace ContractReferenceFixtures.ElaborationEquation
def entry : Contract.Seal.{0,0} := { rootId := `root, catalogs := #[], options := #[] }
def helper : Unit := by_elab do
  let lhs := mkConst ``entry
  for suffix in #["eq_def", "eq_2"] do
    addDecl (.thmDecl {
      name := ``entry |>.str suffix
      levelParams := []
      type := ← Meta.mkEq lhs lhs
      value := ← Meta.mkEqRefl lhs })
  return mkConst ``Unit.unit
end ContractReferenceFixtures.ElaborationEquation
