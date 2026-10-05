import LeanInformationAuditInterface.Contract.Catalog
open Lean LeanInformationAudit
namespace ContractReferenceFixtures.ElaborationChild
def entry : Contract.Seal.{0,0} := { rootId := `root, catalogs := #[], options := #[] }
def helper : Unit := by_elab do
  addDecl (.defnDecl {
    name := `ContractReferenceFixtures.ElaborationChild.entry.generated
    levelParams := []
    type := mkConst ``Contract.Seal [.zero, .zero]
    value := mkConst ``entry
    hints := .abbrev
    safety := .safe })
  return mkConst ``Unit.unit
end ContractReferenceFixtures.ElaborationChild
