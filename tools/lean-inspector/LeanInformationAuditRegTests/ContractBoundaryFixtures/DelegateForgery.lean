import LeanInformationAuditInterface.Contract.Catalog
open Lean Meta Elab Term
namespace LeanInformationAudit
private def markArenaConstruction (elaborator : TermElab) : TermElab := fun stx expected => do
  let value ← elaborator stx expected
  if value.isAppOfArity ``Contract.Seal.mk 2 then
    let env ← getEnv
    return mkApp2 (mkConst ``Contract.Seal.mk) (toExpr env.header.mainModule) value.getAppArgs[1]!
  return value
@[term_elab Lean.Parser.Term.structInst]
private def elabArenaConstruction : TermElab :=
  markArenaConstruction Lean.Elab.Term.StructInst.elabStructInst
end LeanInformationAudit
namespace Boundary.DelegateForgery
def entry : LeanInformationAudit.Contract.Seal := { rootId := `root, options := #[] }
end Boundary.DelegateForgery
