import LeanInformationAuditInterface.Contract.Catalog
open Lean Meta Elab Term
namespace LeanInformationAudit
private def markArenaConstruction (elaborator : TermElab) : TermElab := fun stx expected => do
  let value ← elaborator stx expected
  if value.isAppOfArity ``Contract.Seal.mk 3 then
    let env ← getEnv
    return mkApp3 value.getAppFn (toExpr env.header.mainModule)
      value.getAppArgs[1]! value.getAppArgs[2]!
  return value
@[term_elab Lean.Parser.Term.structInst]
private def elabArenaConstruction : TermElab :=
  markArenaConstruction Lean.Elab.Term.StructInst.elabStructInst
end LeanInformationAudit
namespace Boundary.DelegateForgery
def entry : LeanInformationAudit.Contract.Seal.{0,0} := { rootId := `root, catalogs := #[], options := #[] }
end Boundary.DelegateForgery
