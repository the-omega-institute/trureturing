import LeanInformationAuditContract.Catalog
namespace Boundary.TermElab
elab "metadataTerm" : term => return Lean.toExpr (`root : Lean.Name)
def entry : LeanInformationAudit.Contract.Seal := { rootId := metadataTerm, options := #[] }
end Boundary.TermElab
