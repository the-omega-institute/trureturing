import LeanInformationAuditInterface.Contract.Catalog
namespace Boundary.TermElab
elab "metadataTerm" : term => return Lean.toExpr (`root : Lean.Name)
def entry : LeanInformationAudit.Contract.Seal.{0,0} := { rootId := metadataTerm, catalogs := #[], options := #[] }
end Boundary.TermElab
