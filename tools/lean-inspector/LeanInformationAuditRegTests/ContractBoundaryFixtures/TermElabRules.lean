import LeanInformationAuditInterface.Contract.Catalog
namespace Boundary.TermElabRules
syntax "metadataTerm" : term
elab_rules : term | `(metadataTerm) => return Lean.toExpr (`root : Lean.Name)
def entry : LeanInformationAudit.Contract.Seal.{0,0} := { rootId := metadataTerm, catalogs := #[], options := #[] }
end Boundary.TermElabRules
