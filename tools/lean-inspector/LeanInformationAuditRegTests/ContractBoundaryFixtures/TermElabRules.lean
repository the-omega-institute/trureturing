import LeanInformationAuditContract.Catalog
namespace Boundary.TermElabRules
syntax "metadataTerm" : term
elab_rules : term | `(metadataTerm) => return Lean.toExpr (`root : Lean.Name)
def entry : LeanInformationAudit.Contract.Seal := { rootId := metadataTerm, options := #[] }
end Boundary.TermElabRules
