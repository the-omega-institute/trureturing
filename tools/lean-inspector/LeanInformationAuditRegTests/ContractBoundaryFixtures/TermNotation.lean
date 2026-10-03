import LeanInformationAuditInterface.Contract.Catalog
namespace Boundary.TermNotation
notation "metadataTerm" => (`root : Lean.Name)
def entry : LeanInformationAudit.Contract.Seal := { rootId := metadataTerm, options := #[] }
end Boundary.TermNotation
