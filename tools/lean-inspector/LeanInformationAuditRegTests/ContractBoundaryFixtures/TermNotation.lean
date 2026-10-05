import LeanInformationAuditInterface.Contract.Catalog
namespace Boundary.TermNotation
notation "metadataTerm" => (`root : Lean.Name)
def entry : LeanInformationAudit.Contract.Seal.{0,0} := { rootId := metadataTerm, catalogs := #[], options := #[] }
end Boundary.TermNotation
