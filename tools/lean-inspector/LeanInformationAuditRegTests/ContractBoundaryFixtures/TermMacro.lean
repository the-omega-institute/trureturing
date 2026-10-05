import LeanInformationAuditInterface.Contract.Catalog
namespace Boundary.TermMacro
macro "metadataTerm" : term => `(`root)
def entry : LeanInformationAudit.Contract.Seal.{0,0} := { rootId := metadataTerm, catalogs := #[], options := #[] }
end Boundary.TermMacro
