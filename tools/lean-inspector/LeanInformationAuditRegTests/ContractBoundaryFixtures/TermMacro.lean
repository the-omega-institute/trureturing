import LeanInformationAuditInterface.Contract.Catalog
namespace Boundary.TermMacro
macro "metadataTerm" : term => `(`root)
def entry : LeanInformationAudit.Contract.Seal := { rootId := metadataTerm, options := #[] }
end Boundary.TermMacro
