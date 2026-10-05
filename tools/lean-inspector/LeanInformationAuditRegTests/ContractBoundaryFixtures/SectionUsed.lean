import LeanInformationAuditInterface.Contract.Catalog
namespace LeanInformationAuditRegTests.ReviewBoundaryFixtures.SectionUsed
section
variable (n : Nat)
def literal : LeanInformationAudit.Contract.Seal.{0,0} := { rootId := .num .anonymous n, catalogs := #[], options := #[] }
end
end LeanInformationAuditRegTests.ReviewBoundaryFixtures.SectionUsed
