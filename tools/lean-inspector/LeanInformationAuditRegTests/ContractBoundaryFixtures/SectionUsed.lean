import LeanInformationAuditInterface.Contract.Catalog
namespace LeanInformationAuditRegTests.ReviewBoundaryFixtures.SectionUsed
section
variable (n : Nat)
def literal : LeanInformationAudit.Contract.Seal := { rootId := .num .anonymous n, options := #[] }
end
end LeanInformationAuditRegTests.ReviewBoundaryFixtures.SectionUsed
