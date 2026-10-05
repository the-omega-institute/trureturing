import LeanInformationAuditInterface.Contract.Catalog
namespace LeanInformationAuditRegTests.ReviewBoundaryFixtures.SectionUnused
section
variable (n : Nat)
def literal : LeanInformationAudit.Contract.Seal.{0,0} := { rootId := `Review.root, catalogs := #[], options := #[] }
end
end LeanInformationAuditRegTests.ReviewBoundaryFixtures.SectionUnused
