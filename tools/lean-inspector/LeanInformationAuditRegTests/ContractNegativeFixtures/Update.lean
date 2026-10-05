import LeanInformationAuditInterface.Contract.Catalog

namespace LeanInformationAuditRegTests.ContractNegativeFixtures.Update
def good : LeanInformationAudit.Contract.Seal.{0,0} := { rootId := Lean.Name.anonymous, catalogs := #[], options := #[] }
def bad : LeanInformationAudit.Contract.Seal.{0,0} := { good with rootId := .anonymous }
end LeanInformationAuditRegTests.ContractNegativeFixtures.Update
