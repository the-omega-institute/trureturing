import LeanInformationAuditContract.Catalog

namespace LeanInformationAuditRegTests.ContractNegativeFixtures.Update
def good : LeanInformationAudit.Contract.Seal := { rootId := Lean.Name.anonymous, options := #[] }
def bad : LeanInformationAudit.Contract.Seal := { good with rootId := .anonymous }
end LeanInformationAuditRegTests.ContractNegativeFixtures.Update
