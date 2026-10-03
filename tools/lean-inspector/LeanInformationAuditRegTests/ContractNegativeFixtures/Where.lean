import LeanInformationAuditContract.Catalog

namespace LeanInformationAuditRegTests.ContractNegativeFixtures.Where
def bad : LeanInformationAudit.Contract.Seal where
  rootId := .anonymous
  options := #[]
end LeanInformationAuditRegTests.ContractNegativeFixtures.Where
