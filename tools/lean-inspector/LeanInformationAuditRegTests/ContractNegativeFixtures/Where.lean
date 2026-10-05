import LeanInformationAuditInterface.Contract.Catalog

namespace LeanInformationAuditRegTests.ContractNegativeFixtures.Where
def bad : LeanInformationAudit.Contract.Seal.{0,0} where
  rootId := .anonymous
  catalogs := #[]
  options := #[]
end LeanInformationAuditRegTests.ContractNegativeFixtures.Where
