import LeanInformationAuditInterface.Contract.Catalog

namespace LeanInformationAuditRegTests.ContractNegativeFixtures.Parameters
def bad (n : Nat) : LeanInformationAudit.Contract.Seal.{0,0} := { rootId := .num .anonymous n, catalogs := #[], options := #[] }
end LeanInformationAuditRegTests.ContractNegativeFixtures.Parameters
