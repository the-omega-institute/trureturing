import LeanInformationAuditContract.Catalog

namespace LeanInformationAuditRegTests.ContractNegativeFixtures.Parameters
def bad (n : Nat) : LeanInformationAudit.Contract.Seal := { rootId := .num .anonymous n, options := #[] }
end LeanInformationAuditRegTests.ContractNegativeFixtures.Parameters
