import LeanInformationAuditInterface.Contract.Catalog

namespace LeanInformationAuditRegTests.ContractNegativeFixtures.Forwarding
def good : LeanInformationAudit.Contract.Seal := { rootId := Lean.Name.anonymous, options := #[] }
def bad : LeanInformationAudit.Contract.Seal := good
end LeanInformationAuditRegTests.ContractNegativeFixtures.Forwarding
