import LeanInformationAuditInterface.Contract.Catalog

namespace LeanInformationAuditRegTests.ContractNegativeFixtures.Unsafe
unsafe def bad : LeanInformationAudit.Contract.Seal := { rootId := Lean.Name.anonymous, options := #[] }
end LeanInformationAuditRegTests.ContractNegativeFixtures.Unsafe
