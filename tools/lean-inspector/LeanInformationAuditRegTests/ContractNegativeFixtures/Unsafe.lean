import LeanInformationAuditInterface.Contract.Catalog

namespace LeanInformationAuditRegTests.ContractNegativeFixtures.Unsafe
unsafe def bad : LeanInformationAudit.Contract.Seal.{0,0} := { rootId := Lean.Name.anonymous, catalogs := #[], options := #[] }
end LeanInformationAuditRegTests.ContractNegativeFixtures.Unsafe
