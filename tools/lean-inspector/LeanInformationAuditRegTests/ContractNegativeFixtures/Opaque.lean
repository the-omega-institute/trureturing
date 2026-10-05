import LeanInformationAuditInterface.Contract.Catalog

namespace LeanInformationAuditRegTests.ContractNegativeFixtures.Opaque
opaque bad : LeanInformationAudit.Contract.Seal.{0,0} := { rootId := Lean.Name.anonymous, catalogs := #[], options := #[] }
end LeanInformationAuditRegTests.ContractNegativeFixtures.Opaque
