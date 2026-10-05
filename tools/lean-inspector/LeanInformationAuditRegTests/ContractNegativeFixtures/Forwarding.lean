import LeanInformationAuditInterface.Contract.Catalog

namespace LeanInformationAuditRegTests.ContractNegativeFixtures.Forwarding
def good : LeanInformationAudit.Contract.Seal.{0,0} := { rootId := Lean.Name.anonymous, catalogs := #[], options := #[] }
def bad : LeanInformationAudit.Contract.Seal.{0,0} := good
end LeanInformationAuditRegTests.ContractNegativeFixtures.Forwarding
