import LeanInformationAuditInterface.Contract.Catalog

namespace LeanInformationAuditRegTests.ContractNegativeFixtures.Computed
def bad : LeanInformationAudit.Contract.Seal.{0,0} := (fun x => x) { rootId := Lean.Name.anonymous, catalogs := #[], options := #[] }
end LeanInformationAuditRegTests.ContractNegativeFixtures.Computed
