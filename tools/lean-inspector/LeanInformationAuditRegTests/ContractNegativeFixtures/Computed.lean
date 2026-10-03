import LeanInformationAuditContract.Catalog

namespace LeanInformationAuditRegTests.ContractNegativeFixtures.Computed
def bad : LeanInformationAudit.Contract.Seal := (fun x => x) { rootId := Lean.Name.anonymous, options := #[] }
end LeanInformationAuditRegTests.ContractNegativeFixtures.Computed
