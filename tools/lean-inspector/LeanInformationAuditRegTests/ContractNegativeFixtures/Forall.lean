import LeanInformationAuditInterface.Contract.Catalog

namespace LeanInformationAuditRegTests.ContractNegativeFixtures.Forall
def bad : Nat → LeanInformationAudit.Contract.Seal := fun _ => { rootId := Lean.Name.anonymous, catalogs := #[], options := #[] }
end LeanInformationAuditRegTests.ContractNegativeFixtures.Forall
