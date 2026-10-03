import LeanInformationAuditInterface.Contract.Catalog
open Lean LeanInformationAudit
namespace ContractReferenceFixtures.AuthoredAuxiliary
def entry : Contract.Seal := { rootId := `root, options := #[] }
theorem entry.userClaim : entry = entry := rfl
end ContractReferenceFixtures.AuthoredAuxiliary
