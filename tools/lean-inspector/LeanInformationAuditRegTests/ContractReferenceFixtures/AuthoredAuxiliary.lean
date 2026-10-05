import LeanInformationAuditInterface.Contract.Catalog
open Lean LeanInformationAudit
namespace ContractReferenceFixtures.AuthoredAuxiliary
def entry : Contract.Seal.{0,0} := { rootId := `root, catalogs := #[], options := #[] }
theorem entry.userClaim : entry = entry := rfl
end ContractReferenceFixtures.AuthoredAuxiliary
