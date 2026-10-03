import LeanInformationAuditContract.Catalog
open Lean LeanInformationAudit
namespace ContractReferenceFixtures.Projection
def entry : Contract.Seal := { rootId := `root, options := #[] }
def value : Nat := entry.options.size
end ContractReferenceFixtures.Projection
