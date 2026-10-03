import LeanInformationAuditInterface.Contract.Catalog
open Lean LeanInformationAudit
namespace ContractReferenceFixtures.NestedDeclaration
def entry : Contract.Seal := { rootId := `root, options := #[] }
where
  child : Contract.Seal := { rootId := `root, options := #[] }
end ContractReferenceFixtures.NestedDeclaration
