import LeanInformationAuditInterface.Contract.Catalog
open Lean LeanInformationAudit
namespace ContractReferenceFixtures.NestedDeclaration
def entry : Contract.Seal.{0,0} := { rootId := `root, catalogs := #[], options := #[] }
where
  child : Contract.Seal.{0,0} := { rootId := `root, catalogs := #[], options := #[] }
end ContractReferenceFixtures.NestedDeclaration
