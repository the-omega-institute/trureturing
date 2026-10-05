import LeanInformationAuditInterface.Contract.Catalog
open Lean LeanInformationAudit
namespace ContractReferenceFixtures.StoredType
structure Box where
  T : Type 1
def box : Box := ⟨Contract.Seal.{0,0}⟩
def value : box.T := { rootId := `root, catalogs := #[], options := #[] }
end ContractReferenceFixtures.StoredType
