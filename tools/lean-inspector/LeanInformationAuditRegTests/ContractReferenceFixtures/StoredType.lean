import LeanInformationAuditInterface.Contract.Catalog
open Lean LeanInformationAudit
namespace ContractReferenceFixtures.StoredType
structure Box where
  T : Type
def box : Box := ⟨Contract.Seal⟩
def value : box.T := { rootId := `root, options := #[] }
end ContractReferenceFixtures.StoredType
