import LeanInformationAuditInterface.Contract.Catalog
open Lean LeanInformationAudit
namespace ContractReferenceFixtures.TypeLet
def value : (let T := Contract.Seal; T) := { rootId := `root, options := #[] }
end ContractReferenceFixtures.TypeLet
