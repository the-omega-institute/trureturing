import LeanInformationAuditInterface.Contract.Catalog
open Lean LeanInformationAudit
namespace ContractReferenceFixtures.Projection
def entry : Contract.Seal.{0,0} := { rootId := `root, catalogs := #[], options := #[] }
def value : Nat := entry.options.size
end ContractReferenceFixtures.Projection
