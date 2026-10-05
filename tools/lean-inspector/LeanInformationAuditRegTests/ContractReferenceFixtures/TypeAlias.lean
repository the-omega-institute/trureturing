import LeanInformationAuditInterface.Contract.Catalog
open Lean LeanInformationAudit
namespace ContractReferenceFixtures.TypeAlias
def Alias := Contract.Seal
def value : Alias := { rootId := `root, catalogs := #[], options := #[] }
end ContractReferenceFixtures.TypeAlias
