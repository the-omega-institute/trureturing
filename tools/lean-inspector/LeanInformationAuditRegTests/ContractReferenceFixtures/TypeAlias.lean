import LeanInformationAuditContract.Catalog
open Lean LeanInformationAudit
namespace ContractReferenceFixtures.TypeAlias
def Alias := Contract.Seal
def value : Alias := { rootId := `root, options := #[] }
end ContractReferenceFixtures.TypeAlias
