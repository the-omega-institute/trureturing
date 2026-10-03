import LeanInformationAuditContract.Catalog
open Lean LeanInformationAudit
namespace ContractRootFixtures.Complete
def catalog : Contract.RootCatalog := { data := { rootId := `ContractRoot, expected := #[], source := #[], baseline := #[], companionPrefix := none } }
def sealEntry : Contract.Seal := { rootId := `ContractRoot, options := #[] }
end ContractRootFixtures.Complete
