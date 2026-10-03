import LeanInformationAuditContract.Catalog
open Lean LeanInformationAudit
namespace ContractRootFixtures.UnexpectedCatalog
def catalog : Contract.RootCatalog := { data := { rootId := `ContractRoot, expected := #[], source := #[], baseline := #[], companionPrefix := none } }
end ContractRootFixtures.UnexpectedCatalog
