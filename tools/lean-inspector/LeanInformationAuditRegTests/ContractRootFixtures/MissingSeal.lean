import LeanInformationAuditContract.Catalog
open Lean LeanInformationAudit
namespace ContractRootFixtures.MissingSeal
def catalog : Contract.RootCatalog := { data := { rootId := `ContractRoot, expected := #[], source := #[], baseline := #[], companionPrefix := none } }
end ContractRootFixtures.MissingSeal
