import LeanInformationAuditInterface.Contract.Catalog
open Lean LeanInformationAudit
namespace ContractRootFixtures.DuplicateSeal
def catalog : Contract.RootCatalog := { data := { rootId := `ContractRoot, expected := #[], source := #[], baseline := #[], companionPrefix := none } }
def sealEntry : Contract.Seal := { rootId := `ContractRoot, options := #[] }
def second : Contract.Seal := { rootId := `ContractRoot, options := #[] }
end ContractRootFixtures.DuplicateSeal
