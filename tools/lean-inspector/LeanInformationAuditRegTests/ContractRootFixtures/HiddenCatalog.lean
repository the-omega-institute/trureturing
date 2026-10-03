import LeanInformationAuditInterface.Contract.Catalog
open Lean LeanInformationAudit
namespace ContractRootFixtures.HiddenCatalog
def catalog : (fun T : Type => T) Contract.RootCatalog := { data := { rootId := `ContractRoot, expected := #[], source := #[], baseline := #[], companionPrefix := none } }
def sealEntry : Contract.Seal := { rootId := `ContractRoot, options := #[] }
end ContractRootFixtures.HiddenCatalog
