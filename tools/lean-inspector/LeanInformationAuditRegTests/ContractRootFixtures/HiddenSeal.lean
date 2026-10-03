import LeanInformationAuditContract.Catalog
open Lean LeanInformationAudit
namespace ContractRootFixtures.HiddenSeal
def catalog : Contract.RootCatalog := { data := { rootId := `ContractRoot, expected := #[], source := #[], baseline := #[], companionPrefix := none } }
def sealEntry : (fun T : Type => T) Contract.Seal := { rootId := `ContractRoot, options := #[] }
end ContractRootFixtures.HiddenSeal
