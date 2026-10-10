import LeanInformationAuditInterface.Contract.Catalog
open Lean LeanInformationAudit
namespace ContractRootFixtures.HiddenSeal
def catalog : Contract.RootCatalog := { data := { rootId := `ContractRoot, expected := #[], source := #[], baseline := #[], companionPrefix := none } }
def sealEntry : (fun T : Type _ => T) Contract.Seal := { rootId := `ContractRoot, catalogs := #[], options := #[] }
end ContractRootFixtures.HiddenSeal
