import LeanInformationAuditInterface.Contract.Catalog
open Lean LeanInformationAudit
namespace ContractRootFixtures.HiddenCatalog
def catalog : (fun T : Type _ => T) Contract.RootCatalog := { data := { rootId := `ContractRoot, expected := #[], source := #[], baseline := #[], companionPrefix := none } }
def sealEntry : Contract.Seal.{0,0} := { rootId := `ContractRoot, catalogs := #[], options := #[] }
end ContractRootFixtures.HiddenCatalog
