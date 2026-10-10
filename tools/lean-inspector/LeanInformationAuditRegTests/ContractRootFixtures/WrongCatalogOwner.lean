import LeanInformationAuditInterface.Contract.Catalog
open Lean LeanInformationAudit
namespace ContractRootFixtures.WrongCatalogOwner
def catalog : Contract.RootCatalog := { data := { rootId := `OtherRoot, expected := #[], source := #[], baseline := #[], companionPrefix := none } }
def sealEntry : Contract.Seal.{0,0} := { rootId := `ContractRoot, catalogs := #[], options := #[] }
end ContractRootFixtures.WrongCatalogOwner
