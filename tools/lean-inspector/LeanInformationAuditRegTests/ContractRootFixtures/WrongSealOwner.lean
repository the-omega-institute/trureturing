import LeanInformationAuditInterface.Contract.Catalog
open Lean LeanInformationAudit
namespace ContractRootFixtures.WrongSealOwner
def catalog : Contract.RootCatalog := { data := { rootId := `ContractRoot, expected := #[], source := #[], baseline := #[], companionPrefix := none } }
def sealEntry : Contract.Seal.{0,0} := { rootId := `OtherRoot, catalogs := #[], options := #[] }
end ContractRootFixtures.WrongSealOwner
