import LeanInformationAuditInterface.Contract.Catalog
open Lean LeanInformationAudit
namespace ContractRootFixtures.WrongSealOwner
def catalog : Contract.RootCatalog := { data := { rootId := `ContractRoot, expected := #[], source := #[], baseline := #[], companionPrefix := none } }
def sealEntry : Contract.Seal := { rootId := `OtherRoot, options := #[] }
end ContractRootFixtures.WrongSealOwner
