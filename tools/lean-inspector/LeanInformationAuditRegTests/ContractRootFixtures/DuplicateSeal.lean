import LeanInformationAuditInterface.Contract.Catalog
open Lean LeanInformationAudit
namespace ContractRootFixtures.DuplicateSeal
def catalog : Contract.RootCatalog := { data := { rootId := `ContractRoot, expected := #[], source := #[], baseline := #[], companionPrefix := none } }
def sealEntry : Contract.Seal.{0,0} := { rootId := `ContractRoot, catalogs := #[], options := #[] }
def second : Contract.Seal.{0,0} := { rootId := `ContractRoot, catalogs := #[], options := #[] }
end ContractRootFixtures.DuplicateSeal
