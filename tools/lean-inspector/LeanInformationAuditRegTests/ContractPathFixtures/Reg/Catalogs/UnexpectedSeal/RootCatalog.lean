import LeanInformationAuditInterface.Contract.Catalog
open Lean LeanInformationAudit
namespace LeanInformationAuditRegTests.ContractPathFixtures.Reg.Catalogs.UnexpectedSeal.RootCatalog
def catalog : Contract.RootCatalog := { data := {
  rootId := `LeanInformationAuditRegTests.ContractPathFixtures.Reg.Catalogs.UnexpectedSeal.RootCatalog
  expected := #[]
  source := #[]
  baseline := #[]
  companionPrefix := none } }
def sealEntry : Contract.Seal.{0,0} := { rootId := `LeanInformationAuditRegTests.ContractPathFixtures.Reg.Catalogs.UnexpectedSeal.RootCatalog, catalogs := #[], options := #[] }
end LeanInformationAuditRegTests.ContractPathFixtures.Reg.Catalogs.UnexpectedSeal.RootCatalog
