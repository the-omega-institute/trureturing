import LeanInformationAuditContract.Catalog
open Lean LeanInformationAudit
namespace LeanInformationAuditRegTests.ContractPathFixtures.Reg.Catalogs.DuplicateCatalog.RootCatalog
def catalog : Contract.RootCatalog := { data := {
  rootId := `LeanInformationAuditRegTests.ContractPathFixtures.Reg.Catalogs.DuplicateCatalog.RootCatalog
  expected := #[]
  source := #[]
  baseline := #[]
  companionPrefix := none } }
def catalog2 : Contract.RootCatalog := { data := {
  rootId := `LeanInformationAuditRegTests.ContractPathFixtures.Reg.Catalogs.DuplicateCatalog.RootCatalog
  expected := #[]
  source := #[]
  baseline := #[]
  companionPrefix := none } }
end LeanInformationAuditRegTests.ContractPathFixtures.Reg.Catalogs.DuplicateCatalog.RootCatalog
