import LeanInformationAuditInterface.Contract.Catalog
open Lean LeanInformationAudit
namespace LeanInformationAuditRegTests.ContractPathFixtures.DuplicateCatalog.RootCatalog
def catalog : Contract.RootCatalog := { data := {
  rootId := `LeanInformationAuditRegTests.ContractPathFixtures.DuplicateCatalog.RootCatalog
  expected := #[]
  source := #[]
  baseline := #[]
  companionPrefix := none } }
def catalog2 : Contract.RootCatalog := { data := {
  rootId := `LeanInformationAuditRegTests.ContractPathFixtures.DuplicateCatalog.RootCatalog
  expected := #[]
  source := #[]
  baseline := #[]
  companionPrefix := none } }
end LeanInformationAuditRegTests.ContractPathFixtures.DuplicateCatalog.RootCatalog
