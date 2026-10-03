import LeanInformationAuditInterface.Contract.Catalog
open Lean LeanInformationAudit
namespace LeanInformationAuditRegTests.ContractPathFixtures.Reg.Catalogs.UnexpectedSeal.RootCatalog
def catalog : Contract.RootCatalog := { data := {
  rootId := `LeanInformationAuditRegTests.ContractPathFixtures.Reg.Catalogs.UnexpectedSeal.RootCatalog
  expected := #[]
  source := #[]
  baseline := #[]
  companionPrefix := none } }
def sealEntry : Contract.Seal := { rootId := `LeanInformationAuditRegTests.ContractPathFixtures.Reg.Catalogs.UnexpectedSeal.RootCatalog, options := #[] }
end LeanInformationAuditRegTests.ContractPathFixtures.Reg.Catalogs.UnexpectedSeal.RootCatalog
