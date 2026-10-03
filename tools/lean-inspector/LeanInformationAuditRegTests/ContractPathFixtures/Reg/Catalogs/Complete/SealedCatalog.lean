import LeanInformationAuditContract.Catalog
open Lean LeanInformationAudit
namespace LeanInformationAuditRegTests.ContractPathFixtures.Reg.Catalogs.Complete.SealedCatalog
def catalog : Contract.RootCatalog := { data := {
  rootId := `LeanInformationAuditRegTests.ContractPathFixtures.Reg.Catalogs.Complete.SealedCatalog
  expected := #[]
  source := #[]
  baseline := #[]
  companionPrefix := none } }
def sealEntry : Contract.Seal := { rootId := `LeanInformationAuditRegTests.ContractPathFixtures.Reg.Catalogs.Complete.SealedCatalog, options := #[] }
end LeanInformationAuditRegTests.ContractPathFixtures.Reg.Catalogs.Complete.SealedCatalog
