import LeanInformationAuditContract.Catalog
open Lean LeanInformationAudit
namespace LeanInformationAuditRegTests.ContractPathFixtures.Reg.Catalogs.DuplicateSeal.SealedCatalog
def catalog : Contract.RootCatalog := { data := {
  rootId := `LeanInformationAuditRegTests.ContractPathFixtures.Reg.Catalogs.DuplicateSeal.SealedCatalog
  expected := #[]
  source := #[]
  baseline := #[]
  companionPrefix := none } }
def sealEntry : Contract.Seal := { rootId := `LeanInformationAuditRegTests.ContractPathFixtures.Reg.Catalogs.DuplicateSeal.SealedCatalog, options := #[] }
def seal2 : Contract.Seal := { rootId := `LeanInformationAuditRegTests.ContractPathFixtures.Reg.Catalogs.DuplicateSeal.SealedCatalog, options := #[] }
end LeanInformationAuditRegTests.ContractPathFixtures.Reg.Catalogs.DuplicateSeal.SealedCatalog
