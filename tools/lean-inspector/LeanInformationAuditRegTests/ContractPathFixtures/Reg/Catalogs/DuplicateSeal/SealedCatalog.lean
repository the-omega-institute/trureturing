import LeanInformationAuditInterface.Contract.Catalog
open Lean LeanInformationAudit
namespace LeanInformationAuditRegTests.ContractPathFixtures.Reg.Catalogs.DuplicateSeal.SealedCatalog
def catalog : Contract.RootCatalog := { data := {
  rootId := `LeanInformationAuditRegTests.ContractPathFixtures.Reg.Catalogs.DuplicateSeal.SealedCatalog
  expected := #[]
  source := #[]
  baseline := #[]
  companionPrefix := none } }
def sealEntry : Contract.Seal.{0,0} := { rootId := `LeanInformationAuditRegTests.ContractPathFixtures.Reg.Catalogs.DuplicateSeal.SealedCatalog, catalogs := #[], options := #[] }
def seal2 : Contract.Seal.{0,0} := { rootId := `LeanInformationAuditRegTests.ContractPathFixtures.Reg.Catalogs.DuplicateSeal.SealedCatalog, catalogs := #[], options := #[] }
end LeanInformationAuditRegTests.ContractPathFixtures.Reg.Catalogs.DuplicateSeal.SealedCatalog
