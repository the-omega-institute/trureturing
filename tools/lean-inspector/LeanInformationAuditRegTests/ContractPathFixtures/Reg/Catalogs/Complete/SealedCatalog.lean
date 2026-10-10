import LeanInformationAuditInterface.Contract.Catalog
open Lean LeanInformationAudit
namespace LeanInformationAuditRegTests.ContractPathFixtures.Reg.Catalogs.Complete.SealedCatalog
def catalog : Contract.RootCatalog := { data := {
  rootId := `LeanInformationAuditRegTests.ContractPathFixtures.Reg.Catalogs.Complete.SealedCatalog
  expected := #[]
  source := #[]
  baseline := #[]
  companionPrefix := none } }
def sealEntry : Contract.Seal.{0,0} := { rootId := `LeanInformationAuditRegTests.ContractPathFixtures.Reg.Catalogs.Complete.SealedCatalog, catalogs := #[], options := #[] }
end LeanInformationAuditRegTests.ContractPathFixtures.Reg.Catalogs.Complete.SealedCatalog
