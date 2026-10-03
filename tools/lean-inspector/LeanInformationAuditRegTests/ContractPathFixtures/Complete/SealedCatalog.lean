import LeanInformationAuditInterface.Contract.Catalog
open Lean LeanInformationAudit
namespace LeanInformationAuditRegTests.ContractPathFixtures.Complete.SealedCatalog
def catalog : Contract.RootCatalog := { data := {
  rootId := `LeanInformationAuditRegTests.ContractPathFixtures.Complete.SealedCatalog
  expected := #[]
  source := #[]
  baseline := #[]
  companionPrefix := none } }
def sealEntry : Contract.Seal := { rootId := `LeanInformationAuditRegTests.ContractPathFixtures.Complete.SealedCatalog, options := #[] }
end LeanInformationAuditRegTests.ContractPathFixtures.Complete.SealedCatalog
