import LeanInformationAuditInterface.Contract.Catalog
open Lean LeanInformationAudit
namespace LeanInformationAuditRegTests.ContractPathFixtures.DuplicateSeal.SealedCatalog
def catalog : Contract.RootCatalog := { data := {
  rootId := `LeanInformationAuditRegTests.ContractPathFixtures.DuplicateSeal.SealedCatalog
  expected := #[]
  source := #[]
  baseline := #[]
  companionPrefix := none } }
def sealEntry : Contract.Seal := { rootId := `LeanInformationAuditRegTests.ContractPathFixtures.DuplicateSeal.SealedCatalog, options := #[] }
def seal2 : Contract.Seal := { rootId := `LeanInformationAuditRegTests.ContractPathFixtures.DuplicateSeal.SealedCatalog, options := #[] }
end LeanInformationAuditRegTests.ContractPathFixtures.DuplicateSeal.SealedCatalog
