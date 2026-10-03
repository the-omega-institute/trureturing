import LeanInformationAuditInterface.Contract.Catalog
open Lean LeanInformationAudit
namespace LeanInformationAuditRegTests.ContractPathFixtures.UnexpectedSeal.RootCatalog
def catalog : Contract.RootCatalog := { data := {
  rootId := `LeanInformationAuditRegTests.ContractPathFixtures.UnexpectedSeal.RootCatalog
  expected := #[]
  source := #[]
  baseline := #[]
  companionPrefix := none } }
def sealEntry : Contract.Seal := { rootId := `LeanInformationAuditRegTests.ContractPathFixtures.UnexpectedSeal.RootCatalog, options := #[] }
end LeanInformationAuditRegTests.ContractPathFixtures.UnexpectedSeal.RootCatalog
