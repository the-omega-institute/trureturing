import LeanInformationAuditInterface.Contract.Catalog
open Lean LeanInformationAudit
namespace LeanInformationAuditRegTests.ContractPathFixtures.MissingSeal.SealedCatalog
def catalog : Contract.RootCatalog := { data := {
  rootId := `LeanInformationAuditRegTests.ContractPathFixtures.MissingSeal.SealedCatalog
  expected := #[]
  source := #[]
  baseline := #[]
  companionPrefix := none } }
end LeanInformationAuditRegTests.ContractPathFixtures.MissingSeal.SealedCatalog
