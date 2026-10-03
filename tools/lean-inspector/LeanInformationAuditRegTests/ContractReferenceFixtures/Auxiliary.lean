import LeanInformationAuditInterface.Contract.Catalog
open Lean LeanInformationAudit
namespace ContractReferenceFixtures.Auxiliary
def entry : Contract.Seal := { rootId := `root, options := #[] }
def catalog : Contract.RootCatalog := {
  data := {
    rootId := `root
    expected := #[{
      statement := _
      proof := entry.eq_1
      theoremName := `ContractReferenceFixtures.Auxiliary.entry.eq_1
      objectArenaName := `Nat
      statementIdentity := none
      registrationModuleName := `LeanInformationAuditRegTests.ContractReferenceFixtures.Auxiliary }]
    source := #[]
    baseline := #[]
    companionPrefix := none } }
end ContractReferenceFixtures.Auxiliary
