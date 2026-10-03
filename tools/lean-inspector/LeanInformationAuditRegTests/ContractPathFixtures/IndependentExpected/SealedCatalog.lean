import LeanInformationAuditInterface.Contract.Catalog
open Lean LeanInformationAudit
namespace LeanInformationAuditRegTests.ContractPathFixtures.IndependentExpected.SealedCatalog
def expected : Contract.ExpectedDeclaration := { rootId := `LeanInformationAuditRegTests.ContractPathFixtures.IndependentExpected.SealedCatalog, occurrence := {
  statement := True, proof := True.intro, theoremName := `True.intro,
  objectArenaName := `Arena, statementIdentity := none, registrationModuleName := `Contributor } }
end LeanInformationAuditRegTests.ContractPathFixtures.IndependentExpected.SealedCatalog
