import LeanInformationAuditInterface.Contract.Catalog
open Lean LeanInformationAudit
namespace ContractRootFixtures.IndependentExpected
def catalog : Contract.RootCatalog := { data := { rootId := `ContractRoot, expected := #[], source := #[], baseline := #[], companionPrefix := none } }
def sealEntry : Contract.Seal := { rootId := `ContractRoot, options := #[] }
def expected : Contract.ExpectedDeclaration := { rootId := `ContractRoot, occurrence := { statement := True, proof := True.intro, theoremName := `True.intro, objectArenaName := `Arena, statementIdentity := none, registrationModuleName := `Contributor } }
end ContractRootFixtures.IndependentExpected
