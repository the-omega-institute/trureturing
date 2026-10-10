import LeanInformationAuditRegTests.ContractPathFixtures.Reg.D5.Mirror.RootCatalog
import LeanInformationAuditInterface.Contract.Catalog

namespace LeanInformationAuditRegTests.ContractPathFixtures.Reg.Catalogs.Membership.RootCatalog
open LeanInformationAudit

def catalog : Contract.RootCatalog := { data := {
  rootId := `LeanInformationAuditRegTests.ContractPathFixtures.Reg.Catalogs.Membership.RootCatalog
  expected := #[{
    statement := _
    proof := D5.S0.Tower.GoldenGapZeckendorf.wdigits_fib_add
    theoremName := `D5.S0.Tower.GoldenGapZeckendorf.wdigits_fib_add
    objectArenaName := `Reg.D5.S0.Tower.GoldenGapZeckendorf.arena
    statementIdentity := none
    registrationModuleName := `LeanInformationAuditRegTests.ContractPathFixtures.Reg.D5.Mirror.RootCatalog }]
  source := #[]
  baseline := #[]
  companionPrefix := none } }
end LeanInformationAuditRegTests.ContractPathFixtures.Reg.Catalogs.Membership.RootCatalog
