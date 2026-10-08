import LeanInformationAuditRegTests.CompiledFixtureReader
import LeanInformationAuditRegTests.ContractGuards
import LeanInformationAuditRegTests.ContractTypeCarrierFixture

namespace LeanInformationAuditRegTests.ContractTypeCarrier
open Lean Meta Elab Command LeanInformationAudit.Contract
private def checkTest (label : String) (ok : Bool) : IO Unit :=
  unless ok do throw <| IO.userError s!"compiled.fixture:{label}"

unsafe def check (reader : IO.Ref LeanInformationAudit.RawArtifacts.Store) : IO Unit := do
  let discover := CompiledFixtureReader.discover reader
  let mut error := "accepted"
  try
    discard <| discover #[] #[`LeanInformationAuditRegTests.ContractTypeCarrierFixture]
  catch ex => error := ← pure ex.toString
  checkTest s!"discovery.alias_through_type_carrier:{error}"
    (error.contains "contract.cannot_decode:")
  IO.println s!"CONTRACT_DIAGNOSTIC discovery.alias_through_type_carrier {error}"

end LeanInformationAuditRegTests.ContractTypeCarrier
