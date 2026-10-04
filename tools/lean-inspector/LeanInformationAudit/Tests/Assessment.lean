import LeanInformationAudit.SealCommand

namespace LeanInformationAudit.Tests
open Lean Elab Command

/-- Invoke the production report service in a downstream consumer. -/
elab "test_imported_assessment" : command => do
  let messages := (← get).messages
  liftTermElabM <| assessTypedRegistrations (← getEnv).header.mainModule
  let current := (← get).messages
  unless current.hasErrors do modify fun state => { state with messages }

end LeanInformationAudit.Tests
