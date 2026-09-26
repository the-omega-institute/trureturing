import LeanInformationAuditRegTests.LegacyRelationsSourceBoundary

open Lean Meta LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
namespace LeanInformationAuditRegTests.LegacyRelationsRegistrationBoundary

-- These test-only occurrences drive the actual shared assessor. The historical
-- mirrors stay at their old addresses until a faithful candidate is accepted.
register_information_theorem
    D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.end_state_omits_preempting_cause
  in Reg.Support.LegacyRelations.Preemption.arena
  readout via (realize Reg.Support.LegacyRelations.Preemption.signature
    Reg.Support.LegacyRelations.Preemption.actual.readout
    Reg.Support.LegacyRelations.Preemption.actual.anchor)
  realizes Reg.Support.LegacyRelations.Preemption.registration
  escape from source ({
    owner := `D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause
    coordinates := #[]
    readouts := #[{path := #["arg", "arg", "fn", "arg", "fn", "arg", "fn"], stateBinder := 0}] })
  escape continues (open)

register_information_theorem
    D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.commutativity_hypothesis_is_necessary
  in Reg.Support.LegacyRelations.Completion.arena
  readout via (realize Reg.Support.LegacyRelations.Completion.signature
    Reg.Support.LegacyRelations.Completion.actual.readout
    Reg.Support.LegacyRelations.Completion.actual.anchor)
  realizes Reg.Support.LegacyRelations.Completion.registration
  escape from source ({
    owner := `D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange
    coordinates := #[]
    readouts := #[{path := #["fn", "arg", "arg", "fn", "arg"], stateBinder := 0}] })
  escape continues (open)

register_information_theorem
    D5.S3.ConceptDynamics.InformationEscape.SystemUnit.engine_census_self_application
  in Reg.Support.LegacyRelations.System.arena
  readout via (realize Reg.Support.LegacyRelations.System.signature
    Reg.Support.LegacyRelations.System.actual.readout
    Reg.Support.LegacyRelations.System.actual.anchor)
  realizes Reg.Support.LegacyRelations.System.registration
  escape from source ({
    owner := `D5.S3.ConceptDynamics.InformationEscape.SystemUnit
    coordinates := #[]
    readouts := #[{path := #[], stateBinder := 0}] })
  escape continues (open)

run_meta do
  let owner := (← getEnv).header.mainModule
  let events := (TemplateBinding.inventory (← getEnv)).filter (·.key.registrationModule == owner)
  unless events.size == 3 do throwError "expected all three original source candidates"
  for event in events do
    let some (_, claim) := (TemplateBinding.ownedClaims (← getEnv)).find? (·.2.key == event.key)
      | throwError "missing actual declaration claim"
    let record ← TemplateBinding.assess event (some claim)
    let .declaredUnresolved diagnostic := record.result
      | throwError "unsupported source candidate must remain unresolved"
    unless diagnostic.contains "source.state_binder" do throwError "unexpected failure: {diagnostic}"
    logInfo m!"[PASS] original full registration rejected at source.state_binder: {event.key.theoremName}"

end LeanInformationAuditRegTests.LegacyRelationsRegistrationBoundary
