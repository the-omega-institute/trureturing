import LeanInformationAudit.SealCommand
import D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit

namespace LeanInformationAudit.Tests
open Lean Elab Command

/-- Tests explicitly invoke the same report service after their raw recorder
command. Production registration imports no test or evaluator module. -/
elab "test_assess " "in " command:command : command => registrationTransaction do
  let before ← getEnv
  elabCommand command
  if (← get).messages.hasErrors then return
  let after ← getEnv
  let root := after.header.mainModule
  for (owner, input) in (TemplateEnrollmentInputs.owned after).extract
      (TemplateEnrollmentInputs.owned before).size (TemplateEnrollmentInputs.owned after).size do
    assessRecordedEnrollment owner input
  for (owner, input) in (RegistrationInputs.owned after).extract
      (RegistrationInputs.owned before).size (RegistrationInputs.owned after).size do
    GeneratedDeclarations.withOwner owner <| assessRecordedEntry owner input
  if (SealInputs.owned after).size > (SealInputs.owned before).size then
    liftCoreM <| assessAndSealRegistration (← RegistrationAssessmentInput.capture root)

/-- Rebuild imported fixture records in each consumer, as the report does.
Imported diagnostics were asserted in their producers; setup retains errors. -/
elab "test_imported_assessment" : command => do
  let messages := (← get).messages
  liftTermElabM <| assessRecordedRegistrations (← getEnv).header.mainModule
  let current := (← get).messages
  unless current.hasErrors do modify fun state => { state with messages }

end LeanInformationAudit.Tests
