import Reg.Support.CausalSourceFamily
import LeanInformationAudit.SealCommand

namespace LeanInformationAuditRegTests.LegacyCausalSourceBoundary
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation
open Reg.Support.CausalSourceFamily LeanInformationAudit

noncomputable def registration : Registration separationArena (Separation actual) where
  actual := actual
  bridge := Iff.rfl
  variation := separation_variation
  sensitivity := separation_sensitivity
  dependence := dependence

register_information_theorem intervention_strictly_weaker_than_counterfactual in separationArena
  readout via (realize signature actual.readout actual.anchor)
  realizes registration
  escape from source ({
    owner := `D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation
    coordinates := #[]
    readouts := #[
      { path := #["arg", "body", "arg", "body", "arg", "fn", "arg"], stateBinder := 0 },
      { path := #["arg", "body", "arg", "body", "fn", "arg", "fn", "arg"], stateBinder := 0 }] })
  escape continues (open)

open Lean Meta in
run_meta do
  let env ← getEnv
  let events := (TemplateBinding.inventory env).filter (·.key.registrationModule == env.header.mainModule)
  unless events.size == 1 do throwError "expected one complete original source-family occurrence"
  let event := events[0]!
  let some (_, claim) := (TemplateBinding.ownedClaims env).find? (·.2.key == event.key)
    | throwError "missing original source-family declaration"
  let record ← TemplateBinding.assess event (some claim)
  unless record.result matches .declaredValidated _ do
    throwError "original source-family binding failed: {(← TemplateBinding.recordJson record).compress}"
  logInfo "[PASS] complete original IC source-family registration validates"

run_cmd RootCatalogs.declare {
  rootId := `LeanInformationAuditRegTests.LegacyCausalSourceBoundary
  expected := #[{
    objectArenaName := `Reg.Support.CausalSourceFamily.separationArena
    theoremName := `D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.intervention_strictly_weaker_than_counterfactual
    statementIdentity := "sha256:fd8c5bad3c9b38d167e59ff3889f6897c82fdd7070d8feaae13528062ac13140"
    registrationModuleName := `LeanInformationAuditRegTests.LegacyCausalSourceBoundary }]
  source := #[{
    objectArenaName := `Reg.Support.CausalSourceFamily.separationArena
    theoremName := `D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.intervention_strictly_weaker_than_counterfactual
    statementIdentity := "sha256:fd8c5bad3c9b38d167e59ff3889f6897c82fdd7070d8feaae13528062ac13140"
    registrationModuleName := `LeanInformationAuditRegTests.LegacyCausalSourceBoundary }]
  companionPrefix := some `LeanInformationAuditRegTests.LegacyCausalSourceBoundary }

/--
error: Application type mismatch: The argument
  intervention_strictly_weaker_than_counterfactual.«LeanInformationAuditRegTests.LegacyCausalSourceBoundary/Reg.Support.CausalSourceFamily.separationArena/[anonymous]».__information_unit
has type
  Registration separationArena (Separation actual)
of sort `Type` but is expected to have type
  D5.S3.ConceptDynamics.InformationEscape.TheoremUnit ?arena
of sort `Type (max ?u.1 (?u.2 + 1))` in the application
  D5.S3.ConceptDynamics.InformationEscape.TheoremUnit.primitives
    intervention_strictly_weaker_than_counterfactual.«LeanInformationAuditRegTests.LegacyCausalSourceBoundary/Reg.Support.CausalSourceFamily.separationArena/[anonymous]».__information_unit
-/
#guard_msgs in
#seal_information_theory

#print axioms registration
end LeanInformationAuditRegTests.LegacyCausalSourceBoundary
