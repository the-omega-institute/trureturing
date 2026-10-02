import LeanInformationAudit.Tests.SealCollisionBase
import LeanInformationAudit.Tests.Assessment

test_imported_assessment

open LeanInformationAudit

run_cmd do
  let owner := (← Lean.getEnv).header.mainModule
  let entry : InformationRegistryEntry := {
    theoremName := `LeanInformationAudit.Tests.SealCollisionFixture.target
    unitName := `LeanInformationAudit.Tests.SealCollisionFixture.persistedUnit
    arenaName := `LeanInformationAudit.Tests.SealCollisionFixture.arena
    realizationName := `LeanInformationAudit.Tests.SealCollisionFixture.fixtureRealization
    registrationModuleName := owner }
  let sourceText := (← read).fileMap.source
  let options ← Lean.getOptions
  Lean.modifyEnv (RegistrationInputs.add · { entry, sourceText, options })
  registerValidatedEntry owner entry
