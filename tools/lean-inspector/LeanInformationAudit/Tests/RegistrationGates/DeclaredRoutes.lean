import LeanInformationAudit.Tests.RegistrationGates.DeclaredArgumentIntegration
import LeanInformationAudit.Tests.RegistrationGates.DeclaredP1

namespace LeanInformationAudit.Tests.DeclaredRoutes
open Lean Meta Elab Command
open D5.S3.ConceptDynamics.InformationEscape
open RegistrationPositive

local instance : DecidableEq arena.State := arena.toArena.stateDecidableEq
theorem legacyBridge : LegacyPrimitiveRealization arena (arena.Law good) good := ⟨Iff.rfl⟩

theorem legacy : arena.Law good := rfl
register_information_theorem legacy in arena
  readout via (missingTemplate good) primitives good.toPrimitiveBundle
  realization legacyBridge variation lawVariation sensitivity slotSensitivity

theorem legacyOccurrence : arena.Law good := rfl
register_information_theorem legacyOccurrence in arena object_arena objectArena catalog declared
  readout via (missingTemplate good) primitives good.toPrimitiveBundle
  realization legacyBridge variation lawVariation sensitivity slotSensitivity

information_theorem native in arena readout via (missingTemplate good) primitives good
  variation lawVariation sensitivity slotSensitivity : arena.Law good := rfl

information_theorem nativeOccurrence in arena object_arena objectArena catalog declared
  readout via (missingTemplate good) primitives good
  variation lawVariation sensitivity slotSensitivity : arena.Law good := rfl

run_meta do
  let env ← getEnv
  let finiteNames := #[``legacy, ``legacyOccurrence, ``native, ``nativeOccurrence,
    `LeanInformationAudit.Tests.DeclaredP1.clean]
  let structuralName := `LeanInformationAudit.Tests.DeclaredStructural.declared
  let names := finiteNames.push structuralName
  let sourceOk := finiteNames.all (InformationRegistry.hasTheorem env) &&
    (DispositionCensus.structuralProvenanceEntries env).any (·.theoremName == structuralName)
  logInfo m!"[{if sourceOk then "PASS" else "FAIL"}] all_routes_supported_control"
  let inventory := TemplateBinding.inventory env
  let records := TemplateBinding.records env
  let recorded := names.all fun name =>
    let events := inventory.filter (·.key.theoremName == name)
    let rows := records.filter (·.occurrence.key.theoremName == name)
    events.size == 1 && rows.size == 1 && rows[0]!.occurrence.key == events[0]!.key &&
      (match rows[0]!.result with
       | .declaredValidated certificate => name == structuralName && !certificate.evidenceRef.isEmpty
       | .declaredUnresolved diagnostic => name != structuralName &&
          (diagnostic.splitOn "rule=dtr.missing_template").length == 2
       | .undeclared => false)
  logInfo m!"[{if recorded then "PASS" else "FAIL"}] all_registration_routes_recorded"

end LeanInformationAudit.Tests.DeclaredRoutes
