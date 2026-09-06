import LeanInformationAudit.SealCommand
import LeanInformationAudit.Tests.Occurrence.ImportClosureProducer

open Lean Lean.Elab.Command LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape
open LeanInformationAudit.Tests.ImportClosureProducer

namespace LeanInformationAudit.Tests.SourceOwnerCollision

set_option linter.style.longLine false

local instance : DecidableEq lawArena.State := lawArena.toArena.stateDecidableEq

theorem other : True := trivial

run_cmd do
  let unitName := catalogQualifiedName (← getEnv).header.mainModule
    `LeanInformationAudit.Tests.ImportClosureProducer.objectArena `importedBool
    `LeanInformationAudit.Tests.ImportClosureProducer.importedTheorem theoremUnitSuffix
  let unitId := mkIdent (`_root_ ++ unitName)
  elabCommand (← `(command| def $unitId : TheoremUnit lawArena.toArena :=
    TheoremUnit.mk fixtureRealization.toPrimitiveBundle True other))
  registerValidatedEntry {
    theoremName := `LeanInformationAudit.Tests.SourceOwnerCollision.other
    unitName
    arenaName := `LeanInformationAudit.Tests.ImportClosureProducer.lawArena
    realizationName := `LeanInformationAudit.Tests.ImportClosureProducer.fixtureRealization
    catalogId := `importedBool
    objectArenaName := `LeanInformationAudit.Tests.ImportClosureProducer.objectArena
    localRegistrationNames := false
  }

expect_information_occurrence importedTheorem
  in objectArena
  from "LeanInformationAudit.Tests.Occurrence.ImportClosureProducer"

expect_information_occurrence other
  in objectArena
  from "LeanInformationAudit.Tests.Occurrence.SourceOwnerCollision"

run_cmd do
  let env ← getEnv
  unless (InformationRegistry.entries env).size == 2 do
    throwError "source-owner collision must have two valid entries"
  validateRegistrySnapshot env
  validateSourceEntries env (InformationRegistry.entries env)

/-- error: IE-C025 QualifiedNameCollision root=LeanInformationAudit.Tests.Occurrence.SourceOwnerCollision catalog=importedBool generated_name=LeanInformationAudit.Tests.ImportClosureProducer.importedTheorem.«LeanInformationAudit.Tests.Occurrence.SourceOwnerCollision/LeanInformationAudit.Tests.ImportClosureProducer.objectArena/importedBool».__information_unit occurrences=["LeanInformationAudit.Tests.ImportClosureProducer.objectArena/LeanInformationAudit.Tests.ImportClosureProducer.importedTheorem","LeanInformationAudit.Tests.ImportClosureProducer.objectArena/LeanInformationAudit.Tests.SourceOwnerCollision.other"] -/
#guard_msgs (error) in
#seal_information_theory

end LeanInformationAudit.Tests.SourceOwnerCollision
