import LeanInformationAudit.Tests.Occurrence.ImportedArenaContractSource
import LeanInformationAudit.SealCommand

open Lean Elab Command LeanInformationAudit ImportedContractProbe

local instance : DecidableEq lawArena.State := lawArena.toArena.stateDecidableEq

register_information_theorem target in lawArena object_arena arena catalog absentEvidence
  primitives readout.toPrimitiveBundle realization bridge

-- Bypass only compilation acquisition to model an imported input with missing
-- evidence. With alias guessing this would seal the real registration above.
run_cmd do
  let env ← getEnv
  modifyEnv fun current => ExpectedOccurrenceManifest.addEntry current {
    rootId := env.header.mainModule
    objectArenaName := ``missingEvidence
    theoremName := ``target
    statementIdentity := theoremStatementIdentity env ``target
    registrationModuleName := env.header.mainModule }

/-- error: IE-C003 ArenaSourceUnavailable declaration=ImportedContractProbe.missingEvidence reason=provenance -/
#guard_msgs (error) in
#seal_information_theory

run_cmd do
  let env ← getEnv
  unless (InformationRegistry.entries env).size == 1 &&
      (SealRecords.forRoot env env.header.mainModule).isEmpty do
    throwError "missing-evidence seal changed registration or published records"
