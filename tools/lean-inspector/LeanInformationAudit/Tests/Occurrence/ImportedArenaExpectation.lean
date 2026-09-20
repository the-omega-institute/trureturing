import LeanInformationAudit.Tests.Occurrence.ImportedArenaContractSource
import LeanInformationAudit.SealCommand

open Lean Elab Command LeanInformationAudit ImportedContractProbe

local instance : DecidableEq lawArena.State := lawArena.toArena.stateDecidableEq

run_cmd do
  unless (InformationRegistry.entries (← getEnv)).isEmpty do
    throwError "expectation fixture has incidental registrations"
  for name in #[``expectationAlias, ``expectationCopy] do
    let message ← try
      discard <| liftTermElabM <| resolveCanonicalArenaNameFromEvidence name
      pure "accepted"
    catch error => error.toMessageData.toString
    unless message == s!"IE-C003 ArenaSourceUnavailable declaration={name} reason=provenance" do
      throwError "expectation input was acquired incidentally: {name}: {message}"

expect_information_occurrence target in expectationAlias
  from "LeanInformationAudit.Tests.Occurrence.ImportedArenaExpectation"
expect_information_occurrence target in expectationCopy
  from "LeanInformationAudit.Tests.Occurrence.ImportedArenaExpectation"

run_cmd do
  for (name, owner) in #[( ``expectationAlias, ``arena), (``expectationCopy, ``expectationCopy)] do
    unless (← liftTermElabM <| resolveCanonicalArenaNameFromEvidence name) == owner do
      throwError "independent expectation command did not acquire evidence: {name}"

register_information_theorem target in lawArena object_arena arena catalog forwarding
  primitives readout.toPrimitiveBundle realization bridge
register_information_theorem target in lawArena object_arena expectationCopy catalog copy
  primitives readout.toPrimitiveBundle realization bridge

#seal_information_theory
