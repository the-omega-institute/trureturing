import LeanInformationAudit.Tests.Occurrence.ImportedArenaContractSource
import LeanInformationAudit.SealCommand

open Lean Elab Command LeanInformationAudit ImportedContractProbe

local instance : DecidableEq lawArena.State := lawArena.toArena.stateDecidableEq

/-- error: IE-C003 ArenaSourceUnsupported arena=ImportedContractProbe.expectationNamedLive owner=ImportedContractProbe.expectationNamedLive -/
#guard_msgs (error) in
expect_information_occurrence target in expectationNamedLive
  from "LeanInformationAudit.Tests.Occurrence.ImportedArenaExpectation"

run_cmd do
  let original ← getEnv
  unless (ExpectedOccurrenceManifest.declaredEntries original original.header.mainModule).isEmpty do
    throwError "[FAIL] named live input published an expectation"
  for name in #[``expectationNamedDead, ``expectationNamedExplicit] do
    try
      unless (InformationRegistry.entries (← getEnv)).isEmpty do
        throwError "[FAIL] named expectation has incidental registration"
      elabCommand (← `(command| expect_information_occurrence target in $(mkIdent name)
        from "LeanInformationAudit.Tests.Occurrence.ImportedArenaExpectation"))
      let env ← getEnv
      let entries := ExpectedOccurrenceManifest.declaredEntries env env.header.mainModule
      unless entries.size == 1 && entries[0]!.objectArenaName == name do
        throwError "[FAIL] named independent expectation missing or rewritten: {name}"
      unless (← liftTermElabM <| resolveCanonicalArenaNameFromEvidence name) ==
          `ProvenanceProbe.arena do
        throwError "[FAIL] named independent expectation evidence: {name}"
    finally
      setEnv original
  logInfo "[PASS] ARCH-Q3-001 independent expectation dead/explicit accepted; \
    live rejected before insertion"

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
