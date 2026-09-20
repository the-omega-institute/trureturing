import LeanInformationAudit.Tests.Occurrence.ImportedArenaContractSource
import LeanInformationAudit.SealCommand

open Lean Elab Command LeanInformationAudit ImportedContractProbe

namespace ImportedContractFixture

local instance : DecidableEq lawArena.State := lawArena.toArena.stateDecidableEq

def contributor : Name := `LeanInformationAudit.Tests.Occurrence.ImportedArenaContract

def row (arena : Name) : CommandElabM SnapshotOccurrence := do
  return {
    objectArenaName := arena
    theoremName := ``target
    statementIdentity := theoremStatementIdentity (← getEnv) ``target
    registrationModuleName := contributor }

private def checkEvidence (name owner : Name) : CommandElabM Unit := do
  unless (← liftTermElabM <| resolveCanonicalArenaNameFromEvidence name) == owner do
    throwError "contract evidence ownership: {name}"

-- Each route is tested in isolation, before any registration or other acquisition.
-- Baseline-only is an invalid seal membership, but must still acquire its evidence.
run_cmd do
  unless (InformationRegistry.entries (← getEnv)).isEmpty do
    throwError "contract fixture has incidental registrations"
  let original ← getEnv
  for (aliasName, copy, role) in #[
      (``expectedAlias, ``expectedCopy, "expected"),
      (``sourceAlias, ``sourceCopy, "source"),
      (``baselineAlias, ``baselineCopy, "baseline")] do
    try
      for name in #[aliasName, copy] do
        let message ← try
          discard <| liftTermElabM <| resolveCanonicalArenaNameFromEvidence name
          pure "accepted"
        catch error => error.toMessageData.toString
        unless message == s!"IE-C003 ArenaSourceUnavailable declaration={name} reason=provenance" do
          throwError "contract input was acquired incidentally: {name}: {message}"
      let rows := #[← row aliasName, ← row copy]
      RootCatalogs.declare {
        rootId := original.header.mainModule
        expected := if role == "expected" then rows else #[]
        source := if role == "source" then rows else #[]
        baseline := if role == "baseline" then rows else #[] }
      checkEvidence aliasName ``arena
      checkEvidence copy copy
      let some contract := RootCatalogs.find? (← getEnv) original.header.mainModule
        | throwError "missing contract"
      unless contract.expected.size == (if role == "expected" then 2 else 0) &&
          contract.source.size == (if role == "source" then 2 else 0) &&
          contract.baseline.size == (if role == "baseline" then 2 else 0) do
        throwError "contract acquisition changed independent membership"
    finally
      setEnv original
  logInfo "contract expected-only/source-only/baseline-only aliases and copies acquired"

-- The actual native producer retains six distinct source spellings. In particular,
-- neither source-only nor baseline rows is incidentally acquired by registration.
run_cmd do
  let baseline := #[← row ``baselineAlias, ← row ``baselineCopy]
  RootCatalogs.declare {
    rootId := (← getEnv).header.mainModule
    expected := #[← row ``expectedAlias, ← row ``expectedCopy]
    source := #[← row ``sourceAlias, ← row ``sourceCopy] ++ baseline
    baseline }
  for (aliasName, copy) in #[( ``expectedAlias, ``expectedCopy),
      (``sourceAlias, ``sourceCopy), (``baselineAlias, ``baselineCopy)] do
    checkEvidence aliasName ``arena
    checkEvidence copy copy

register_information_theorem target in lawArena object_arena arena catalog forwarding
  primitives readout.toPrimitiveBundle realization bridge
register_information_theorem target in lawArena object_arena expectedCopy catalog copy
  primitives readout.toPrimitiveBundle realization bridge

#seal_information_theory

end ImportedContractFixture
