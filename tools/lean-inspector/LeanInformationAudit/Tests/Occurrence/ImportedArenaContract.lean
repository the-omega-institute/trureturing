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

-- Each input route must reject both directions of grouped/default misalignment
-- before publishing a contract. Run before registration, resetting each attempt.
run_cmd do
  unless (InformationRegistry.entries (← getEnv)).isEmpty do
    throwError "grouped contract fixture has incidental registrations"
  let original ← getEnv
  for (aliasName, copy, role) in #[
      (``expectedGroupedAlias, ``expectedGroupedCopy, "expected"),
      (``sourceGroupedAlias, ``sourceGroupedCopy, "source"),
      (``baselineGroupedAlias, ``baselineGroupedCopy, "baseline")] do
    for name in #[aliasName, copy] do
      try
        let rows := #[← row name]
        let diagnostic ← try
          RootCatalogs.declare {
            rootId := original.header.mainModule
            expected := if role == "expected" then rows else #[]
            source := if role == "source" then rows else #[]
            baseline := if role == "baseline" then rows else #[] }
          pure "accepted"
        catch ex => ex.toMessageData.toString
        unless diagnostic == s!"IE-C003 ArenaSourceUnsupported arena={name} owner={name}" do
          throwError "[FAIL] grouped {role} input {name}: {diagnostic}"
        unless (RootCatalogs.find? (← getEnv) original.header.mainModule).isNone do
          throwError "[FAIL] grouped {role} input published a contract"
      finally
        setEnv original
  -- Explicit evidence acquisition also transports each deferred rejection to a
  -- second native import; no expected owner is obtained from a registration.
  for name in #[``expectedGroupedAlias, ``expectedGroupedCopy,
      ``sourceGroupedAlias, ``sourceGroupedCopy, ``baselineGroupedAlias, ``baselineGroupedCopy] do
    let .defnInfo info ← getConstInfo name | throwError "expected grouped definition"
    discard <| liftTermElabM <| ArenaProvenance.declarationValue info
    -- Also acquire the live forwarding helper before hitting the deferred input.
    let diagnostic ← liftTermElabM do
      try return s!"accepted owner={← resolveCanonicalArenaName name}"
      catch ex => ex.toMessageData.toString
    unless diagnostic == s!"IE-C003 ArenaSourceUnsupported arena={name} owner={name}" do
      throwError "[FAIL] grouped contract evidence acquisition: {diagnostic}"
  logInfo "[PASS] Q3 independent expected/source/baseline dual rejection; no contract published"

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
