import LeanInformationAudit.RawArtifacts
import LeanInformationAudit.CompiledAxioms
import LeanInformationAudit.Contract.Discovery

namespace LeanInformationAuditRegTests.CompiledFixtureReader
open Lean LeanInformationAudit

unsafe def discover (reader : IO.Ref RawArtifacts.Store) (requirements : Array Contract.RootStructure.Requirement) (owners : Array Name)
    (sourceOf : Name → IO System.FilePath := Contract.Discovery.moduleSource) : IO Contract.Discovery.Snapshot := do
  for owner in owners do RawArtifacts.loadModule owner reader
  let store ← reader.get
  let start ← IO.getNumHeartbeats
  let context : Contract.CompiledExpressions.Context := {
    find := (store.constants[·]?), heartbeatStart := start, heartbeatLimit := Lean.Core.getMaxHeartbeats ({} : Options) }
  let closures ← IO.mkRef ({ closure := store.metadata.axioms } : CompiledAxioms.AxiomClosureState)
  Contract.Discovery.discoverCompiled requirements owners context
    (fun owner => return (← store.getModule owner).constants)
    (CompiledAxioms.collectAxiomsShared context.find closures) sourceOf
end LeanInformationAuditRegTests.CompiledFixtureReader
