import LeanInformationAudit.Tests.RegistrationGates.AllowlistBoundaries
import LeanInformationAudit.ReadoutProvenance

namespace LeanInformationAuditRegTests.CompiledProvenance
open Lean LeanInformationAudit LeanInformationAudit.RegistrationGates

/-- Read real compiler artifacts and run provenance with no compiler context.
The assertions cover positive readouts, retained target identity, payload
rejection and the existing zero-work incomplete route. -/
unsafe def readFixture : IO Unit := do
  let moduleName := `LeanInformationAudit.Tests.RegistrationGates.AllowlistBoundaries
  let reader ← IO.mkRef ({} : RawArtifacts.Store)
  RawArtifacts.loadModule moduleName reader
  let store ← reader.get
  let view := CompiledView.fromArtifacts store moduleName
  let session ← IO.mkRef ({} : ProvenanceSession)
  let context : QueryContext := {
    view, session, heartbeatStart := (← IO.getNumHeartbeats),
    heartbeatLimit := provenanceDefEqHeartbeats }
  for (label, readout, rejected) in #[
      ("plain", `AllowlistBoundaries.plain, false),
      ("independent_proof", `AllowlistBoundaries.proofArgument, false),
      ("target_identity", `AllowlistBoundaries.forbiddenArgument, true),
      ("payload", `AllowlistBoundaries.hiddenPayload, true)] do
    let (actual, closure) ← (Compiled.readoutClosureCurrent
      `AllowlistBoundaries.target (mkConst readout)).run context
    unless actual == rejected && closure.isSome do
      throw <| IO.userError s!"compiled.provenance:{label}:{actual}:{closure}"
    IO.println s!"[PASS] compiled provenance {label} rejected={actual}"
  let (rejected, closure) ← (Compiled.readoutClosureCurrent
    `AllowlistBoundaries.target (mkConst `AllowlistBoundaries.plain)).run
      { context with options := ({} : Options).set `provenanceExpressionLimit (0 : Nat) }
  unless !rejected && closure.isNone do
    throw <| IO.userError "compiled.provenance:zero_work"
  IO.println "[PASS] compiled provenance zero work is incomplete"

run_meta readFixture

end LeanInformationAuditRegTests.CompiledProvenance
