import LeanInformationAudit.Projection.OutputOnlyAudit

namespace LeanInformationAudit.Tests.PointerIdentity
open Lean Elab Command

private def identity (a b : α) : Bool := unsafe ptrEq a b

private def fileIdentity (a b : α) : Bool := unsafe
  match unsafeIO (IO.FS.readFile "/dev/null") with
  | .ok text => text.isEmpty && ptrEq a b
  | .error _ => false

private def computedIdentity (a b : α) : Bool := unsafe !(ptrEq a b)

private def swappedIdentity (a b : α) : Bool := unsafe ptrEq b a

private def publishIdentity : CommandElabM Unit := do
  let env ← getEnv
  if identity env env then pure () else throwError "identity failure"

private def publishFile : CommandElabM Unit := do
  let env ← getEnv
  if fileIdentity env env then pure () else throwError "identity failure"

private def publishComputed : CommandElabM Unit := do
  let env ← getEnv
  if computedIdentity env env then pure () else throwError "identity failure"

private def publishSwapped : CommandElabM Unit := do
  let env ← getEnv
  if swappedIdentity env env then pure () else throwError "identity failure"

private def identityCommand : CommandElab := terminalSealCommand publishIdentity
private def fileCommand : CommandElab := terminalSealCommand publishFile
private def computedCommand : CommandElab := terminalSealCommand publishComputed
private def swappedCommand : CommandElab := terminalSealCommand publishSwapped

-- Audit only: none of the candidate publication closures is executed.
run_cmd do
  let env ← getEnv
  for (name, expected, label) in #[
      (``identityCommand, true, "snapshot_pointer_identity_accepted"),
      (``fileCommand, false, "snapshot_unsafe_file_identity_rejected"),
      (``computedCommand, false, "snapshot_unsafe_computation_rejected"),
      (``swappedCommand, false, "snapshot_pointer_argument_order_rejected")] do
    let result := auditSealOutputOnly env name env.header.mainModule
    let ok := match result with
      | .ok () => expected
      | .error message => !expected &&
          (message.splitOn "IE-C043 KernelProjectionUsedForAdmission").length == 2 &&
          (message.splitOn "field=capability:").length == 2
    (if ok then logInfo else logError) m!"[{if ok then "PASS" else "FAIL"}] {label}"
    unless ok do logInfo m!"actual={repr result}"

end LeanInformationAudit.Tests.PointerIdentity
