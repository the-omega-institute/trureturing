import LeanInformationAudit.Tests.RegistrationGates.NativeCoherence.BindingOwner

namespace LeanInformationAudit.Tests.NativeCoherence
open Lean Meta TemplateAudit

private def replaceNative (path : System.FilePath) (bytes : ByteArray) : IO Unit := do
  let temp := path.withExtension "dtr-native-temporary"
  IO.FS.writeBinFile temp bytes
  IO.FS.rename temp path

run_meta do
  let originalEnv ← getEnv
  let some original := (TemplateBinding.records originalEnv).find?
      (·.occurrence.key.theoremName == `LeanInformationAudit.Tests.NativeBindingOwner.validated)
    | throwError "setup: native binding fixture missing"
  let claim : TemplateBindingClaim := {
    key := original.occurrence.key, arena := original.occurrence.arena,
    owner := original.bindingOwner.getD original.occurrence.key.registrationModule,
    descriptor := original.descriptor }
  let warmed ← TemplateBinding.assess original.occurrence (some claim)
  unless warmed.result matches .declaredValidated _ do
    throwError "setup: fresh native binding did not validate"
  let before := TemplateBinding.observedAssessments (← getEnv)
  let cached ← TemplateBinding.assess original.occurrence (some claim)
  let cachedOk := (cached.result matches .declaredValidated _) &&
    (TemplateBinding.observedAssessments (← getEnv)).size == before.size
  logInfo m!"[{if cachedOk then "PASS" else "FAIL"}] native_cached_binding_accepted"
  let path ← findOLean original.occurrence.key.registrationModule
  let bytes ← IO.FS.readBinFile path
  try
    -- Replace the inode; never write into a mapped native file.
    replaceNative path (bytes.push 0)
    let record ← TemplateBinding.assess original.occurrence (some claim)
    let ok := match record.result with
      | .declaredUnresolved diagnostic =>
        (diagnostic.splitOn "rule=E7.native_input_changed").length == 2
      | _ => false
    logInfo m!"[{if ok then "PASS" else "FAIL"}] replaced_native_artifact_rejected"
  finally
    replaceNative path bytes
    unless (← IO.FS.readBinFile path) == bytes do
      throwError "setup: native artifact restoration failed"
    setEnv originalEnv

end LeanInformationAudit.Tests.NativeCoherence
