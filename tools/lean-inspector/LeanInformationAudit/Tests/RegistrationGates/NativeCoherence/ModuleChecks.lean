import LeanInformationAudit.Registry
import LeanInformationAudit.Tests.RegistrationGates.NativeCoherence.Plain
import LeanInformationAudit.Tests.RegistrationGates.NativeCoherence.Modern
import LeanInformationAudit.Tests.SourceIsolation

open Lean LeanInformationAudit LeanInformationAudit.TemplateAudit

private def replaceNative (path : System.FilePath) (bytes : ByteArray) : IO Unit := do
  let temp := path.withExtension "dtr-module-temporary"
  IO.FS.writeBinFile temp bytes
  IO.FS.rename temp path

private def observe (label : String) (root : Name) (expected : String) : CoreM Bool := do
  let reason ← try
    NativeCoherence.validate #[root]
    pure ""
  catch error => pure (← error.toMessageData.toString)
  let ok := reason == expected
  logInfo m!"[{if ok then "PASS" else "FAIL"}] {label} actual={reason}"
  return ok

run_meta LeanInformationAudit.Tests.withPrivateSources do
  let saved ← getEnv
  let root := `LeanInformationAudit.Tests.RegistrationGates.NativeCoherence.Modern
  let legacy := `LeanInformationAudit.Tests.RegistrationGates.NativeCoherence.Plain
  discard <| observe "legacy_native_still_accepted" legacy ""
  setEnv saved
  let fresh ← observe "fresh_module_native_report_accepted" root ""
  setEnv saved
  let source : System.FilePath := sourcePath root
  let sourceBytes ← IO.FS.readBinFile source
  try
    replaceNative source (sourceBytes ++ "\n-- stale native source\n".toUTF8)
    discard <| observe "stale_module_source_rejected" root
      s!"incomplete_closure:E7.native_source:{root}"
  finally
    replaceNative source sourceBytes
    setEnv saved
  let olean ← findOLean root
  for (path, kind) in #[(olean.addExtension "private", "private"),
      (olean.withExtension "ir", "ir")] do
    let bytes ← IO.FS.readBinFile path
    try
      replaceNative path (bytes.push 0)
      discard <| observe s!"changed_module_{kind}_artifact_rejected" root
        s!"incomplete_closure:E7.loaded_native:{root}"
    finally
      replaceNative path bytes
      setEnv saved
    if fresh then
      NativeCoherence.validate #[root]
      try
        replaceNative path (bytes.push 0)
        discard <| observe s!"cached_module_{kind}_artifact_rejected" root
          "incomplete_closure:E7.native_input_changed"
      finally
        replaceNative path bytes
        setEnv saved
  discard <| observe "restored_module_native_accepted" root ""
  setEnv saved
