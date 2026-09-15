import LeanInformationAudit.Tests.RegistrationGates.NativeCoherence.Owner
import LeanInformationAudit.Tests.RegistrationGates.NativeCoherence.Plain
import LeanInformationAudit.Tests.SourceIsolation

namespace LeanInformationAudit.Tests.NativeCoherence
open Lean Meta Elab Command TemplateAudit

private def replaceFile (path : System.FilePath) (bytes : ByteArray) : IO Unit := do
  let temp := path.withExtension "dtr-native-temporary"
  IO.FS.writeBinFile temp bytes
  IO.FS.rename temp path

private def withFile (path : System.FilePath) (bytes : ByteArray)
    (action : CommandElabM α) : CommandElabM α := do
  let original ← IO.FS.readBinFile path
  try
    replaceFile path bytes
    action
  finally
    replaceFile path original
    unless (← IO.FS.readBinFile path) == original do
      throwError "setup: native fixture restoration failed"

private def observeEnrollment (label : String) (expected : Option String) : CommandElabM Unit := do
  let saved ← get
  let result ← enroll `DTRNativeFixture.template
  let actual := match result with | .ok () => none | .error text => some text
  let present := (selectedPlan (← getEnv) `DTRNativeFixture.template).isOk
  set saved
  let ok := actual == expected && present == expected.isNone
  logInfo m!"[{if ok then "PASS" else "FAIL"}] {label} actual={repr actual}"

elab "observe_native_enrollment_coherence" : command => withPrivateSources do
  observeEnrollment "fresh_native_source_plan_accepted" none
  for (suffix, label) in #[("Owner", "fresh_source_stale_native_enrollment_rejected"),
      ("Helper", "transitive_source_stale_native_enrollment_rejected")] do
    let name := Name.str `LeanInformationAudit.Tests.RegistrationGates.NativeCoherence suffix
    let path : System.FilePath := sourcePath name
    let original ← IO.FS.readBinFile path
    withFile path (original ++ "\n-- changed after native import\n".toUTF8) do
      observeEnrollment label (some s!"incomplete_closure:E7.native_source:{name}")
  let owner := `LeanInformationAudit.Tests.RegistrationGates.NativeCoherence.Owner
  let path : System.FilePath := sourcePath owner
  let original ← IO.FS.readBinFile path
  withFile path (original ++ "\n-- export changed after native import\n".toUTF8) do
    let saved ← get
    let reason ← try
      discard <| liftTermElabM <| TemplateBinding.moduleInputs (← getEnv) owner
      pure ""
    catch error => pure (← error.toMessageData.toString)
    set saved
    let ok := reason == s!"incomplete_closure:E7.native_source:{owner}"
    logInfo m!"[{if ok then "PASS" else "FAIL"}] native_export_stale_source_rejected reason={reason}"

observe_native_enrollment_coherence

elab "observe_empty_report_driver_coherence" : command => withPrivateSources do
  let requested := `LeanInformationAudit.Tests.RegistrationGates.NativeCoherence.Plain
  let observe (label : String) (expected : Option String) : CommandElabM Unit := do
    let saved ← get
    let actual ← try
      let values ← liftTermElabM <| finiteInformationTemplateReportDriver #[requested]
      unless values.size == 1 &&
          (values[0]!.getObjValAs? (Array Json) "inventory").toOption.any (·.isEmpty) do
        throwError "setup: expected exactly one empty inventory"
      pure none
    catch error => pure (some (← error.toMessageData.toString))
    set saved
    logInfo m!"[{if actual == expected then "PASS" else "FAIL"}] {label} actual={repr actual}"
  observe "no_registration_current_driver_accepted" none
  let owner := `LeanInformationAudit.Registry
  let path : System.FilePath := sourcePath owner
  let bytes ← IO.FS.readBinFile path
  withFile path (bytes ++ "\n-- driver changed after import\n".toUTF8) do
    observe "no_registration_stale_driver_rejected"
      (some s!"incomplete_closure:E7.native_source:{owner}")

observe_empty_report_driver_coherence

end LeanInformationAudit.Tests.NativeCoherence
