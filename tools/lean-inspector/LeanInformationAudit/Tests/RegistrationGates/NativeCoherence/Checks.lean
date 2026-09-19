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
  (if ok then logInfo else logError) m!"[{if ok then "PASS" else "FAIL"}] {label} actual={repr actual}"

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
    (if ok then logInfo else logError) m!"[{if ok then "PASS" else "FAIL"}] native_export_stale_source_rejected reason={reason}"

observe_native_enrollment_coherence

elab "observe_empty_report_driver_coherence" : command => withPrivateSources do
  let requested := `LeanInformationAudit.Tests.RegistrationGates.NativeCoherence.Plain
  let observe (label : String) (expected : Option String) : CommandElabM Unit := do
    let saved ← get
    let actual ← try
      let values ← liftTermElabM <| finiteInformationTemplateReportDriver #[requested]
      unless values.size == 1 &&
          (values[0]!.1.getObjValAs? (Array Json) "inventory").toOption.any (·.isEmpty) do
        throwError "setup: expected exactly one empty inventory"
      pure none
    catch error => pure (some (← error.toMessageData.toString))
    set saved
    (if actual == expected then logInfo else logError) m!"[{if actual == expected then "PASS" else "FAIL"}] {label} actual={repr actual}"
  observe "no_registration_current_driver_accepted" none
  let owner := `LeanInformationAudit.Registry
  let path : System.FilePath := sourcePath owner
  let bytes ← IO.FS.readBinFile path
  withFile path (bytes ++ "\n-- driver changed after import\n".toUTF8) do
    observe "no_registration_stale_driver_rejected"
      (some s!"incomplete_closure:E7.native_source:{owner}")

observe_empty_report_driver_coherence

elab "observe_report_batch_coherence" : command => withPrivateSources do
  let owner := `LeanInformationAudit.Tests.RegistrationGates.NativeCoherence.Owner
  let plain := `LeanInformationAudit.Tests.RegistrationGates.NativeCoherence.Plain
  let requested := #[owner, plain]
  discard <| liftTermElabM <| finiteInformationTemplateReportDriver requested
  let observed := NativeCoherence.lastInputs (← getEnv)
  let complete := #[owner, plain, `LeanInformationAudit.Registry,
    `LeanInformationAudit.Tests.RegistrationGates.NativeCoherence.Helper].all
      (fun name => observed.contains (sourcePath name))
  (if complete then logInfo else logError) m!"[{if complete then "PASS" else "FAIL"}] native_report_batch_union_rechecked"
  let path : System.FilePath := sourcePath owner
  let bytes ← IO.FS.readBinFile path
  withFile path (bytes ++ "\n-- changed between report batches\n".toUTF8) do
    let reason ← try
      discard <| liftTermElabM <| finiteInformationTemplateReportDriver requested
      pure ""
    catch error => pure (← error.toMessageData.toString)
    let ok := reason == "incomplete_closure:E7.native_input_changed"
    (if ok then logInfo else logError) m!"[{if ok then "PASS" else "FAIL"}] native_report_batch_cached_source_rejected reason={reason}"
  discard <| liftTermElabM <| finiteInformationTemplateReportDriver requested
  logInfo "[PASS] native_report_batch_restored_source_accepted"

observe_report_batch_coherence

end LeanInformationAudit.Tests.NativeCoherence
