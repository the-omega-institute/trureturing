import Reg.D5.S3.Quantum.Information.InfiniteCalibrationControl

open Lean Meta LeanInformationAudit
namespace LeanInformationAuditRegTests.InfiniteSourceContract

set_option trace.InformationRegistration.check true

run_meta do
  let snapshot ← TemplateBinding.exportSnapshot
  let records := snapshot.selected.filter (fun record => record.occurrence.key.registrationModule ==
    `Reg.D5.S3.Quantum.Information.InfiniteCalibrationControl)
  let #[record] := records | throwError "expected one complete infinite source registration"
  let .declaredValidated cert := record.result
    | throwError "infinite source failed: {(← TemplateBinding.recordJson record).compress}"
  unless cert.sourceBinding.isSome && record.escape.fromObject.isSome &&
      record.escape.continuation.any (·.kind == "open") do throwError "incomplete infinite record"
  let wires ← TemplateBinding.reportJson #[(record.occurrence.key.registrationModule,
    #[record.occurrence.key])]
  IO.FS.writeFile ((← Repository.root) / ".lake/build/infinite-family-evidence.json")
    ((Json.arr wires).compress ++ "\n")
  logInfo m!"[PASS] original_infinite_real_calibration_all_parameters evidence_ref={cert.evidenceRef}"

end LeanInformationAuditRegTests.InfiniteSourceContract
