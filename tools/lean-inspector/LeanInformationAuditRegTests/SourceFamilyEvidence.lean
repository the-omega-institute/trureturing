import Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation
import Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore
import Reg.D5.S3.Quantum.Information.InfiniteCalibrationControl
import LeanInformationAuditRegTests.CompiledSourceWire

open Lean Meta LeanInformationAudit
namespace LeanInformationAuditRegTests.SourceFamilyEvidence

set_option trace.InformationRegistration.check true

run_meta do
  for name in #[
      `D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation.history_law_conditional_expectation,
      `D5.S1.Words.Patterns.CyclicStackPreimages.process_eq_run,
      `D5.S1.Words.Patterns.CyclicStackPreimages.process_perm,
      `D5.S3.Quantum.Information.InfiniteCalibrationControl.result] do
    let env ← getEnv
    let some event := (TemplateBinding.inventory env).find? (·.key.theoremName == name)
      | throwError "[FAIL] original source occurrence missing: {name}"
    let some (_, claim) := (TemplateBinding.ownedClaims env).find? (·.2.key == event.key)
      | throwError "[FAIL] original source claim missing: {name}"
    let before := (TemplateBinding.observedAssessments env).size
    let start ← IO.monoMsNow
    let heartbeats ← IO.getNumHeartbeats
    let record ← TemplateBinding.assess event (some claim)
    let heartbeats := (← IO.getNumHeartbeats) - heartbeats
    let elapsed := (← IO.monoMsNow) - start
    unless (TemplateBinding.observedAssessments (← getEnv)).size == before + 1 do
      throwError "[FAIL] source assessment measurement used cached result: {name}"
    let .declaredValidated certificate := record.result
      | throwError "[FAIL] original source assessment: {(← TemplateBinding.recordJson record).compress}"
    unless certificate.sourceBinding.isSome && record.escape.bridgeKind == "source-equivalence" &&
        record.escape.fromObject.isSome && record.escape.continuation.any (·.kind == "open") do
      throwError "[FAIL] original source four slots: {name}"
    logInfo m!"SOURCE_ASSESSMENT {name}: internal_heartbeats={heartbeats} ms={elapsed} evidence_ref={certificate.evidenceRef}"
  let snapshot ← TemplateBinding.exportSnapshot
  let modules := #[
    `Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation,
    `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore,
    `Reg.D5.S3.Quantum.Information.InfiniteCalibrationControl]
  let selection := modules.map fun owner => (owner,
    snapshot.originals.filter (·.occurrence.key.registrationModule == owner) |>.map (·.occurrence.key))
  let wire := (Json.arr (← TemplateBinding.reportJson selection)).compress
  unless wire == CompiledSourceWire.canonical do
    throwError "SOURCE_FAMILY_REPORT={wire}"
  IO.FS.writeFile ((← Repository.root) / ".lake/build/compiled-source-family-evidence.json") (wire ++ "\n")
  logInfo "[PASS] four_original_source_occurrences_exact_native_managed_wire"

end LeanInformationAuditRegTests.SourceFamilyEvidence
