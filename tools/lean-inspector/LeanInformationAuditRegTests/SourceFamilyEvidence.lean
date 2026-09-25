import Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation
import Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore
import Reg.D5.S3.Quantum.Information.InfiniteCalibrationControl
import LeanInformationAuditRegTests.CompiledSourceWire

open Lean Meta LeanInformationAudit
namespace LeanInformationAuditRegTests.SourceFamilyEvidence

run_meta do
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
