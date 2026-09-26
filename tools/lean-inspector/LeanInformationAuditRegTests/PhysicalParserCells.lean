-- The existing cut-template consumer shares the one canonical enrollment.
import Reg.D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion
import Reg.D5.S0.Computability.Coding.PhysicalSixParser
import Reg.D5.S0.Computability.Coding.PhysicalParserTally
import Reg.D5.S0.Computability.Coding.PhysicalParserPadding
import Reg.D5.S0.Computability.Coding.PhysicalParserField
import Reg.D5.S0.Computability.Coding.PhysicalParserExecution

open Lean Meta LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape RegistrationTemplates

namespace LeanInformationAuditRegTests.PhysicalParserCells

-- Use the actual source-owner registrations, including all original premises,
-- complete output frames, head positions and bounds at every execution prefix.
run_meta do
  let pairs := #[
    (`D5.S0.Computability.Coding.PhysicalSixParser.coupled_source_rewind,
      `Reg.D5.S0.Computability.Coding.PhysicalSixParser),
    (`D5.S0.Computability.Coding.PhysicalParserTally.count_one,
      `Reg.D5.S0.Computability.Coding.PhysicalParserTally),
    (`D5.S0.Computability.Coding.PhysicalParserPadding.pad_one,
      `Reg.D5.S0.Computability.Coding.PhysicalParserPadding),
    (`D5.S0.Computability.Coding.PhysicalParserField.parse_field,
      `Reg.D5.S0.Computability.Coding.PhysicalParserField),
    (`D5.S0.Computability.Coding.PhysicalParserExecution.parser_frame_resources,
      `Reg.D5.S0.Computability.Coding.PhysicalParserExecution)]
  let .defnInfo erased ← getConstInfo ``Reg.Support.PhysicalParserCells.erased
    | throwError "[FAIL] missing cell erasure"
  let mut selection := #[]
  for (target, owner) in pairs do
    let env ← getEnv
    let events := (TemplateBinding.inventory env).filter fun event =>
      event.key.theoremName == target && event.key.registrationModule == owner
    let #[event] := events | throwError "[FAIL] expected one source-owner occurrence: {target}"
    let some (_, claim) := (TemplateBinding.ownedClaims env).find? (·.2.key == event.key)
      | throwError "[FAIL] missing source-owner claim: {target}"
    let record ← TemplateBinding.assess event (some claim)
    let .declaredValidated cert := record.result
      | throwError "[FAIL] physical cell registration: {(← TemplateBinding.recordJson record).compress}"
    unless record.escape.bridgeKind == "legacy" && record.escape.fromObject.isSome &&
        record.escape.continuation.any (·.kind == "open") && !cert.evidenceRef.isEmpty do
      throwError "[FAIL] incomplete four-slot physical cell registration: {target}"
    -- False erasure cannot masquerade as the identity readout of this occurrence.
    -- This uses full current production assessment, not a fixture-only comparator.
    let changed ← TemplateBinding.assess event (some { claim with descriptor := some erased.value })
    let .declaredUnresolved diagnostic := changed.result
      | throwError "[FAIL] erased cell descriptor accepted: {target}"
    unless (diagnostic.splitOn "rule=dtr.realization_mismatch ").length == 2 do
      throwError "[FAIL] erased descriptor failed at an unexpected boundary: {diagnostic}"
    logInfo m!"[PASS] physical_cells_complete_law_and_erasure_rejected {target} evidence_ref={cert.evidenceRef}"
    selection := selection.push (owner, #[event.key])
  let wires ← TemplateBinding.reportJson selection
  IO.FS.writeFile ((← Repository.root) / ".lake/build/physical-parser-cell-evidence.json")
    ((Json.arr wires).compress ++ "\n")

-- These kernel checks tie the positive/negative Laws and dependence proofs to
-- each retained arena and its actual realization, rather than existential toys.

section
open Reg.D5.S0.Computability.Coding.PhysicalSixParser
example : arena.Law cellRealization := _root_.D5.S0.Computability.Coding.PhysicalSixParser.coupled_source_rewind
example : ¬ arena.Law Reg.Support.PhysicalParserCells.erased := erased_fails
example : ∃ b b' : Bool, cellRealization.readout () b ≠ cellRealization.readout () b' := dependence
end

section
open Reg.D5.S0.Computability.Coding.PhysicalParserTally
example : arena.Law cellRealization := _root_.D5.S0.Computability.Coding.PhysicalParserTally.count_one
example : ¬ arena.Law Reg.Support.PhysicalParserCells.erased := erased_fails
example : ∃ b b' : Bool, cellRealization.readout () b ≠ cellRealization.readout () b' := dependence
end

section
open Reg.D5.S0.Computability.Coding.PhysicalParserPadding
example : arena.Law cellRealization := _root_.D5.S0.Computability.Coding.PhysicalParserPadding.pad_one
example : ¬ arena.Law Reg.Support.PhysicalParserCells.erased := erased_fails
example : ∃ b b' : Bool, cellRealization.readout () b ≠ cellRealization.readout () b' := dependence
end

section
open Reg.D5.S0.Computability.Coding.PhysicalParserField
example : arena.Law cellRealization := _root_.D5.S0.Computability.Coding.PhysicalParserField.parse_field
example : ¬ arena.Law Reg.Support.PhysicalParserCells.erased := erased_fails
example : ∃ b b' : Bool, cellRealization.readout () b ≠ cellRealization.readout () b' := dependence
end

section
open Reg.D5.S0.Computability.Coding.PhysicalParserExecution
example : arena.Law cellRealization := _root_.D5.S0.Computability.Coding.PhysicalParserExecution.parser_frame_resources
example : ¬ arena.Law Reg.Support.PhysicalParserCells.erased := erased_fails
example : ∃ b b' : Bool, cellRealization.readout () b ≠ cellRealization.readout () b' := dependence
end

end LeanInformationAuditRegTests.PhysicalParserCells
