import Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors
import LeanInformationAudit.Tests.Assessment

open Lean Meta LeanInformationAudit

run_meta do
  let .defnInfo info ← getConstInfo
      `Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Scan.registration_2
    | throwError "production registration definition absent"
  let row ← Contract.Decoder.registration
    `Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors info ""
  let some declaration := row.input.declaration
    | throwError "production declaration absent"
  let some selection := declaration.escapeInput.sourceSelection
    | throwError "production source selection absent"
  unless selection.coordinates == #[0, 23] && selection.readouts.size == 1 do
    throwError "production source selection changed"
  let readout := selection.readouts[0]!
  unless readout.path.size == 34 && readout.stateBinder == 14 &&
      readout.path.extract 0 22 == Array.replicate 22 "body" &&
      readout.path.extract 32 34 == #["fn", "arg"] do
    throwError "production long readout path changed"

test_imported_assessment

run_meta do
  let target := `D5.S1.Words.Attractors.periodic_residual_scan
  let some record := (TemplateBinding.records (← getEnv)).find?
      (·.occurrence.key.theoremName == target)
    | throwError "production long-path assessment absent"
  let unitInfo ← getConstInfo record.occurrence.unitName
  let targetInfo ← getConstInfo target
  unless ← isDefEq record.occurrence.statement targetInfo.type do
    throwError "production long-path statement changed"
  let some value := unitInfo.value? (allowOpaque := true)
    | throwError "production long-path unit value absent"
  checkWithKernel value
  logInfo "[PASS] production long-array metadata preserves source selection and kernel companions"
