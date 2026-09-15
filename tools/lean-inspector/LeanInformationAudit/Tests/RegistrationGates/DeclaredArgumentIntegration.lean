import LeanInformationAudit.Tests.RegistrationGates.Positive
import LeanInformationAudit.Tests.RegistrationGates.DeclaredStructural

namespace LeanInformationAudit.Tests.DeclaredArgumentIntegration
open Lean Meta Elab Command RegistrationGates

run_meta do
  let before ← observedWholeReadoutCalls
  let mut witnessControls := true
  for name in #[`RegistrationPositive.source, `RegistrationPositive.nativePositive,
      `RegistrationPositive.nativeOccurrence, `RegistrationPositive.legacyOccurrence] do
    let some entry := InformationRegistry.find? (← getEnv) name
      | throwError "setup: missing finite route"
    witnessControls := witnessControls && (← validateFinite entry).isNone
    let missing ← validateFinite { entry with variationWitness := .anonymous }
    witnessControls := witnessControls && missing.any (·.startsWith "IE-C048 ")
  let after ← observedWholeReadoutCalls
  logInfo m!"[{if witnessControls then "PASS" else "FAIL"}] finite_witness_controls_preserved"
  logInfo m!"[{if before == after then "PASS" else "FAIL"}] finite_gates_skip_whole_readout"
  let some structural := (DispositionCensus.structuralProvenanceEntries (← getEnv)).find?
      (·.theoremName == `LeanInformationAudit.Tests.DeclaredStructural.declared)
    | throwError "setup: missing structural route"
  let before ← observedWholeReadoutCalls
  let result ← validateStructural structural
  let after ← observedWholeReadoutCalls
  let valid := result.any fun message => message.startsWith "IE-C048 " &&
    message.endsWith "reason=missing_witness"
  logInfo m!"[{if valid then "PASS" else "FAIL"}] structural_missing_witness_preserved"
  logInfo m!"[{if before == after then "PASS" else "FAIL"}] structural_gates_skip_whole_readout"

end LeanInformationAudit.Tests.DeclaredArgumentIntegration
