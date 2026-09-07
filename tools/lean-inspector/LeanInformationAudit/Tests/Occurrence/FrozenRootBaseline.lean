import LeanInformationAudit.Tests.Occurrence.SealBaseline

open Lean Lean.Elab.Command LeanInformationAudit

run_cmd do
  let env := (← getEnv).setMainModule frozenInformationRootId
  validateRegistrySnapshot env
  unless (expectedOccurrencesForRoot env frozenInformationRootId).size == 11 do
    throwError "ROOT-B-frozen-baseline: expected eleven frozen occurrences"
  logInfo "ROOT-B-frozen-baseline: eleven frozen occurrences validated"
