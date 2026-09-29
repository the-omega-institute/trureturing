import LeanInformationAuditRegTests.SealBaseline

open Lean Lean.Elab.Command LeanInformationAudit

run_cmd do
  let env ← getEnv
  validateRegistrySnapshot Reg.Support.InformationRootContract.rootId env
  unless (expectedOccurrencesForRoot env Reg.Support.InformationRootContract.rootId).size == 11 do
    throwError "ROOT-B-frozen-baseline: expected eleven frozen occurrences"
  logInfo "ROOT-B-frozen-baseline: eleven frozen occurrences validated"
