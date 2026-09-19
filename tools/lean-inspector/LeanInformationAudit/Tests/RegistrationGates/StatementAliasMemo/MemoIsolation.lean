import LeanInformationAudit.Syntax
import D5.S3.ConceptDynamics.InterventionLaws.ObservationInterventionKernelStrictness

open Lean Meta Elab Command LeanInformationAudit.RegistrationGates

theorem memoOtherTarget : Nat.le 6 16 := by change 6 ≤ 16; decide

run_meta withStatementAliasMemo do
  let env ← getEnv
  let target := ``D5.S3.ConceptDynamics.InterventionLaws.ObservationInterventionKernelStrictness.intervention_kernel_strictly_finer_than_observation
  let first ← argumentIdentityState target 524288
  let second ← argumentIdentityState target 524288
  unless first.recognizedStatement.isSome && second.recognizedStatement.isSome do
    throwError "memo fixture did not normalize the statement"
  logInfo m!"MEMO_SCOPE cold={524288-first.exprFuel} warm={524288-second.exprFuel}"
  let disguised := mkApp2 (mkConst ``id [.succ .zero]) (.sort .zero) second.statement
  let (apart, _) ← (checkedStatementType env disguised).run second
  if apart.isSome then throwError "MEMO_ACCEPTED_SAME_STATEMENT"
  let other ← argumentIdentityState ``memoOtherTarget 524288
  let candidate := mkApp2 (mkConst ``Nat.lt) (mkNatLit 5) (mkNatLit 16)
  unless ← isDefEq candidate other.statement do throwError "memo fixture is not defeq"
  let (apart, _) ← (checkedStatementType env candidate).run other
  if apart.isSome then throwError "MEMO_LEAKED_ACROSS_THEOREMS"
  logInfo "[PASS] MemoWarmStatementDisguise"
  logInfo "[PASS] MemoDifferentTheoremDisguise"

-- Scope exit must restore both the enable flag and an enclosing cached value.
-- Compare work on identical queries so this observes reuse without exposing the
-- private memo or relying on a wall-clock threshold.
run_meta do
  let target := ``D5.S3.ConceptDynamics.InterventionLaws.ObservationInterventionKernelStrictness.intervention_kernel_strictly_finer_than_observation
  let cold ← argumentIdentityState target 524288
  withStatementAliasMemo do
    let first ← argumentIdentityState target 524288
    let warm ← argumentIdentityState target 524288
    unless warm.exprFuel > first.exprFuel do throwError "[FAIL] MemoWarmReuse"
    logInfo "[PASS] MemoWarmReuse"
  let outside ← argumentIdentityState target 524288
  unless outside.exprFuel == cold.exprFuel do
    throwError "[FAIL] MemoScopeRestoredAfterSuccess"
  logInfo "[PASS] MemoScopeRestoredAfterSuccess"
  try
    withStatementAliasMemo do
      let _ ← argumentIdentityState target 524288
      throwError "memo fixture exception"
  catch _ => pure ()
  let afterException ← argumentIdentityState target 524288
  unless afterException.exprFuel == cold.exprFuel do
    throwError "[FAIL] MemoScopeRestoredAfterException"
  logInfo "[PASS] MemoScopeRestoredAfterException"
  withStatementAliasMemo do
    let _ ← argumentIdentityState target 524288
    let warm ← argumentIdentityState target 524288
    withStatementAliasMemo do
      let _ ← argumentIdentityState ``memoOtherTarget 524288
      pure ()
    let restored ← argumentIdentityState target 524288
    unless restored.exprFuel == warm.exprFuel do
      throwError "[FAIL] MemoEnclosingCacheRestored"
    logInfo "[PASS] MemoEnclosingCacheRestored"
