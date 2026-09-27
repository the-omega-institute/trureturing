import LeanInformationAudit.Syntax
import D5.S3.ConceptDynamics.InterventionLaws.ObservationInterventionKernelStrictness

open Lean Meta Elab Command LeanInformationAudit
open LeanInformationAudit.RegistrationGates

def identityDisguiseAlias (p : Prop) : Prop := p

run_meta do
  let env ← getEnv
  let target := ``D5.S3.ConceptDynamics.InterventionLaws.ObservationInterventionKernelStrictness.intervention_kernel_strictly_finer_than_observation
  let statement := (← getConstInfo target).type
  for (label, candidate) in #[
      ("id", mkApp2 (mkConst ``id [.succ .zero]) (.sort .zero) statement),
      ("let", Expr.letE `hidden (.sort .zero) statement (.bvar 0) false),
      ("alias", mkApp (mkConst ``identityDisguiseAlias) statement)] do
    unless ← isDefEq candidate statement do throwError "fixture_not_defeq:{label}"
    let initial ← argumentIdentityState target 524288
    let (apart, _) ← (checkedStatementType env candidate).run initial
    if apart.isSome then throwError "[FAIL] NEGATIVE_IDENTITY_ACCEPTED:{label}"
    let verdict ← templateArgumentsCurrent target #[candidate] 524288
    match verdict with
    | .error reason =>
      unless reason.startsWith "forbidden_dependency" || reason.startsWith "unclassified_form:E6.argument_identity" do
        throwError "negative_wrong_rejection:{label}:{reason}"
      logInfo m!"[PASS] StatementDisguise_{label}: {reason}"
    | .ok _ => throwError "NEGATIVE_ARGUMENT_ACCEPTED:{label}"
