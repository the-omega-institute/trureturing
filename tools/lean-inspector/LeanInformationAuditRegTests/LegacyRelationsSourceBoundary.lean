import Reg.Support.LegacyRelations.Preemption
import Reg.Support.LegacyRelations.Completion
import Reg.Support.LegacyRelations.System

/- Implicit abstraction and Boolean reification still reject. The positive
production registrations use explicit checked selectors; these probes preserve
the boundaries against silently inferring either operation. -/
open Lean Meta LeanInformationAudit
namespace LeanInformationAuditRegTests.LegacyRelationsSourceBoundary

private def mustReject (rule : String) (action : MetaM Unit) : MetaM Unit := do
  let result ← try action; pure "accepted" catch e => e.toMessageData.toString
  unless result.contains rule do throwError "expected {rule}, got {result}"
  logInfo m!"[PASS] original source boundary: {rule}"

private partial def firstConstant (name : Name) (e : Expr)
    (path : Array String := #[]) : Option (Array String) :=
  if e.isConstOf name then some path else
  match e with
  | .app f a => firstConstant name f (path.push "fn") <|>
      firstConstant name a (path.push "arg")
  | .forallE _ d b _ | .lam _ d b _ =>
      firstConstant name d (path.push "domain") <|> firstConstant name b (path.push "body")
  | .letE _ t v b _ => firstConstant name t (path.push "type") <|>
      firstConstant name v (path.push "value") <|> firstConstant name b (path.push "body")
  | .mdata _ b | .proj _ _ b => firstConstant name b (path.push "body")
  | _ => none

run_meta do
  let family := `D5.S3.ConceptDynamics.InformationEscape.DependentFamily
  let cases := #[
    (`D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.end_state_omits_preempting_cause,
      `D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.endState,
      `Reg.Support.LegacyRelations.Preemption),
    (`D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.commutativity_hypothesis_is_necessary,
      `D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.counterexampleF,
      `Reg.Support.LegacyRelations.Completion),
    (`D5.S3.ConceptDynamics.InformationEscape.SystemUnit.engine_census_self_application,
      `D5.S3.ConceptDynamics.InformationEscape.SystemUnit.SystemStatement,
      `Reg.Support.LegacyRelations.System)]
  for (name, operand, support) in cases do
    let info ← getConstInfo name
    let some path := firstConstant operand info.type
      | throwError "original operand absent: {operand}"
    let ((context, _), _) ← (SourceScope.atPath info.type path).run 524288
    unless context.isEmpty do throwError "expected closed named source operand: {name}"
    let owner := (RegistrationReifier.declaringModuleOf (← getEnv) name).get!
    mustReject "source.state_binder" do
      discard <| (SourceScope.resolve info {
        owner, coordinates := #[], readouts := #[{path, stateBinder := 0}] }).run 524288
    let record := mkConst (support ++ `registration)
    let recordType ← inferType record
    unless ← isDefEq recordType.getAppArgs[1]! info.type do
      throwError "full original statement not preserved: {name}"
    checkWithKernel record
    let law ← mkAppM (family ++ `Arena.Law)
      #[mkConst (support ++ `arena), mkConst (support ++ `actual)]
    if support == `Reg.Support.LegacyRelations.Preemption then
      mustReject "source.statement_reconstruction" do
        discard <| (SourceScope.reconstruct info.type law).run 524288
    else
      discard <| (SourceScope.reconstruct info.type law).run 524288
    mustReject "source.statement_reconstruction" do
      discard <| (SourceScope.reconstruct info.type (mkConst ``True)).run 524288
    logInfo m!"[PASS] full statement and all family obligations: {name}"

end LeanInformationAuditRegTests.LegacyRelationsSourceBoundary
