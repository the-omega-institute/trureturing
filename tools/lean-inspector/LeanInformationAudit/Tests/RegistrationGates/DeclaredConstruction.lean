import LeanInformationAudit.Registry

namespace LeanInformationAudit.Tests.DeclaredConstruction
open Lean Meta TemplateAudit

private def agrees (result : Except String (Expr × Nat)) (expected : Expr) : Bool :=
  match result with
  | .ok (actual, work) => work > 0 && actual.equal expected
  | _ => false

private def incomplete (result : Except String α) (rule : String) : Bool :=
  match result with
  | .error message => message == "incomplete_closure:E8." ++ rule
  | _ => false

run_meta do
  let x := FVarId.mk `localInput
  let ty := mkConst `Nat
  let metadata := MData.empty.insert `retained (DataValue.ofNat 7)
  let expression := Expr.letE `namedLet ty (.bvar 0)
    (.lam `namedLambda (.bvar 1)
      (.mdata metadata (.app (.bvar 2) (.app (.bvar 1) (.bvar 0)))) .instImplicit) false
  let argument := Expr.app (.fvar x) (.bvar 0)
  let samples := #[expression, .forallE `namedPi ty expression .implicit,
    .proj `Prod 1 (.app (.bvar 0) expression)]
  let mut substitution := true
  let mut lifting := true
  let mut abstraction := true
  for sample in samples do
    substitution := substitution && agrees (PlanTransform.substituteExpr sample argument)
      (sample.instantiate1 argument)
    lifting := lifting && agrees (PlanTransform.liftExpr sample 0 3) (sample.liftLooseBVars 0 3)
    let instantiated := sample.instantiate1 argument
    abstraction := abstraction && agrees (PlanTransform.abstractExpr instantiated x)
      (instantiated.abstract #[.fvar x])
  let deep := (List.range 300).foldl (fun expr _ => Expr.app (.const `id []) expr) (.bvar 0)
  let exprWork := PlanTransform.substituteExpr expression argument 0 0
  let universeExpr := Expr.const `universeTest [
    .max (.param `u) (.succ (.param `v)), .imax (.param `u) (.param `v)]
  let mut universes := true
  for u in #[Level.zero, .succ .zero, .param `rigid, .max (.param `rigid) (.succ .zero)] do
    for v in #[Level.zero, .succ .zero, .param `other] do
      universes := universes && agrees (PlanTransform.instantiateExpr universeExpr [`u, `v] [u, v])
        (universeExpr.instantiateLevelParams [`u, `v] [u, v])
  let p := PlanNode.lam (.atom ty) (.mdata metadata (.app (.atom (.bvar 1)) (.atom (.bvar 0)))) .implicit
  let expressionP := Expr.lam .anonymous ty (.mdata metadata (.app (.bvar 1) (.bvar 0))) .implicit
  let origin := match PlanTransform.substitutePlan p (.supplied argument) with
    | .ok (.lam _ (.mdata _ (.app (.supplied retained) (.atom (.bvar 0)))) .implicit, _) =>
      retained.equal argument
    | _ => false
  let retained := PlanNode.audit (.typeNode (.atom (.bvar 0)))
    (.expanded (.app (.bvar 0) (.fvar x)) (.proofLeaf (.app (.bvar 0) ty)))
  let retainedOk := match PlanTransform.substitutePlan retained (.atom argument) with
    | .ok (.audit (.typeNode (.atom t)) (.expanded raw (.proofLeaf pt)), _) =>
      t.equal argument && raw.equal (.app argument (.fvar x)) &&
        pt.equal (.app argument ty)
    | _ => false
  let materialized := PlanTransform.toExpr p
  let exactWork := match materialized with
    | .ok (_, work) => (PlanTransform.toExpr p work).isOk &&
        incomplete (PlanTransform.toExpr p (work - 1)) "construction_work"
    | _ => false
  for (label, ok) in #[
      ("bounded_substitution_capture_avoiding", substitution && lifting && abstraction),
      ("deep_application_substitution_incomplete", incomplete
        (PlanTransform.substituteExpr deep argument) "construction_depth"),
      ("raw_substitution_work_charged", incomplete exprWork "construction_work"),
      ("universe_instantiation_work_charged", incomplete
        (PlanTransform.instantiateExpr universeExpr [`u, `v] [.zero, .zero] 0) "construction_work"),
      ("universe_instantiation_matches_lean", universes),
      ("plan_materialization_work_charged", exactWork),
      ("abstraction_work_charged", incomplete
        (PlanTransform.abstractExpr argument x 0 0) "construction_work"),
      ("retained_syntax_and_supplied_origins_preserved", origin && retainedOk &&
        agrees materialized expressionP)] do
    (if ok then logInfo else logError) m!"[{if ok then "PASS" else "FAIL"}] {label}"

run_meta do
  let nested : MetaM Unit := withCurrHeartbeats do
    IO.addHeartbeats 600
    Core.checkMaxHeartbeats "nested work fixture"
  let rejected ← withOptions (·.set `maxHeartbeats (1 : Nat)) <| tryCatchRuntimeEx
    (withCumulativeBudget do nested; nested; pure false)
    (fun ex => pure ex.isMaxHeartbeat)
  let positive ← tryCatchRuntimeEx
    (withCumulativeBudget (pure true)) (fun _ => pure false)
  for (label, ok) in #[
      ("nested_meta_work_remains_cumulative", rejected),
      ("bounded_meta_work_accepted", positive)] do
    (if ok then logInfo else logError) m!"[{if ok then "PASS" else "FAIL"}] {label}"

end LeanInformationAudit.Tests.DeclaredConstruction
