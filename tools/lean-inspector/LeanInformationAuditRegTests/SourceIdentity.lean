import LeanInformationAuditRegTests.ExplicitSourceOperands

open Lean Meta LeanInformationAudit RegistrationGates
namespace LeanInformationAuditRegTests.SourceIdentity

universe u v
theorem target (α : Type u) (x : α) : x = x := rfl
def aliasProp (p : Prop) : Prop := p
def deltaProp : Prop := ∀ (α : Type u) (x : α), x = x
theorem twoVariables (x y : Nat) : x = x ∧ y = y := ⟨rfl, rfl⟩
theorem otherTrue : True := True.intro
theorem proofTarget : True.intro = True.intro := rfl

private def reject (name : Name) (label rule : String) (e : Expr) : MetaM Unit := do
  let options ← getOptions
  let result ← try
    discard <| SourceOperands.check name #[e] 524288
    pure "accepted"
  catch error => error.toMessageData.toString
  unless result.contains rule do throwError "{label}: expected {rule}, got {result}"
  unless (← getOptions) == options do throwError "{label}: options leaked after exception"
  logInfo m!"[PASS] identity_{label}: {rule}"

private def reachesConversion (name : Name) (e : Expr) : MetaM Unit := do
  let initial ← argumentIdentityState name 524288
  let (_, state) ← (argumentIdentityNode (← getEnv) e (deferStatementApart := true)).run initial
  unless state.unclassified.isSome && !state.forbidden && !state.incomplete do
    throwError "control did not reach SourceOperands conversion: {e}"

private def suite (enabled : Bool) : MetaM Unit :=
    withOptions (smartUnfolding.set · enabled) <| TemplateAudit.withCumulativeBudget do
  let name := ``target
  let statement := (← getConstInfo name).type
  let beta := mkApp (.lam `p (mkSort .zero) (.bvar 0) .default) statement
  let zeta := Expr.letE `p (mkSort .zero) statement (.bvar 0) false
  let delta := mkConst ``deltaProp [.param `u]
  let aliased := mkApp (mkConst ``aliasProp) statement
  let options ← getOptions
  -- Both options prime the same Meta cache; the checker changes only its call.
  for e in #[beta, zeta, delta, aliased] do
    unless ← withTransparency .all <| isDefEq e statement do throwError "outside before"
  reject name "exact" "forbidden_dependency:source.operand_identity" statement
  for (label, e) in #[("beta", beta), ("zeta", zeta), ("delta", delta), ("alias", aliased)] do
    reachesConversion name e
    withFreshCache do
      reject name (label ++ "_cold") "forbidden_dependency:source.operand_identity" e
    reject name label "forbidden_dependency:source.operand_identity" e
  let rigid := Expr.forallE `α (mkSort (.succ (.param `v)))
    (.forallE `x (.bvar 0) (mkApp3 (mkConst ``Eq [.succ (.param `v)])
      (.bvar 1) (.bvar 0) (.bvar 0)) .default) .default
  reachesConversion name rigid
  unless !(← withTransparency .all <| isDefEq rigid statement) do throwError "rigid universes unified"
  discard <| SourceOperands.check name #[rigid] 524288
  unless (← getOptions) == options do throwError "options leaked after success"
  let distinct ← withLocalDeclD `x (mkConst ``Nat) fun x =>
    withLocalDeclD `y (mkConst ``Nat) fun y => do
      mkForallFVars #[x, y] (mkApp2 (mkConst ``And) (← mkEq x x) (← mkEq x y))
  reachesConversion ``twoVariables distinct
  unless !(← withTransparency .all <| isDefEq distinct (← getConstInfo ``twoVariables).type) do
    throwError "rigid variables unified"
  discard <| SourceOperands.check ``twoVariables #[distinct] 524288
  let mvar ← mkFreshExprMVar (mkSort .zero)
  reachesConversion name mvar
  reject name "expression_mvar" "incomplete_closure:source.identity_metavariable" mvar
  unless !(← mvar.mvarId!.isAssigned) do throwError "identity assigned metavariable"
  let level ← mkFreshLevelMVar
  let levelCandidate := mkConst ``deltaProp [level]
  reachesConversion name levelCandidate
  reject name "universe_mvar" "incomplete_closure:source.identity_metavariable" levelCandidate
  unless (← instantiateLevelMVars level) == level do throwError "identity assigned universe"
  let opaqueProof := Expr.letE `proof statement (mkConst name [.param `u])
    (mkConst ``True.intro) false
  discard <| SourceOperands.check name #[opaqueProof] 524288
  let discarded := mkApp (.lam `ignored (mkSort .zero) (mkNatLit 0) .default) aliased
  reject name "raw_discarded" "forbidden_dependency:source.operand_identity" discarded
  let letDiscarded := Expr.letE `ignored (mkSort .zero) aliased (mkNatLit 0) false
  reject name "raw_let" "forbidden_dependency:source.operand_identity" letDiscarded
  let proofLet := Expr.letE `ignored statement (mkConst name [.param `u]) (mkNatLit 0) false
  reject name "raw_proof_let" "forbidden_dependency:source.operand_identity" proofLet
  reject name "dictionary" "forbidden_dependency:source.operand_identity"
    (mkApp (mkConst ``Decidable) aliased)
  let proof ← mkEq (mkConst ``otherTrue) (mkConst ``True.intro)
  reachesConversion ``proofTarget proof
  reject ``proofTarget "proof_irrelevance" "forbidden_dependency:source.operand_identity" proof
  -- The exception is raised by conversion itself, after the raw precheck.
  let result ← try
    withCanUnfoldPred (fun _ info => do
      if info.name == ``deltaProp then
        if smartUnfolding.get (← getOptions) then throwError "identity option not local"
        throwError "identity_conversion_exception"
      pure true) do
      withFreshCache do discard <| SourceOperands.check name #[delta] 524288
    pure "accepted"
  catch error => error.toMessageData.toString
  unless result.contains "identity_conversion_exception" do
    throwError "conversion exception swallowed: {result}"
  unless (← getOptions) == options do throwError "conversion exception leaked options"
  let exhausted ← tryCatchRuntimeEx
    (withCanUnfoldPred (fun _ info => do
      if info.name == ``deltaProp then Core.throwMaxHeartbeat `identityTest `maxHeartbeats 100000
      pure true) <| withFreshCache do
      discard <| SourceOperands.check name #[delta] 524288
      pure false)
    (fun error => pure error.isMaxHeartbeat)
  unless exhausted do throwError "heartbeat exception converted to a verdict"
  unless (← getOptions) == options do throwError "heartbeat exception leaked options"
  for e in #[beta, zeta, delta, aliased] do
    unless ← withTransparency .all <| isDefEq e statement do throwError "outside after"
  logInfo m!"[PASS] identity_cache_order option={enabled}; success/exception restoration"

-- Each order starts cold, then runs against the preceding option's warm cache.
run_meta withFreshCache do
  suite true
  suite false
  suite true
run_meta withFreshCache do
  suite false
  suite true
  suite false

end LeanInformationAuditRegTests.SourceIdentity
