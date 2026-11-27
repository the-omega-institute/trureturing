module
public import Lean
import Init.WF

/-! Specialize well-founded unfolding to steps that respect pointwise equality of recursive calls. -/

namespace OmegaChecks.InitCompiler.Recursion

section
variable {α : Sort u} {motive : α → Sort v} (measure : α → Nat)
variable (step : (x : α) → ((y : α) → InvImage (· < ·) measure y x → motive y) → motive x)
private abbrev Pointwise := ∀ x left right, (∀ y h, left y h = right y h) → step x left = step x right

private theorem fuelIrrel (cong : Pointwise measure step) (fuel other : Nat) (x : α)
    (hx : measure x < fuel) (hx' : measure x < other) :
    WellFounded.Nat.fix.go measure step fuel x hx = WellFounded.Nat.fix.go measure step other x hx' := by
  induction fuel generalizing x other with
  | zero => exact (Nat.not_succ_le_zero _ hx).elim
  | succ n ih =>
    cases other with
    | zero => exact (Nat.not_succ_le_zero _ hx').elim
    | succ m => exact cong x _ _ fun y hy => ih m y _ _

public theorem fixPointwise
    (cong : ∀ x left right, (∀ y h, left y h = right y h) → step x left = step x right) (x : α) :
    WellFounded.Nat.fix measure step x = step x (fun y _ => WellFounded.Nat.fix measure step y) := by
  have reduce (n) (hn : measure x < n) (eq : n = measure x + 1) :
      WellFounded.Nat.fix.go measure step n x hn = step x (fun y _ => WellFounded.Nat.fix measure step y) := by
    cases eq
    exact cong x _ _ fun y hy => fuelIrrel measure step cong _ _ y _ _
  exact reduce _ _ (WellFounded.Nat.eager_eq _)
end

open Lean Meta

/-- Keep the constructive proof closed when it is copied into the empty kernel. -/
public def loadRule : IO ConstantInfo := do
  let owner := `OmegaChecks.InitCompiler.Recursion
  let env ← importModules #[{module := owner}] {} (level := .private)
  let some (.thmInfo ci) := env.find? (owner ++ `fixPointwise) | throw <| IO.userError "missing fixed point proof"
  let expand := fun n => isPrivateName n && env.getModuleIdxFor? n == env.getModuleIdx? owner
  let expandTerm (e : Expr) := (Meta.deltaExpand e expand (allowOpaque := true)).toIO'
    {fileName := "<fixed point proof>", fileMap := default} {env}
  return .thmInfo {ci with value := ← expandTerm ci.value, type := ← expandTerm ci.type}

private partial def solveBranch (g : MVarId) (agree : FVarId) (depth : Nat) : MetaM Unit := g.withContext do
  if (← observing? g.refl).isSome then return
  if let some (_, lhs, rhs) := (← instantiateMVars (← g.getType)).eq? then
    if lhs.getAppFn.isFVar && lhs.getAppNumArgs == 2 then
      -- Splitting the state can reintroduce its dependent recursive-call hypothesis.
      -- Recover it from the two functions, including the concrete decrease proof.
      let bound := (← getLCtx).findDecl? fun decl => do
        let .forallE _ _ (.forallE _ _ conclusion _) _ := decl.type | none
        let some (_, l, r) := conclusion.eq? | none
        guard (l.getAppFn == lhs.getAppFn && r.getAppFn == rhs.getAppFn)
        return decl
      if let some decl := bound then
        let term := mkAppN decl.toExpr lhs.getAppArgs
        if ← isDefEq (← inferType term) (← g.getType) then
          g.assign term
          return
  if (← observing? do
    let rest ← g.apply (mkFVar agree)
    guard rest.isEmpty).isSome then return
  if depth == 0 then throwError "recursive step requires further congruence"
  if (← observing? do
    let result ← g.rewrite (← g.getType) (mkFVar agree)
    guard result.mvarIds.isEmpty
    let next ← g.replaceTargetEq result.eNew result.eqProof
    solveBranch next agree (depth - 1)).isSome then return
  if let some branches ← splitTarget? g (useNewSemantics := true) then
    for branch in branches do solveBranch branch agree (depth - 1)
    return
  for subgoal in ← g.congrCore do solveBranch subgoal agree (depth - 1)

private partial def openState (g : MVarId) (vars : List FVarId) : MetaM (List MVarId) := g.withContext do
  let x :: rest := vars | return [g]
  let type ← inferType (mkFVar x)
  unless [`PSigma, `Prod, `PSum, `Sum].any type.getAppFn.isConstOf do return ← openState g rest
  let mut result := []
  for branch in ← g.cases x do
    result := result ++ (← openState branch.mvarId ((branch.fields.toList.map Expr.fvarId!) ++ rest))
  return result

private def stepProof (type : Expr) : MetaM Expr := do
  let goal ← mkFreshExprSyntheticOpaqueMVar type
  let (x, g) ← goal.mvarId!.intro1
  for branch in ← openState g [x] do
    let (args, target) ← branch.introN 3
    let (some target, _) ← dsimpGoal target (← Simp.mkContext) | continue
    solveBranch target args[2]! 12
  instantiateMVars goal

private def pointwiseApplication (rule : ConstantInfo) (levels : List Level) (args : Array Expr) : MetaM Expr := do
  let mut type := rule.type.instantiateLevelParams rule.levelParams levels
  for arg in args[:4] do type := type.bindingBody!.instantiate1 arg
  let proof ← stepProof type.bindingDomain!
  let value := (rule.value! (allowOpaque := true)).instantiateLevelParams rule.levelParams levels
  return value.beta (args[:4].toArray ++ #[proof, args[4]!])

private partial def closeEquation (goal : MVarId) (fuel : Nat) : MetaM Unit := goal.withContext do
  if (← observing? goal.refl).isSome then return
  let fuel + 1 := fuel | throwError "unfolded branches differ"
  let (some reduced, _) ← dsimpGoal goal (← Simp.mkContext) | return
  if (← observing? reduced.refl).isSome then return
  let some branches ← splitTarget? reduced (useNewSemantics := true) | throwError "no matching branch"
  for g in branches do closeEquation g fuel

/-- Generated proofs may use function extensionality to unpack the recursion state.
Case-analyze the actual tuple before applying the fixed point law to each constructor. -/
private def unfoldingEquation (rule : ConstantInfo) (type : Expr) (alignNatBranches : Bool) : MetaM Expr := do
  let proof ← mkFreshExprSyntheticOpaqueMVar type
  let (xs, g) ← proof.mvarId!.intros
  let some x := xs.back? | throwError "missing recursion state"
  for branch in ← openState g [x] do
    branch.withContext do
      let some (_, lhs, _) := (← branch.getType).eq? | throwError "expected equation"
      let .const name levels := lhs.getAppFn | throwError "expected a named recursive function"
      let ci ← getConstInfo name
      let some value := ci.value? | throwError "expected a recursive definition"
      let rhs := (value.instantiateLevelParams ci.levelParams levels).beta lhs.getAppArgs
      let eq ← if rhs.isAppOfArity `WellFounded.fix 6 then
        pure (mkAppN (mkConst `WellFounded.fix_eq rhs.getAppFn.constLevels!) rhs.getAppArgs)
      else if rhs.isAppOfArity `WellFounded.Nat.fix 5 then
        pointwiseApplication rule rhs.getAppFn.constLevels! rhs.getAppArgs
      else throwError "unexpected fixed point"
      if rhs.isAppOfArity `WellFounded.Nat.fix 5 && !alignNatBranches then
        branch.assign eq
        return
      let some (_, _, unfolded) := (← inferType eq).eq? | throwError "missing fixed point equation"
      let some (_, _, target) := (← branch.getType).eq? | throwError "missing equation target"
      let rest ← mkFreshExprSyntheticOpaqueMVar (← mkEq unfolded target)
      closeEquation rest.mvarId! 6
      branch.assign (← mkEqTrans eq rest)
  instantiateMVars proof

/-- Inline the fixed point law after proving congruence for the actual recursive step. -/
public def specialize (env : Environment) (rule official : ConstantInfo) (body : Expr)
    (alignNatBranches := false) : IO Expr := do
  let used := body.getUsedConstantsAsSet
  unless used.contains `WellFounded.Nat.fix_eq ||
      (used.contains `WellFounded.fix_eq && used.contains `funext) do return body
  let action : MetaM Expr := do
    if used.contains `funext then
      if let some result ← observing? (unfoldingEquation rule official.type alignNatBranches) then return result
    Meta.transform body (post := fun e => do
      unless e.isAppOfArity `WellFounded.Nat.fix_eq 5 do return .done e
      let some term ← observing? (pointwiseApplication rule e.getAppFn.constLevels! e.getAppArgs) | return .done e
      return .done term)
  try
    let inlineGenerated : MetaM Expr := do
      let result ← action
      Meta.deltaExpand result (fun n => !env.contains n) (allowOpaque := true)
    let result ← inlineGenerated.run' |>.toIO' {fileName := "<fixed point congruence>", fileMap := default} {env}
    if result.hasFVar || result.hasMVar || result.hasLooseBVars then return body
    return result
  catch _ => return body

end OmegaChecks.InitCompiler.Recursion
