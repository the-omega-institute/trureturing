import LeanInformationAuditRegAnalysis.SearchReduction.Runner

/-! Bounded presentation certificates. No candidate proof, simp extension,
induction, unbounded theorem search or submitted equivalence certificate is consulted. -/
namespace LeanInformationAudit.SearchReduction
open Lean Meta Elab Tactic

/-- Logical introduction/projection and the pinned `omega` procedure are the
finite presentation rules. Opaque arithmetic subterms remain atoms. -/
private partial def closePresentation (index : FactIndex) (goal : MVarId) : MetaM Bool := goal.withContext do
  let saved ← saveState
  let mut facts := #[]
  for decl in ← getLCtx do
    unless decl.isImplementationDetail do
      if ← isProp decl.type then facts := facts ++ (← components decl.toExpr)
  if ← presentation goal facts then return true
  let type ← withTransparency .reducible <| whnf (← goal.getType)
  if type.isForall then
    let (_, next) ← goal.intro1
    if ← closePresentation index next then return true
  else if type.isAppOfArity ``And 2 || type.isAppOfArity ``Iff 2 then
    let ctor := if type.isAppOfArity ``And 2 then ``And.intro else ``Iff.intro
    let goals ← goal.apply (← mkConstWithFreshMVarLevels ctor)
    if ← goals.allM (closePresentation index) then return true
  else
    try
      let leaves ← (structural goal #[]).run' index
      if ← leaves.allM (fun leaf => do
          let goals ← (Term.withoutErrToSorry <| Tactic.run leaf
            (evalTactic (← `(tactic| omega)))).run'
          pure goals.isEmpty) then return true
    catch ex =>
      if ex.isRuntime || ex.isInterrupt || ex.isMaxHeartbeat then throw ex
  saved.restore
  return false

/-- Match every binder, its kind and its dependent domain before certifying the
terminal equivalence. No premise, parameter or universe is silently erased. -/
private partial def equivalent (index : FactIndex) (left right : Expr) (xs : Array Expr := #[]) : MetaM Bool := do
  let left ← withTransparency .reducible <| whnf left
  let right ← withTransparency .reducible <| whnf right
  match left, right with
  | .forallE name domain body kind, .forallE _ domain' body' kind' =>
    if kind != kind' then return false
    unless ← withTransparency .reducible <| isDefEq domain domain' do return false
    withLocalDecl name kind domain fun x =>
      equivalent index (body.instantiate1 x) (body'.instantiate1 x) (xs.push x)
  | .forallE .., _ | _, .forallE .. => return false
  | _, _ =>
    let type ← mkAppM ``Iff #[left, right]
    let goal ← mkFreshExprMVar type
    let withTruth ← goal.mvarId!.assert `_presentationTruth (mkConst ``True) (mkConst ``True.intro)
    let (_, next) ← withTruth.intro1
    unless ← closePresentation index next do return false
    let proof ← mkLambdaFVars xs (← instantiateMVars goal)
    let type ← mkForallFVars xs type
    let levels := (collectLevelParams {} type).params.toList
    discard <| checkProof (← mkFreshUserName `_searchReduction.presentation) levels type proof
    return true

/-- Source projections preserve its entire telescope. Iff elimination supplies
its two implication directions, never an unproved equivalence licence. -/
partial def certifiedRestatement (target source : Expr) (index : FactIndex := {}) : MetaM Bool := do
  let saved ← saveState
  if ← equivalent index target source then return true
  saved.restore
  forallTelescopeReducing source fun xs body => do
    let body ← withTransparency .reducible <| whnf body
    if body.isAppOfArity ``And 2 then
      return (← certifiedRestatement target (← mkForallFVars xs body.appFn!.appArg!) index) ||
        (← certifiedRestatement target (← mkForallFVars xs body.appArg!) index)
    if body.isAppOfArity ``Iff 2 then
      let forward ← mkForallFVars xs (← mkArrow body.appFn!.appArg! body.appArg!)
      let backward ← mkForallFVars xs (← mkArrow body.appArg! body.appFn!.appArg!)
      return (← certifiedRestatement target forward index) || (← certifiedRestatement target backward index)
    return false

end LeanInformationAudit.SearchReduction
