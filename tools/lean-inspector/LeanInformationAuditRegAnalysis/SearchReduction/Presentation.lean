import LeanInformationAuditRegAnalysis.SearchReduction.Runner

/-! Bounded presentation certificates. No candidate proof, simp extension,
induction, unbounded theorem search or submitted equivalence certificate is consulted. -/
namespace LeanInformationAudit.SearchReduction
open Lean Meta Elab Tactic
open LeanInformationAudit.Tests.SearchReduction (Run Failure)

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
private partial def equivalent (index : FactIndex) (left right : Expr) (xs : Array Expr := #[]) : MetaM (Option Expr) := do
  let left ← withTransparency .reducible <| whnf left
  let right ← withTransparency .reducible <| whnf right
  match left, right with
  | .forallE name domain body kind, .forallE _ domain' body' kind' =>
    if kind != kind' then return none
    unless ← withTransparency .reducible <| isDefEq domain domain' do return none
    withLocalDecl name kind domain fun x =>
      equivalent index (body.instantiate1 x) (body'.instantiate1 x) (xs.push x)
  | .forallE .., _ | _, .forallE .. => return none
  | _, _ =>
    let type ← mkAppM ``Iff #[left, right]
    let goal ← mkFreshExprMVar type
    let withTruth ← goal.mvarId!.assert `_presentationTruth (mkConst ``True) (mkConst ``True.intro)
    let (_, next) ← withTruth.intro1
    unless ← closePresentation index next do return none
    let proof ← mkLambdaFVars xs (← instantiateMVars goal)
    let type ← mkForallFVars xs type
    let levels := (collectLevelParams {} type).params.toList
    discard <| checkProof (← mkFreshUserName `_searchReduction.presentation) levels type proof
    return some proof

/-- Source projections preserve its entire telescope. Iff elimination supplies
its two implication directions, never an unproved equivalence licence. -/
partial def restatementConversion (target source : Expr) (index : FactIndex := {}) :
    MetaM (Option Expr) := do
  let saved ← saveState
  if let some equivalence ← equivalent index target source then
    return ← withLocalDeclD `_source source fun h =>
      forallTelescopeReducing target fun xs _ => do
        let proof ← mkAppM ``Iff.mpr #[mkAppN equivalence xs, mkAppN h xs]
        let proof ← mkLambdaFVars #[h] (← mkLambdaFVars xs proof)
        pure (some proof)
  saved.restore
  forallTelescopeReducing source fun xs body => do
    let body ← withTransparency .reducible <| whnf body
    let projections := if body.isAppOfArity ``And 2 then #[``And.left, ``And.right]
      else if body.isAppOfArity ``Iff 2 then #[``Iff.mp, ``Iff.mpr] else #[]
    for projection in projections do
      let before ← saveState
      let projected ← withLocalDeclD `_source source fun h => do
        let value ← mkAppM projection #[mkAppN h xs]
        let type ← mkForallFVars xs (← inferType value)
        pure type
      if let some conversion ← restatementConversion target projected index then
        return ← withLocalDeclD `_source source fun h => do
          let value ← mkAppM projection #[mkAppN h xs]
          let value ← mkLambdaFVars xs value
          pure (some (← mkLambdaFVars #[h] (mkApp conversion value)))
      before.restore
    return none

/-- Both baseline certification and structure exclusion use this procedure. -/
def certifiedRestatement (target source : Expr) (index : FactIndex := {}) : MetaM Bool := do
  return (← restatementConversion target source index).isSome

/-- Enumerate actual B statements in stable order. Retrieval successes are only
priorities; the remaining statements are still checked with the same rules. -/
def baselinePresentation (env : Environment) (levels : List Name) (target : Expr)
    (preferred : Array Name := #[]) : IO (Run × Option PresentationEvidence × String) := do
  let work : CoreM (Option PresentationEvidence) := MetaM.run' do
    let index ← factIndex
    let names := preferred ++ index.matcherConstants.map (·.1)
    let mut seen : NameSet := {}
    for name in names do
      if seen.contains name then continue
      seen := seen.insert name
      let some info := (env.setExporting false).find? name | continue
      if info.isUnsafe || (name.isInternalDetail && !isPrivateName name) then continue
      let saved ← saveState
      let value ← mkConstWithFreshMVarLevels name
      let source ← inferType value
      unless ← isProp source do
        saved.restore
        continue
      if let some conversion ← restatementConversion target source index then
        let conversion ← inlineGenerated env (← instantiateMVars conversion)
        let proof ← instantiateMVars (mkApp conversion value)
        let conversionType ← instantiateMVars (← inferType conversion)
        let axioms ← checkProof (← mkFreshUserName `_searchReduction.baselinePresentation)
          levels target proof
        discard <| checkProof (← mkFreshUserName `_searchReduction.baselineConversion)
          levels conversionType conversion
        return some {source := name, conversionType, conversion, proof, axioms}
      saved.restore
    return none
  let context : Core.Context := {
    fileName := "<R_v1 presentation>", fileMap := default, options := options,
    initHeartbeats := ← IO.getNumHeartbeats, maxHeartbeats := budget * 1000 }
  match ← (work.run context {env}).toIO' with
  | .ok (some evidence, state) =>
    if state.messages.hasErrors then return (.incomplete .execution, none, "search.presentation_errors")
    return (.found, some evidence, "")
  | .ok (none, state) =>
    if state.messages.hasErrors then return (.incomplete .execution, none, "search.presentation_errors")
    return (.exhausted, none, "")
  | .error ex =>
    let failure := if ex.isMaxHeartbeat then Failure.heartbeat
      else if ex.isInterrupt then .cancelled else .execution
    return (.incomplete failure, none, ← ex.toMessageData.toString)

end LeanInformationAudit.SearchReduction
