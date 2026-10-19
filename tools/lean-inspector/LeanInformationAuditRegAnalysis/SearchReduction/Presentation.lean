import LeanInformationAuditRegAnalysis.SearchReduction.PresentationSyntax

/-! Bounded presentation certificates. No candidate proof, simp extension,
induction, unbounded theorem search or submitted equivalence certificate is consulted. -/
namespace LeanInformationAudit.SearchReduction
open Lean Meta Elab Tactic
open LeanInformationAudit.Tests.SearchReduction (Run Failure)

/-- Logical introduction/projection and the pinned `omega` procedure are the
finite presentation rules. Opaque arithmetic subterms remain atoms. -/
private partial def closePresentation (index : FactIndex) (extra : Array Expr)
    (goal : MVarId) : MetaM Bool := goal.withContext do
  let saved ← saveState
  let mut facts := extra
  for decl in ← getLCtx do
    unless decl.isImplementationDetail do
      if ← isProp decl.type then facts := facts ++ (← components decl.toExpr)
  let type ← withTransparency .reducible <| whnf (← goal.getType)
  if type.isForall then
    let (_, next) ← goal.intro1
    if ← closePresentation index extra next then return true
  else if type.isAppOfArity ``And 2 || type.isAppOfArity ``Iff 2 then
    let ctor := if type.isAppOfArity ``And 2 then ``And.intro else ``Iff.intro
    let goals ← goal.apply (← mkConstWithFreshMVarLevels ctor)
    if ← goals.allM (closePresentation index extra) then return true
  else
    if ← presentation goal facts then return true
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
private partial def equivalent (index : FactIndex) (extra : Array Expr)
    (left right : Expr) (xs : Array Expr := #[]) : MetaM (Option Expr) := do
  let left ← withTransparency .reducible <| whnf left
  let right ← withTransparency .reducible <| whnf right
  match left, right with
  | .forallE name domain body kind, .forallE _ domain' body' kind' =>
    if kind != kind' then return none
    unless ← withTransparency .reducible <| isDefEq domain domain' do return none
    withLocalDecl name kind domain fun x =>
      equivalent index extra (body.instantiate1 x) (body'.instantiate1 x) (xs.push x)
  | .forallE .., _ | _, .forallE .. => return none
  | _, _ =>
    -- Delta-reduce explicit subterms as well as the proposition's head.
    -- This uses definitional equality without any simp extension or theorem.
    let left ← withReducible <| reduce left (skipTypes := false)
    let right ← withReducible <| reduce right (skipTypes := false)
    let mut facts := #[]
    for fact in extra do
      let mut value := fact
      for x in xs do
        unless (← withTransparency .reducible <| whnf (← inferType value)).isForall do break
        value := mkApp value x
      facts := facts ++ (← components value)
    let type ← mkAppM ``Iff #[left, right]
    let goal ← mkFreshExprMVar type
    let withTruth ← goal.mvarId!.assert `_presentationTruth (mkConst ``True) (mkConst ``True.intro)
    let (_, next) ← withTruth.intro1
    unless ← closePresentation index facts next do return none
    let proof ← mkLambdaFVars xs (← instantiateMVars goal)
    let type ← mkForallFVars xs type
    let levels := (collectLevelParams {} type).params.toList
    discard <| checkProof (← mkFreshUserName `_searchReduction.presentation) levels type proof
    return some proof

/-- Source projections preserve its entire telescope. Iff elimination supplies
its two implication directions, never an unproved equivalence licence. -/
private partial def compatibleBinders (target source : Expr) : MetaM Bool := do
  let source ← withTransparency .reducible <| whnf source
  if let .forallE name domain body kind := source then
    let target ← withTransparency .reducible <| whnf target
    let .forallE _ domain' body' kind' := target | return false
    if kind != kind' then return false
    unless ← withTransparency .reducible <| isDefEq domain domain' do return false
    return ← withLocalDecl name kind domain fun x =>
      compatibleBinders (body'.instantiate1 x) (body.instantiate1 x)
  -- A source And/Iff projection can introduce further target binders. It
  -- cannot remove or change any binder already outside that connective.
  if source.isAppOfArity ``And 2 || source.isAppOfArity ``Iff 2 then return true
  return !(← withTransparency .reducible <| whnf target).isForall

partial def restatementConversion (target source : Expr) (index : FactIndex := {})
    (extra : Array Expr := #[]) :
    MetaM (Option Expr) := do
  unless ← compatibleBinders target source do return none
  let saved ← saveState
  if let some equivalence ← equivalent index extra target source then
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
      if let some conversion ← restatementConversion target projected index extra then
        return ← withLocalDeclD `_source source fun h => do
          let value ← mkAppM projection #[mkAppN h xs]
          let value ← mkLambdaFVars xs value
          pure (some (← mkLambdaFVars #[h] (mkApp conversion value)))
      before.restore
    return none

/-- The wide structure exclusion retains the legacy conversion relation. -/
def certifiedRestatement (target source : Expr) (index : FactIndex := {}) : MetaM Bool := do
  return (← restatementConversion target source index).isSome

/-- A syntactic rejection of data-valued constants avoids elaborating their
telescopes. Unknown and dependent result sorts remain candidates. -/
private def proofCandidate (env : Environment) (type : Expr) : Bool := Id.run do
  let body := type.getForallBody.consumeMData
  if body.isSort then return false
  let .const name levels := body.getAppFn | return true
  let some info := (env.setExporting false).find? name | return true
  let result := (info.type.instantiateLevelParams info.levelParams levels).getForallBody
  if let .sort (.succ _) := result then return false
  return true

private def inductiveHead (env : Environment) (e : Expr) : Option Name := do
  let name ← e.consumeMData.getAppFn.consumeMData.constName?
  match (env.setExporting false).find? name with
  | some (.inductInfo _) => some name
  | _ => none

private def propositionSort (env : Environment) (e : Expr) : Option Bool := do
  if e.consumeMData.isSort then return false
  let .const name levels := e.consumeMData.getAppFn.consumeMData | none
  let info ← (env.setExporting false).find? name
  match (info.type.instantiateLevelParams info.levelParams levels).getForallBody.consumeMData with
  | .sort .zero => some true
  | .sort (.succ _) => some false
  | _ => none

/-- Reject only rigid telescope mismatches before allocating metavariables.
Reducible or dependent heads stay in the full definitional-equality check. -/
private partial def rigidlyCompatible (env : Environment) (target source : Expr) : Bool :=
  match target.consumeMData, source.consumeMData with
  | .forallE _ domain body kind, .forallE _ domain' body' kind' =>
    kind == kind' &&
      (match propositionSort env domain, propositionSort env domain' with
        | some left, some right => left == right | _, _ => true) &&
      !(domain.isSort && (inductiveHead env domain').isSome) &&
      !(domain'.isSort && (inductiveHead env domain).isSome) &&
      (match inductiveHead env domain, inductiveHead env domain' with
        | some left, some right => left == right | _, _ => true) &&
      rigidlyCompatible env body body'
  | .forallE .., source =>
    match inductiveHead env source with
    | some name => name == ``And || name == ``Iff
    | none => true
  | target, .forallE .. => (inductiveHead env target).isNone && !target.isSort
  | _, _ => true

private def baselineSource (env : Environment) (levels : List Name) (target : Expr)
    (name : Name) : IO (Attempt × Option PresentationEvidence × Nat × Nat) := do
  let evidence ← IO.mkRef (none : Option PresentationEvidence)
  let converted ← IO.mkRef (0 : Nat)
  let verified ← IO.mkRef (0 : Nat)
  let started ← IO.getNumHeartbeats
  let row ← attempt env levels target s!"presentation/{name}" fun goal => do
    let value ← mkConstWithFreshMVarLevels name
    let source ← inferType value
    unless ← isProp source do return false
    let start ← IO.getNumHeartbeats
    let result ← singleSourceConversion target source
    converted.set ((← IO.getNumHeartbeats) - start)
    if let some conversion := result then
      let conversion ← inlineGenerated env (← instantiateMVars conversion)
      let proof ← instantiateMVars (mkApp conversion value)
      let conversionType ← instantiateMVars (← inferType conversion)
      let start ← IO.getNumHeartbeats
      let axioms ← checkProof (← mkFreshUserName `_searchReduction.baselineConversion)
        levels conversionType conversion
      verified.set ((← IO.getNumHeartbeats) - start)
      evidence.set (some {source := name, conversionType, conversion, proof, axioms})
      goal.assign proof
      return true
    return false
  let total := (← IO.getNumHeartbeats) - started
  return (row, ← evidence.get, ← converted.get, max (← verified.get) (total - (← converted.get)))

/-- Single-source certification. Syntax normalization and the directional
query precede all Meta operations on candidate statements. No whnf is run for
an unmatched source. Every failure remains incomplete unless a proof is found. -/
def baselinePresentation (env : Environment) (levels : List Name) (target : Expr)
    (index? : Option FactIndex) :
    IO (Run × Option PresentationEvidence × String) := do
  let some index := index?
    | return (.incomplete .execution, none, "search.presentation_index_unavailable")
  let start ← IO.getNumHeartbeats
  let mut entries := []
  for (name, info) in index.matcherConstants do
    if info.isUnsafe || (name.isInternalDetail && !isPrivateName name) then continue
    if !proofCandidate env info.type || !rigidlyCompatible env target info.type then continue
    match normalizedAtoms env info.type with
    | .error err => return (.incomplete .execution, none, s!"{err}: {name}")
    | .ok atoms => entries := (name, atoms) :: entries
    if (← IO.getNumHeartbeats) - start > budget * 1000 then
      return (.incomplete .heartbeat, none, "search.presentation_index_budget")
  let built ← IO.getNumHeartbeats
  let .ok _atoms := normalizedAtoms env target
    | return (.incomplete .execution, none, "search.presentation_target_normalization")
  let .ok matches := normalizedLookup env target entries.reverse
    | return (.incomplete .execution, none, "search.presentation_query_normalization")
  let hits := matches
  let queried ← IO.getNumHeartbeats
  let mut checked := 0
  let mut conversionCost := 0
  let mut verificationCost := 0
  let mut failure := none
  let detail := fun checked conversionCost verificationCost =>
    s!"indexed_sources={entries.length}, candidates={hits.length}, checked_presentations={checked}, " ++
    s!"index_heartbeats={built-start}, query_heartbeats={queried-built}, " ++
    s!"conversion_heartbeats={conversionCost}, verification_heartbeats={verificationCost}"
  for (name, _) in hits do
    let (row, evidence, converted, verified) ← baselineSource env levels target name
    checked := checked + 1
    conversionCost := conversionCost + converted
    verificationCost := verificationCost + verified
    if let some evidence := evidence then
      return (.found, some evidence, detail checked conversionCost verificationCost)
    if let .incomplete reason := row.outcome then failure := some (reason, row.detail)
  match failure with
  | some (reason, text) => return (.incomplete reason, none,
      detail checked conversionCost verificationCost ++ s!", {text}")
  | none => return (.exhausted, none, detail checked conversionCost verificationCost)

end LeanInformationAudit.SearchReduction
