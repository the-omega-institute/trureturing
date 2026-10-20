import LeanInformationAuditRegAnalysis.SearchReduction.PresentationSyntax

/-! Bounded presentation certificates. No candidate proof, simp extension,
induction, unbounded theorem search or submitted equivalence certificate is consulted. -/
namespace LeanInformationAudit.SearchReduction
open Lean Meta Elab Tactic
open LeanInformationAudit.Tests.SearchReduction (Run Failure)

/-- Logical introduction/projection and the pinned `omega` procedure are the
finite presentation rules. Opaque arithmetic subterms remain atoms. -/
private partial def closePresentation (index : FactIndex)
    (goal : MVarId) : MetaM Bool := goal.withContext do
  let saved ← saveState
  let mut facts := #[]
  for decl in ← getLCtx do
    unless decl.isImplementationDetail do
      if ← isProp decl.type then facts := facts ++ (← components decl.toExpr)
  let type ← withTransparency .reducible <| whnf (← goal.getType)
  if type.isForall then
    let (_, next) ← goal.intro1
    if ← closePresentation index next then return true
  else if type.isAppOfArity ``And 2 || type.isAppOfArity ``Iff 2 then
    let ctor := if type.isAppOfArity ``And 2 then ``And.intro else ``Iff.intro
    let goals ← goal.apply (← mkConstWithFreshMVarLevels ctor)
    if ← goals.allM (closePresentation index) then return true
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
private partial def equivalent (index : FactIndex)
    (left right : Expr) (xs : Array Expr := #[]) : MetaM (Option Expr) := do
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
    -- Delta-reduce explicit subterms as well as the proposition's head.
    -- This uses definitional equality without any simp extension or theorem.
    let left ← withReducible <| reduce left (skipTypes := false)
    let right ← withReducible <| reduce right (skipTypes := false)
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
    : MetaM (Option Expr) := do
  unless ← compatibleBinders target source do return none
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

/-- The wide structure exclusion retains the legacy conversion relation. -/
def certifiedRestatement (target source : Expr) (index : FactIndex := {}) : MetaM Bool := do
  return (← restatementConversion target source index).isSome

private def rawBinderCount : Expr → Nat
  | .forallE _ _ body _ => 1 + rawBinderCount body
  | .mdata _ body => rawBinderCount body
  | _ => 0

/-- Neutral goals need no source-body normalization. Try the raw common
telescope first without deleting or changing any directional-query member. -/
def neutralFirst (target : Expr) (entries : Array (Name × Expr × RawOriginBound)) :=
  let matching := entries.filter (fun entry => rawBinderCount entry.2.1 == rawBinderCount target)
  let remaining := entries.filter (fun entry => rawBinderCount entry.2.1 != rawBinderCount target)
  matching ++ remaining

theorem neutralFirst_complete (target : Expr) (entries : Array (Name × Expr × RawOriginBound))
    (entry : Name × Expr × RawOriginBound) :
    entry ∈ neutralFirst target entries ↔ entry ∈ entries := by
  by_cases h : rawBinderCount entry.2.1 = rawBinderCount target <;>
    simp [neutralFirst, h]

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
  profilePhase "presentation/start"
  let some index := index?
    | return (.incomplete .execution, none, "search.presentation_index_unavailable")
  let start ← IO.getNumHeartbeats
  let unitLimit := budget * 1000
  let priorBound := (4 + 5 * index.enumerationSize) * unitLimit
  IO.eprintln s!"presentation budget: independent_units, enumeration={index.enumerationSize}, unit_limit={unitLimit}, prior_heartbeats_bound={priorBound}"
  let targetAtoms ← match normalizedAtoms env target with
    | .ok atoms => pure atoms
    | .error err => return (.incomplete .execution, none,
        s!"search.presentation_target_normalization: {err}")
  let targetNormalized ← IO.getNumHeartbeats
  if targetNormalized - start > unitLimit then
    return (.incomplete .heartbeat, none, "search.presentation_target_normalization_budget")
  let needsOrigins := targetAtoms.any (fun key =>
    !key.scope.isEmpty || key.constants.any (originAnchor env))
  let mut eligible := #[]
  let mut enumerated := 0
  let domainStart ← IO.getNumHeartbeats
  let domainSize := env.constants.fold (fun n name info =>
    if productionAllowed name info then n + 1 else n) 0
  if (← IO.getNumHeartbeats) - domainStart > unitLimit then
    return (.incomplete .heartbeat, none, "search.presentation_domain_budget")
  let rawStart ← IO.getNumHeartbeats
  for (name, info) in env.constants do
    unless productionAllowed name info do continue
    let scopeStart ← IO.getNumHeartbeats
    let scopeMatches := sourceScopeNecessary env info.type targetAtoms
    if (← IO.getNumHeartbeats) - scopeStart > unitLimit then
      return (.incomplete .heartbeat, none, s!"search.presentation_scope_budget: {name}")
    unless scopeMatches do continue
    enumerated := enumerated + 1
    let unitStart ← IO.getNumHeartbeats
    let bound := if needsOrigins then (rawOrigins env info.type).run' {}
      else {unknown := true}
    if rawNecessary env targetAtoms bound then
      eligible := eligible.push (name, info.type, bound)
    if (← IO.getNumHeartbeats) - unitStart > unitLimit then
      return (.incomplete .heartbeat, none,
        s!"search.presentation_raw_index_budget: raw_sources={enumerated}, " ++
          s!"necessary_hits={eligible.size}, " ++
          s!"raw_index_heartbeats={(← IO.getNumHeartbeats)-start}")
  if (← IO.getNumHeartbeats) - rawStart > (1 + 2 * domainSize) * unitLimit then
    return (.incomplete .heartbeat, none, "search.presentation_enumeration_budget")
  profilePhase "presentation/filtered"
  let rawBuilt ← IO.getNumHeartbeats
  let orderingStart ← IO.getNumHeartbeats
  eligible := eligible.qsort (fun a b => Name.quickLt a.1 b.1)
  if targetAtoms.all (·.isScope) then eligible := neutralFirst target eligible
  if (← IO.getNumHeartbeats) - orderingStart > unitLimit then
    return (.incomplete .heartbeat, none, "search.presentation_ordering_budget")
  let built ← IO.getNumHeartbeats
  let certificateKind := if targetAtoms.all (·.isScope) then "neutral" else "single-source"
  let mut normalized := 0
  let mut hits := 0
  let mut checked := 0
  let mut normalizationCost := 0
  let mut queryCost := 0
  let mut conversionCost := 0
  let mut verificationCost := 0
  let mut failure := none
  let detail := fun normalized hits checked normalizationCost queryCost
      conversionCost verificationCost =>
    s!"heartbeat_unit=internal, certificate_kind={certificateKind}, budget_semantics=independent_units, enumeration_sources={index.enumerationSize}, domain_sources={domainSize}, " ++
    s!"unit_limit={unitLimit}, prior_heartbeats_bound={priorBound}, raw_sources={enumerated}, necessary_hits={eligible.size}, " ++
    s!"normalized_sources={normalized}, " ++
    s!"candidates={hits}, checked_presentations={checked}, " ++
    s!"target_normalization_heartbeats={targetNormalized-start}, " ++
    s!"domain_heartbeats={rawStart-domainStart}, raw_index_heartbeats={rawBuilt-rawStart}, " ++
    s!"ordering_heartbeats={built-orderingStart}, " ++
    s!"normalization_heartbeats={normalizationCost}, query_heartbeats={queryCost}, " ++
    s!"conversion_heartbeats={conversionCost}, verification_heartbeats={verificationCost}"
  for (name, source, bound) in eligible do
    let before ← IO.getNumHeartbeats
    let sourceAtoms := normalizedAtomsWithOrigins env source bound
    normalized := normalized + 1
    normalizationCost := normalizationCost + ((← IO.getNumHeartbeats) - before)
    if (← IO.getNumHeartbeats) - before > unitLimit then
      failure := some (.heartbeat, s!"search.presentation_normalization_budget: {name}")
      continue
    match sourceAtoms with
    | .error err =>
      failure := some (.execution, s!"{err}: {name}")
      continue
    | .ok atoms =>
      let before ← IO.getNumHeartbeats
      let matched := supportIncluded targetAtoms atoms
      let queryUsed := (← IO.getNumHeartbeats) - before
      queryCost := queryCost + queryUsed
      if queryUsed > unitLimit then
        failure := some (.heartbeat, s!"search.presentation_query_budget: {name}")
        continue
      unless matched do continue
    hits := hits + 1
    let (row, evidence, converted, verified) ← baselineSource env levels target name
    checked := checked + 1
    conversionCost := conversionCost + converted
    verificationCost := verificationCost + verified
    if let some evidence := evidence then
      return (.found, some evidence,
        detail normalized hits checked normalizationCost queryCost conversionCost verificationCost)
    if let .incomplete reason := row.outcome then failure := some (reason, row.detail)
  match failure with
  | some (reason, text) => return (.incomplete reason, none,
      detail normalized hits checked normalizationCost queryCost conversionCost verificationCost ++
        s!", {text}")
  | none => return (.exhausted, none,
      detail normalized hits checked normalizationCost queryCost conversionCost verificationCost)

end LeanInformationAudit.SearchReduction
