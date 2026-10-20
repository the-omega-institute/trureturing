import LeanInformationAuditRegAnalysis.SearchReduction.Graph
import LeanInformationAudit.CompiledAxioms
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-! Declaration dependency extraction and statement-only local reconstruction. -/
namespace LeanInformationAudit.SearchReduction
open Lean Meta Elab Tactic

abbrev localBudget : Nat := 200000
abbrev localConfiguration : String := "R_loc-decl/analytic-cut-k2/200000"

private def standardClosure (xs : Array Name) : Bool :=
  xs.all (#[`propext, `Classical.choice, `Quot.sound].contains ·)

def checkLocalProof (type proof : Expr) : MetaM Unit := do
  let type ← instantiateMVars type
  let proof ← instantiateMVars proof
  unless !type.hasMVar && !type.hasFVar && !proof.hasMVar && !proof.hasFVar && !proof.hasSorry do
    throwError "graph.unclosed_local_certificate"
  let name ← mkFreshUserName `_declLocal
  let levels := (collectLevelParams {} type).params.toList
  let before ← getEnv
  if ← isProp type then
    addDecl (.thmDecl {name, levelParams := levels, type, value := proof})
  else
    addDecl (.defnDecl {
      name, levelParams := levels, type, value := proof,
      hints := .abbrev, safety := .safe})
  let axioms ← collectAxioms name
  setEnv before
  unless standardClosure axioms do throwError "graph.nonstandard_axioms: {axioms}"

/-- Administrative reduction removes dead lets, beta redexes and discarded
constructor fields. Named author declarations remain opaque dependency nodes. -/
def liveValue (value : Expr) : MetaM Expr := do
  let value ← zetaReduce value
  Meta.transform value (post := fun e => do
    let head := e.getAppFn
    let env ← getEnv
    let reduce := e.isProj || head.isLambda ||
      head.constName?.any (fun n => (env.getProjectionFnInfo? n).isSome)
    if reduce then return .done (← withReducible <| whnf e)
    if let some n := head.constName? then
      if isRecCore (← getEnv) n || isMatcherCore (← getEnv) n then
        return .done (← withReducible <| whnf e)
    return .done e)

private def generated (env : Environment) (n : Name) : Bool :=
  !allowCompletion env n || isMatcherCore env n || isAuxRecursor env n

private structure ExtractionState where
  vertices : Array GraphVertex := #[]
  edges : Array GraphEdge := #[]
  ids : NameMap Nat := {}
  visiting : NameSet := {}

private abbrev ExtractM := StateRefT ExtractionState MetaM

/-- Ownership is transitive: an equation of a matcher or a nested proof
auxiliary belongs to the same author declaration as its generated parent. -/
private partial def declarationOwner (name : Name) : MetaM Name := do
  if !(generated (← getEnv) name || (← isEqnThm name)) then return name
  let mut parent := (← isEqnThm? name).getD name.getPrefix
  while !parent.isAnonymous && !((← getEnv).contains parent) do parent := parent.getPrefix
  if parent.isAnonymous || parent == name then
    throwError "graph.generated_owner_unknown:{name}"
  declarationOwner parent

private def vocabularyKind : ConstantInfo → Bool
  | .inductInfo _ | .ctorInfo _ | .recInfo _ => true
  | _ => false

/-- Generated constants are folded into their nearest existing owner. The
compiler predicates identify auxiliaries; an unowned auxiliary fails closed. -/
private partial def dependencyNames (base : Environment) (owner : Name)
    (info : ConstantInfo) (cache : IO.Ref (NameMap (Array Name)))
    (seen : NameSet := {}) : MetaM (Array Name) := do
  if let some found := (← cache.get).find? info.name then return found
  let (types, _) := CompiledAxioms.declarationDependencyParts info
  let values ← match info.value? (allowOpaque := true) with
    | some value => pure (← liveValue value).getUsedConstants
    | none => pure #[]
  let mut result := #[]
  for dep in types ++ values do
    if dep == owner || seen.contains dep then continue
    let depInfo := ((← getEnv).setExporting false).find? dep
    if !base.contains dep && depInfo.any vocabularyKind then
      result := result ++ (← dependencyNames base owner depInfo.get! cache (seen.insert dep))
    else if !base.contains dep && (generated (← getEnv) dep || (← isEqnThm dep)) then
      let some aux := ((← getEnv).setExporting false).find? dep
        | throwError "graph.generated_missing:{dep}"
      let parent ← declarationOwner dep
      let parentInfo := ((← getEnv).setExporting false).find? parent
      if parentInfo.any vocabularyKind then
        result := result ++ (← dependencyNames base owner parentInfo.get! cache
          (seen.insert dep |>.insert parent))
      else if parent != owner then result := result.push parent
      else result := result ++ (← dependencyNames base owner aux cache (seen.insert dep))
    else if !result.contains dep then result := result.push dep
  cache.modify (·.insert info.name result)
  return result

private partial def extractDeclaration (base : Environment) (additions : Array Name)
    (cache : IO.Ref (NameMap (Array Name))) (name : Name) : ExtractM Nat := do
  if (← get).visiting.contains name then throwError "graph.declaration_cycle:{name}"
  if let some id := (← get).ids.find? name then return id
  let info ← getConstInfo name
  let id := (← get).vertices.size
  let seed := base.contains name
  let origin := mkConst name (info.levelParams.map Level.param)
  modify fun s => {s with
    ids := s.ids.insert name id
    visiting := s.visiting.insert name,
    vertices := s.vertices.push {
      id, type := info.type, origin, seed,
      opaqueDecl := !seed, structureSeed := additions.contains name,
      structureProof? := if additions.contains name then some origin else none}}
  unless seed do
    unless (info.value? (allowOpaque := true)).isSome do
      throwError "graph.missing_declaration_body:{name}"
    let deps ← dependencyNames base name info cache
    let mut premises := []
    for dep in deps do premises := premises ++ [← extractDeclaration base additions cache dep]
    modify fun s => {s with edges := s.edges.push {
      conclusion := id, premises := premises.eraseDups, source := some name}}
  modify fun s => {s with visiting := s.visiting.erase name}
  return id

/-- Extraction is one traversal of each live declaration value. No author body
is retained in the graph or supplied to the local reconstructor. -/
def extractGraph (base : Environment) (target : Name)
    (additions : Array Name := #[]) : MetaM ProofGraph := do
  try
    let cache ← IO.mkRef ({} : NameMap (Array Name))
    let (root, state) ← (extractDeclaration base additions cache target).run {}
    return {root, vertices := state.vertices.toList, edges := state.edges.toList}
  catch ex =>
    return {complete := false, issues := [s!"graph.extraction:{← ex.toMessageData.toString}"]}

private partial def injectiveVariables (args telescope : Array Expr) (position : Nat := 0)
    (used : Array Expr := #[]) : MetaM Bool := do
  if position >= args.size then return true
  let value ← instantiateMVars args[position]!
  if value.isMVar then
    for x in telescope do
      if used.contains x then continue
      let saved ← saveState
      if ← withReducible <| isDefEq (← inferType value) (← inferType x) then
        value.mvarId!.assign x
        if ← injectiveVariables args telescope (position + 1) (used.push x) then return true
      saved.restore
    return false
  if value.isFVar && telescope.contains value && !used.contains value then
    return ← injectiveVariables args telescope (position + 1) (used.push value)
  return false

/-- Complete bounded injection matching of statement telescopes. A term or a
repeated variable never qualifies as a binder renaming. -/
def analyticPremise (premise consumer : Expr) : MetaM Bool := do
  let saved ← saveState
  let started ← IO.getNumHeartbeats
  try
    let answer ← withTheReader Core.Context (fun ctx =>
        {ctx with initHeartbeats := started, maxHeartbeats := localBudget * 1000}) do
      let levels := (collectLevelParams {} premise).params.toList
      let premise := premise.instantiateLevelParams levels (← levels.mapM fun _ => mkFreshLevelMVar)
      forallTelescopeReducing consumer fun xs body => do
        let found ← IO.mkRef false
        let mut parts := #[body]
        for x in xs do parts := parts.push (← inferType x)
        for input in parts do
          discard <| Meta.transform input (pre := fun part => do
            if ← found.get then return .done part
            if !(← isProp part) then return .continue
            let before ← saveState
            let (args, _, candidate) ← forallMetaTelescopeReducing premise
            if ← withReducible <| isDefEq candidate part then
              if ← injectiveVariables args xs then found.set true
            before.restore
            return .continue)
        return ← found.get
    saved.restore
    return answer
  catch ex =>
    saved.restore
    throw ex

private def exactLocal (goal : MVarId) (facts : Array Expr) : MetaM Bool := goal.withContext do
  for fact in facts do
    let saved ← saveState
    if ← withReducible <| isDefEq (← inferType fact) (← goal.getType) then
      goal.assign fact
      return true
    saved.restore
  return false

private def tryAssumptions (goal : MVarId) (facts : Array Expr) : MetaM Bool := do
  for fact in facts do
    let saved ← saveState
    try
      let goals ← withReducible <| goal.apply fact {approx := false}
      if ← goals.allM (fun g => exactLocal g facts) then return true
    catch ex =>
      if ex.isMaxHeartbeat || ex.isInterrupt || ex.isRuntime then throw ex
    saved.restore
  return false

private def eliminateLocal (facts : Array Expr) : MetaM (Array Expr) := do
  let mut result := facts
  for fact in facts do
    let type ← withReducible <| whnf (← inferType fact)
    if type.isAppOfArity ``And 2 then
      for n in #[``And.left, ``And.right] do result := result.push (← mkAppM n #[fact])
    else if type.isAppOfArity ``Iff 2 then
      for n in #[``Iff.mp, ``Iff.mpr] do result := result.push (← mkAppM n #[fact])
    else if type.isAppOfArity ``Subtype 2 then
      result := result.push (← mkAppM ``Subtype.property #[fact])
  return result

private partial def structuralLocal (goal : MVarId) (facts : Array Expr)
    (fuel : Nat := 32) : MetaM Bool := goal.withContext do
  if fuel == 0 then return false
  let type ← withReducible <| whnf (← goal.getType)
  if type.isForall then
    let (fvar, next) ← goal.intro1
    return ← structuralLocal next (facts.push (mkFVar fvar)) (fuel - 1)
  if ← exactLocal goal facts then return true
  let saved ← saveState
  try goal.refl; return true
  catch ex => if ex.isMaxHeartbeat || ex.isInterrupt || ex.isRuntime then throw ex
  saved.restore
  let facts ← eliminateLocal facts
  if ← exactLocal goal facts then return true
  for fact in facts do
    let factType ← withReducible <| whnf (← inferType fact)
    if factType.isAppOfArity ``Exists 2 then
      let before ← saveState
      try
        let (major, next) ← (← goal.assert `_exists factType fact).intro1
        let branches ← next.cases major
        if h : branches.size = 1 then
          let branch := branches[0]'(by omega)
          let available := (facts.filter (· != fact)).map branch.subst.apply
          if ← structuralLocal branch.mvarId (available ++ branch.fields) (fuel - 1) then return true
      catch ex => if ex.isMaxHeartbeat || ex.isInterrupt || ex.isRuntime then throw ex
      before.restore
  let ctor? := if type.isAppOfArity ``And 2 then some ``And.intro
    else if type.isAppOfArity ``Iff 2 then some ``Iff.intro
    else if type.isAppOfArity ``Exists 2 then some ``Exists.intro
    else if type.isAppOfArity ``Subtype 2 then some ``Subtype.mk else none
  if let some ctor := ctor? then
    try
      let goals ← goal.apply (← mkConstWithFreshMVarLevels ctor)
      let obligations ← goals.filterM fun g => g.withContext do isProp (← g.getType)
      if ← obligations.allM (fun g => structuralLocal g facts (fuel - 1)) then
        let proof ← instantiateMVars (mkMVar goal)
        unless proof.hasMVar do return true
    catch ex => if ex.isMaxHeartbeat || ex.isInterrupt || ex.isRuntime then throw ex
    saved.restore
  return ← tryAssumptions goal facts

/-- Fixed procedure order is part of the R identity, independent of calibration. -/
private def solveLocalGoal (goal : MVarId) (facts : Array Expr) : MetaM Bool := do
  for procedure in [:9] do
    let saved ← saveState
    let ok ← try
      if procedure == 0 then structuralLocal goal facts
      else if procedure == 1 then goal.withContext do
        let mut theorems : SimpTheoremsArray := #[]
        for fact in facts do
          let type ← whnf (← inferType fact)
          if type.isAppOfArity ``Eq 3 || type.isAppOfArity ``Iff 2 then
            theorems ← theorems.addTheorem (.fvar fact.fvarId!) fact
        let context ← Simp.mkContext {failIfUnchanged := false} theorems {}
        let (remaining, _) ← simpGoal goal context (simprocs := #[])
        return remaining.isNone
      else goal.withContext do
        let target ← instantiateMVars (← goal.getType)
        if target.hasMVar then return false
        let tac ← match procedure with
          | 2 => `(tactic| omega)
          | 3 => `(tactic| ring)
          | 4 => `(tactic| ring_nf)
          | 5 => do
            let mut names := #[]
            for fact in facts do
              let type ← inferType fact
              if ← isProp type then
                names := names.push (mkIdent (← getFVarLocalDecl fact).userName)
            `(tactic| linarith only [$[$names:term],*])
          | 6 => `(tactic| positivity)
          | 7 => `(tactic| norm_num1)
          | _ =>
            let quantified ← IO.mkRef false
            discard <| Meta.transform target (pre := fun e => do
              if e.isForall || e.isAppOf ``Exists then quantified.set true
              return .continue)
            if ← quantified.get then return false
            `(tactic| decide)
        let goals ← (Term.withoutErrToSorry <| Tactic.run goal (evalTactic tac)).run'
        return goals.isEmpty
    catch ex =>
      if ex.isMaxHeartbeat || ex.isInterrupt || ex.isRuntime then throw ex
      pure false
    if ok then return true
    saved.restore
  return false

structure LocalResult where
  cost : EdgeCost := .unknown
  proof? : Option Expr := none
  detail : String := ""
  used : List Nat := []
  sharedData? : Option Bool := none

private def withFacts {α : Type} (types : List Expr)
    (action : Array Expr → MetaM α) : MetaM α := do
  let rec go (remaining : List Expr) (facts : Array Expr) : MetaM α := do
    match remaining with
    | [] => action facts
    | type :: rest => withLocalDeclD (Name.num `_premise facts.size) type (fun fact => go rest (facts.push fact))
  go types #[]

/-- Only statement types enter R. The successful lambda retains precisely its
used premise binders, so zero edges carry their actual premises. -/
def localRebuild (target : Expr) (types : List Expr := []) : MetaM LocalResult := do
  let original ← saveState
  let started ← IO.getNumHeartbeats
  try
    let result : LocalResult ← withTheReader Core.Context (fun ctx =>
        {ctx with initHeartbeats := started, maxHeartbeats := localBudget * 1000}) do
      withFacts types fun facts => do
        let root ← mkFreshExprMVar target
        let mut goal := root.mvarId!
        let mut available := facts
        while (← goal.withContext <| withReducible <| whnf (← goal.getType)).isForall do
          let (fvar, next) ← goal.intro1
          available := available.push (mkFVar fvar)
          goal := next
        unless ← goal.withContext (solveLocalGoal goal available) do
          return {cost := .one, detail := "normal-exhaustion"}
        let proof ← instantiateMVars root
        unless !proof.hasMVar do return {cost := .unknown, detail := "unclosed-reconstruction"}
        let used := facts.toList.zipIdx.filterMap fun (fact, i) =>
          if proof.containsFVar fact.fvarId! then some i else none
        let selected := used.toArray.map (facts[·]!)
        let certificate ← mkLambdaFVars selected proof
        let certificateType ← mkForallFVars selected target
        checkLocalProof certificateType certificate
        return {cost := .zero, proof? := some certificate, used, detail := "kernel-checked-statement"}
    original.restore
    return result
  catch ex =>
    original.restore
    let detail ← ex.toMessageData.toString
    return {cost := .unknown, detail := if ex.isMaxHeartbeat then "heartbeat"
      else if ex.isInterrupt then "cancelled" else s!"execution:{detail}"}

private def vertex (graph : ProofGraph) (id : Nat) : GraphVertex :=
  (graph.vertices.find? (·.id == id)).getD default

/-- Type classification is shared by both arms and the given-premise ablation. -/
private def annotateGraph (graph : ProofGraph) : MetaM ProofGraph := do
  let mut edges := []
  let mut graph := graph
  for edge in graph.edges do
    let started ← IO.getNumHeartbeats
    let mut edge := edge
    try
      let analytic ← withTheReader Core.Context (fun ctx =>
          {ctx with initHeartbeats := started, maxHeartbeats := localBudget * 1000}) do
        edge.premises.filterM fun p =>
          analyticPremise (vertex graph p).type (vertex graph edge.conclusion).type
      edge := {edge with analytic}
    catch ex =>
      graph := {graph with
        complete := false,
        issues := s!"graph.analytic:{edge.source}:{← ex.toMessageData.toString}" :: graph.issues}
    edges := edges ++ [edge]
  return {graph with edges}

/-- Same price function in each arm; only the seed flag changes. -/
def priceGraph (graph : ProofGraph) (paired := false) (allGiven := false) : MetaM ProofGraph := do
  let mut edges := []
  let seeds := (graph.vertices.filter (fun v =>
    v.seed || (paired && v.structureSeed && !v.targetPart))).map (·.id)
  for edge in graph.edges do
    let available := if allGiven then edge.premises else statementPremises edge seeds
    let analytic := edge.analytic
    let result ← localRebuild (vertex graph edge.conclusion).type (available.map (vertex graph · |>.type))
    let used := result.used.map (available[·]!)
    let edge := if allGiven then
        if paired then {edge with pairedVisibleCost := result.cost, pairedGivenUsedPremises := used}
        else {edge with visibleCost := result.cost, givenUsedPremises := used}
      else if paired then {edge with pairedCost := result.cost, pairedZeroProof := result.proof?, pairedUsedPremises := used}
      else {edge with
        cost := result.cost, zeroProof := result.proof?, usedPremises := used,
        analytic, detail := result.detail}
    edges := edges ++ [edge]
  return {graph with edges}

private def armSeeds (graph : ProofGraph) (paired : Bool) : List Nat :=
  (graph.vertices.filter (fun v => v.seed || (paired && v.structureSeed && !v.targetPart))).map (·.id)

private def armGraph (graph : ProofGraph) (paired allGiven : Bool) : ProofGraph :=
  {graph with edges := graph.edges.map fun edge =>
    let cost := if allGiven then (if paired then edge.pairedVisibleCost else edge.visibleCost)
      else if paired then edge.pairedCost else edge.cost
    {edge with cost, premises := if cost == .zero then
      (if allGiven then
        (if paired then edge.pairedGivenUsedPremises else edge.givenUsedPremises)
       else if paired then edge.pairedUsedPremises else edge.usedPremises) else edge.premises}}

def rootProbe (graph : ProofGraph) (paired := false) : MetaM ProbeResult := do
  let seeds := armSeeds graph paired
  let result ← localRebuild (vertex graph graph.root).type (seeds.map (vertex graph · |>.type))
  let outcome := match result.cost with
    | .zero => Run.found | .one => .exhausted | .unknown => .incomplete .undecided
  return {
    outcome, checked := result.proof?.isSome, premises := result.used.map (seeds[·]!),
    proof? := result.proof?, detail := result.detail}

/-- Only zero certificates and seed constants are assembled, never author
nonseed values. The backpointers come from the same table as the reported DP. -/
def assembleZero (graph : ProofGraph) (paired := false) : MetaM (Option Expr) := do
  let arm := armGraph graph paired false
  let seeds := armSeeds graph paired
  let table := dpTable arm costUpper seeds
  let rec go (fuel id : Nat) : MetaM (Option Expr) := do
    if h : fuel = 0 then return none
    let v := vertex graph id
    if v.seed then return some v.origin
    if paired && v.structureSeed && !v.targetPart then return v.structureProof?
    let some index := (table[id]?.getD {}).edge? | return none
    let some edge := arm.edges[index]? | return none
    let some schema := if paired then edge.pairedZeroProof else edge.zeroProof | return none
    let mut arguments := #[]
    for p in edge.premises do
      let some proof ← go (fuel - 1) p | return none
      arguments := arguments.push proof
    return some (mkAppN schema arguments)
  termination_by fuel
  decreasing_by omega
  try
    let some proof ← go (graph.vertices.length + 1) graph.root | return none
    checkLocalProof (vertex graph graph.root).type proof
    return some proof
  catch _ => return none

/-- Two root probes, target-part reverse probes and declaration-level k=2.
The d_given ablation supplies all premise types; it does not affect verdicts. -/
def evaluateGraph (raw : ProofGraph) : MetaM GraphReading := do
  if raw.vertices.isEmpty then return {graph := raw}
  let mut raw := raw
  let mut targetPartComplete := true
  let rootType := (vertex raw raw.root).type
  let baseIds := armSeeds raw false
  let baseTypes := baseIds.map (vertex raw · |>.type)
  let mut vertices := []
  for v in raw.vertices do
    let mut v := v
    if v.structureSeed then
      let reverse ← localRebuild v.type (rootType :: baseTypes)
      let independent ← localRebuild v.type baseTypes
      if reverse.cost == .unknown || independent.cost == .unknown then targetPartComplete := false
      let part ← analyticPremise v.type rootType
      let inverse ← analyticPremise rootType v.type
      v := {v with targetPart := part || inverse ||
        (reverse.cost == .zero && independent.cost == .one)}
    vertices := vertices ++ [v]
  raw := {raw with vertices}
  let graph ← annotateGraph {raw with edges := raw.edges ++ k2Frontier raw}
  let graph ← priceGraph graph
  let graph ← priceGraph graph true
  let graph ← priceGraph graph false true
  let graph ← priceGraph graph true true
  let baseProbe ← rootProbe graph
  let pairedProbe ← rootProbe graph true
  let mut graph := graph
  for paired in [false, true] do
    let probe := if paired then pairedProbe else baseProbe
    if probe.checked && (!paired || !baseProbe.checked) then
      let actual := probe.premises
      graph := {graph with edges := graph.edges ++ [{
        conclusion := graph.root, premises := actual, window := 0,
        cost := if paired then (if baseProbe.outcome == .exhausted then .one else .unknown) else .zero, pairedCost := .zero,
        visibleCost := .zero, pairedVisibleCost := .zero,
        usedPremises := if paired then [] else actual, pairedUsedPremises := actual,
        givenUsedPremises := if paired then [] else actual, pairedGivenUsedPremises := actual,
        zeroProof := if paired then none else probe.proof?, pairedZeroProof := probe.proof?,
        detail := if paired then "paired-root-probe" else "baseline-root-probe"}]}
  let baselineGraph := armGraph graph false false
  let pairedGraph := armGraph graph true false
  let baseSeeds := armSeeds graph false
  let pairSeeds := armSeeds graph true
  let k1 := {graph with edges := graph.edges.filter (·.window != 2)}
  let selectedSeeds := optimalSeeds pairedGraph costUpper pairSeeds
  let witnessEdges := graph.edges.zipIdx.filterMap fun (edge, i) =>
    if isWitnessEdge graph selectedSeeds edge then some i else none
  return {
    graph, baseline := graphInterval baselineGraph baseSeeds,
    paired := graphInterval pairedGraph pairSeeds,
    baselineK1 := graphInterval (armGraph k1 false false) baseSeeds,
    pairedK1 := graphInterval (armGraph k1 true false) pairSeeds,
    baselineVisible := graphInterval (armGraph graph false true) baseSeeds,
    pairedVisible := graphInterval (armGraph graph true true) pairSeeds,
    baselineProbe := baseProbe, pairedProbe, selectedSeeds, witnessEdges, targetPartComplete,
    noAuxiliary := !(raw.vertices.any (·.structureSeed)),
    pairedUsesSeed := selectedSeeds.any (fun id =>
      let v := vertex graph id
      v.structureSeed && !v.seed && !v.targetPart)}

end LeanInformationAudit.SearchReduction
