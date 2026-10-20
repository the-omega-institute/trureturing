import LeanInformationAuditRegAnalysis.SearchReduction.Graph

/-! Scoped proof extraction and the frozen local reconstructor. Author data is
available only to the explicitly labelled visible-data ablation. -/
namespace LeanInformationAudit.SearchReduction
open Lean Meta Elab Tactic

abbrev localBudget : Nat := 200000
abbrev graphCapacity : Nat := 262144

private def standardClosure (xs : Array Name) : Bool :=
  xs.all (#[`propext, `Classical.choice, `Quot.sound].contains ·)

/-- Kernel checking is performed on the closed sequent, including its scope. -/
def checkLocalProof (type proof : Expr) : MetaM Unit := do
  let type ← instantiateMVars type
  let proof ← instantiateMVars proof
  unless !type.hasMVar && !type.hasFVar && !proof.hasMVar && !proof.hasFVar && !proof.hasSorry do
    throwError "graph.unclosed_local_certificate"
  let name ← mkFreshUserName `_graphLocal
  let levels := (collectLevelParams {} type).params.toList
  let before ← getEnv
  addDecl (.thmDecl {name, levelParams := levels, type, value := proof})
  let axioms ← collectAxioms name
  unless standardClosure axioms do throwError "graph.nonstandard_axioms: {axioms}"
  setEnv before

structure ExtractionState where
  graph : ProofGraph := {}
  vertices : Array GraphVertex := #[]
  edges : Array GraphEdge := #[]
  shared : Std.HashMap (Expr × List FVarId) Nat := {}

abbrev ExtractM := StateRefT ExtractionState MetaM

private def incomplete (reason : String) : ExtractM Unit :=
  modify fun s => {s with graph := {s.graph with
    complete := false
    issues := reason :: s.graph.issues}}

private def scopeVariables : MetaM (Array Expr) := do
  let mut xs := #[]
  for decl in ← getLCtx do xs := xs.push decl.toExpr
  return xs

/-- Occurrences are shared only by expression identity in the same fvar scope;
proposition equality is never a graph-node key. -/
private partial def visit (base : Environment) (additions : Array (Expr × Expr))
    (proof : Expr) (position : List Nat) (unfolding : NameSet := {}) : ExtractM Nat := do
  let proof := proof.consumeMData
  let scope ← scopeVariables
  let key := (proof, scope.toList.map Expr.fvarId!)
  if let some id := (← get).shared[key]? then return id
  if (← get).vertices.size ≥ graphCapacity then
    if !(← get).graph.issues.any (·.startsWith "graph.capacity:") then
      incomplete s!"graph.capacity:limit={graphCapacity},position={position}"
    return 0
  let type ← inferType proof
  let closed ← mkForallFVars scope type
  let mut structureSeed := false
  let mut structureProof? := none
  for added in additions do
    let saved ← (saveState : MetaM Meta.SavedState)
    let equal ← withReducible <| isDefEq closed added.1
    (saved.restore : MetaM Unit)
    if equal then
      structureSeed := true
      structureProof? := some added.2
  let id := (← get).vertices.size
  let vertex : GraphVertex := {
    id, type := closed, origin := proof, scope, lctx := ← getLCtx,
    instances := ← getLocalInstances, position, structureSeed, structureProof?}
  modify fun s => {s with
    shared := s.shared.insert key id
    vertices := s.vertices.push vertex}
  let addEdge (premises : List Nat) (head : Option Expr := none)
      (authorData : Array (Option Expr) := #[]) : ExtractM Unit := do
    let source := head.bind Expr.constName?
    let head ← head.mapM (mkLambdaFVars scope ·)
    modify fun s => {s with edges := s.edges.push {conclusion := id, premises, head, source, authorData}}
  match proof with
  | .fvar _ =>
    modify fun s => {s with vertices := s.vertices.modify id (fun v => {v with seed := true})}
  | .lam name domain body info =>
    let child ← withLocalDecl name info domain fun x =>
      visit base additions (body.instantiate1 x) (position ++ [0]) unfolding
    addEdge [child]
  | .letE _ _ value body _ =>
    let child ← visit base additions (body.instantiate1 value) (position ++ [0]) unfolding
    addEdge [child]
  | .app .. | .const .. =>
    let head := proof.getAppFn
    let args := proof.getAppArgs
    if let .lam .. := head then
      let child ← visit base additions proof.headBeta (position ++ [0]) unfolding
      addEdge [child]
    else if let .const name levels := head then
      let info ← getConstInfo name
      if base.contains name && info.isTheorem && args.isEmpty then
        modify fun s => {s with vertices := s.vertices.modify id (fun v => {v with seed := true})}
      else if !base.contains name && (← isProp info.type) then
        if unfolding.contains name then
          incomplete s!"graph.recursive_helper:{name}"
        else if let some value := info.value? (allowOpaque := true) then
          let value := value.instantiateLevelParams info.levelParams levels
          let child ← visit base additions (mkAppN value args).headBeta
            (position ++ [0]) (unfolding.insert name)
          addEdge [child]
        else incomplete s!"graph.missing_body:{name}"
      else
        let mut premises := []
        if base.contains name && info.isTheorem then
          premises := [← visit base additions head (position ++ [args.size]) unfolding]
        let mut data := #[]
        for h : i in [:args.size] do
          let arg := args[i]
          if ← isProp (← inferType arg) then
            let child ← visit base additions arg (position ++ [i]) unfolding
            premises := premises ++ [child]
            data := data.push none
          else
            data := data.push (some (← mkLambdaFVars scope arg))
        addEdge premises (some head) data
    else if head.isFVar then
      let mut premises := []
      let mut data := #[]
      for h : i in [:args.size] do
        let arg := args[i]
        if ← isProp (← inferType arg) then
          premises := premises ++ [← visit base additions arg (position ++ [i]) unfolding]
          data := data.push none
        else
          data := data.push (some (← mkLambdaFVars scope arg))
      addEdge premises (some head) data
    else
      incomplete s!"graph.unsupported_application_head:{head.ctorName}"
  | .mdata _ _ => incomplete "graph.unexpected_mdata"
  | .proj .. => incomplete "graph.unsupported_projection"
  | _ => incomplete s!"graph.unsupported_expr:{proof.ctorName}"
  return id

/-- Extraction reads the author environment, while the protected environment
only determines stopping leaves. Failures are explicit incompleteness. -/
def extractGraph (base : Environment) (target proof : Expr)
    (additions : Array (Expr × Expr) := #[]) : MetaM ProofGraph := do
  try
    let ((root, _), state) ← (do
      let root ← visit base additions proof []
      for (_, added) in additions do discard <| visit base additions added [graphCapacity]
      pure (root, ())).run {}
    let graph := {state.graph with vertices := state.vertices.toList, edges := state.edges.toList, root}
    unless ← isDefEq (← inferType proof) target do
      return {graph with complete := false, issues := ["graph.target_type_mismatch"]}
    return graph
  catch ex =>
    return {complete := false, issues := [s!"graph.extraction_exception:{← ex.toMessageData.toString}"]}

structure HiddenExpr where
  skeleton : Expr
  dataSlots : Array Expr := #[]
  proofSlots : Array Expr := #[]
  instances : Array Expr := #[]
  instanceAuthors : Array (Option Expr) := #[]

/-- Rebuild a maximal application spine from its head telescope. No author
argument is copied on the hidden-data path. -/
def hideData (head : Expr) (arity : Nat) (visible : Array (Option Expr) := #[])
    (author : Array (Option Expr) := #[]) :
    MetaM HiddenExpr := do
  let mut result : HiddenExpr := {skeleton := head}
  for i in [:arity] do
    let type ← whnf (← inferType result.skeleton)
    let .forallE _ domain _ kind := type
      | if type.hasMVar then throwError "graph.hidden_spine_blocked"
        else throwError "graph.spine_arity"
    let prop ← isProp domain
    let value ← if let some (some data) := visible[i]? then pure data
      else mkFreshExprMVar domain
    result := {result with skeleton := mkApp result.skeleton value}
    if !prop then result := {result with dataSlots := result.dataSlots.push value}
    else result := {result with proofSlots := result.proofSlots.push value}
    if kind.isInstImplicit then result := {result with
      instances := result.instances.push value
      instanceAuthors := result.instanceAuthors.push (author[i]?.join)}
  return result

private partial def replayPlan (plan : SpinePlan) (scope : Array Expr)
    (visible : Bool) (expected : Expr) : MetaM HiddenExpr := do
  let .app head data children := plan
  let instantiateScope (closed : Expr) : Expr := Id.run do
    let mut body := closed
    let mut count := 0
    while body.isLambda do
      count := count + 1
      body := body.bindingBody!
    return (mkAppN closed (scope.extract 0 count)).headBeta
  let head := instantiateScope head
  let authorData := data.map (·.map instantiateScope)
  let result ← hideData head data.size (if visible then authorData else #[]) authorData
  unless ← withReducible <| isDefEq (← inferType result.skeleton) expected do
    throwError "graph.replay_head_result_mismatch"
  let mut allData := result.dataSlots
  let mut allProofs := #[]
  let mut allInstances := result.instances
  let mut allInstanceAuthors := result.instanceAuthors
  for h : i in [:result.proofSlots.size] do
    let proof := result.proofSlots[i]
    if let some (some child) := children[i]? then
      let child ← replayPlan child scope visible (← inferType proof)
      unless ← isDefEq (← inferType child.skeleton) (← inferType proof) do
        throwError "graph.frontier_interface_mismatch"
      proof.mvarId!.assign child.skeleton
      allData := allData ++ child.dataSlots
      allProofs := allProofs ++ child.proofSlots
      allInstances := allInstances ++ child.instances
      allInstanceAuthors := allInstanceAuthors ++ child.instanceAuthors
    else allProofs := allProofs.push proof
  return {result with
    dataSlots := allData
    proofSlots := allProofs
    instances := allInstances
    instanceAuthors := allInstanceAuthors}

private def tryAssumptions (goal : MVarId) (facts : Array Expr) : MetaM Bool := do
  for fact in facts do
    let saved ← saveState
    try
      let goals ← withReducible <| goal.apply fact {approx := false}
      let allClosed ← goals.allM fun remaining => remaining.withContext do
        for available in facts do
          let before ← saveState
          if ← withReducible <| isDefEq (← inferType available) (← remaining.getType) then
            remaining.assign available
            return true
          before.restore
        return false
      if allClosed then
        check (← instantiateMVars (mkMVar goal))
        return true
    catch ex =>
      if ex.isMaxHeartbeat || ex.isInterrupt || ex.isRuntime then throw ex
    saved.restore
  return false

private def exactLocal (goal : MVarId) (facts : Array Expr) : MetaM Bool := goal.withContext do
  for fact in facts do
    let saved ← saveState
    if ← withReducible <| isDefEq (← inferType fact) (← goal.getType) then
      goal.assign fact
      return true
    saved.restore
  return false

private def eliminateLocal (facts : Array Expr) : MetaM (Array Expr) := do
  let mut result := facts
  for fact in facts do
    let type ← withReducible <| whnf (← inferType fact)
    if type.isAppOfArity ``And 2 then
      for name in #[``And.left, ``And.right] do result := result.push (← mkAppM name #[fact])
    else if type.isAppOfArity ``Iff 2 then
      for name in #[``Iff.mp, ``Iff.mpr] do result := result.push (← mkAppM name #[fact])
    else if type.isAppOfArity ``Subtype 2 then
      result := result.push (← mkAppM ``Subtype.property #[fact])
  return result

/-- Fixed deterministic structural introduction, with no witness enumeration. -/
private partial def structuralLocal (goal : MVarId) (facts : Array Expr)
    (fuel : Nat := 32) : MetaM Bool := goal.withContext do
  if fuel == 0 then return false
  let type ← withReducible <| whnf (← goal.getType)
  if type.isForall then
    let (fvar, next) ← goal.intro1
    return ← structuralLocal next (facts.push (mkFVar fvar)) (fuel - 1)
  if ← exactLocal goal facts then return true
  let saved ← saveState
  try
    goal.refl
    return true
  catch ex =>
    if ex.isMaxHeartbeat || ex.isInterrupt || ex.isRuntime then throw ex
  saved.restore
  let facts ← eliminateLocal facts
  if ← exactLocal goal facts then return true
  -- Exists has no data projection: eliminate it into a fresh branch scope.
  -- The witness is a local variable there, never a globally selected datum.
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
          if ← structuralLocal branch.mvarId (available ++ branch.fields) (fuel - 1) then
            return true
      catch ex =>
        if ex.isMaxHeartbeat || ex.isInterrupt || ex.isRuntime then throw ex
      before.restore
  let ctor? := if type.isAppOfArity ``And 2 then some ``And.intro
    else if type.isAppOfArity ``Iff 2 then some ``Iff.intro
    else if type.isAppOfArity ``Exists 2 then some ``Exists.intro
    else if type.isAppOfArity ``Subtype 2 then some ``Subtype.mk
    else none
  if let some ctor := ctor? then
    try
      let head ← mkConstWithFreshMVarLevels ctor
      let hidden ← hideData head (← inferType head).getForallArity
      if ← withReducible <| isDefEq (← inferType hidden.skeleton) (← goal.getType) then
        let allClosed ← hidden.proofSlots.allM fun proof => do
          let proof ← instantiateMVars proof
          if proof.isMVar then structuralLocal proof.mvarId! facts (fuel - 1)
          else pure true
        if allClosed && (← hidden.dataSlots.allM fun data => return !(← instantiateMVars data).hasMVar) then
          goal.assign hidden.skeleton
          return true
    catch ex =>
      if ex.isMaxHeartbeat || ex.isInterrupt || ex.isRuntime then throw ex
    saved.restore
  return ← tryAssumptions goal facts

private def tacticLocal (goal : MVarId) (facts forbidden : Array Expr)
    (useOmega : Bool) : MetaM Bool := do
  let mut goal := goal
  for fact in forbidden.reverse do
    if (← goal.getDecl).lctx.contains fact.fvarId! then goal ← goal.clear fact.fvarId!
  goal.withContext do
    let target ← instantiateMVars (← goal.getType)
    if useOmega && target.hasMVar then return false
    if !useOmega then
      let mut theorems : SimpTheoremsArray := #[]
      for fact in facts do
        let type ← whnf (← inferType fact)
        if type.isAppOfArity ``Eq 3 || type.isAppOfArity ``Iff 2 then
          theorems ← theorems.addTheorem (.fvar fact.fvarId!) fact
      let context ← Simp.mkContext {failIfUnchanged := false} theorems {}
      let (remaining, _) ← simpGoal goal context (simprocs := #[])
      return remaining.isNone
    let goals ← try
      (Term.withoutErrToSorry <| Tactic.run goal (evalTactic (← `(tactic| omega)))).run'
    catch ex =>
      if ex.isMaxHeartbeat || ex.isInterrupt || ex.isRuntime then throw ex
      return false
    return goals.isEmpty

private def solveLocalGoal (goal : MVarId) (facts forbidden : Array Expr) : MetaM Bool := do
  for procedure in [:3] do
    let saved ← saveState
    let start ← IO.getNumHeartbeats
    let ok ← withTheReader Core.Context (fun ctx =>
        {ctx with initHeartbeats := start, maxHeartbeats := localBudget * 1000}) do
      match procedure with
      | 0 => structuralLocal goal facts
      | 1 => tacticLocal goal facts forbidden false
      | _ => tacticLocal goal facts forbidden true
    if ok then return true
    saved.restore
  return false

structure LocalResult where
  cost : EdgeCost := .unknown
  proof? : Option Expr := none
  detail : String := ""
  hiddenSlots : Nat := 0
  sharedData? : Option Bool := none

private def withFacts {α : Type} (types : List Expr)
    (action : Array Expr → MetaM α) : MetaM α := do
  let rec go (remaining : List Expr) (facts : Array Expr) : MetaM α := do
    match remaining with
    | [] => action facts
    | type :: rest => withLocalDeclD `_premise type fun fact => go rest (facts.push fact)
  go types #[]

/-- R_loc sees only the conclusion, head, scoped variables, and seed premises.
Nonseed types enter only after all hidden data has been fixed, to discharge
exact residual obligations and build the kernel-checked edge certificate. -/
partial def localRebuild (target : Expr) (head : Option Expr)
    (data : Array (Option Expr)) (seedTypes residualTypes : List Expr)
    (visible := false) (plan? : Option SpinePlan := none) : MetaM LocalResult := do
  let original ← saveState
  let started ← IO.getNumHeartbeats
  try
    let result ← withTheReader Core.Context (fun ctx =>
        {ctx with initHeartbeats := started, maxHeartbeats := localBudget * 1000}) do
      withFacts (seedTypes ++ residualTypes) fun allFacts => do
        let mut seeds := allFacts.extract 0 seedTypes.length
        let residuals := allFacts.extract seedTypes.length allFacts.size
        let targetGoal ← mkFreshExprMVar target
        let mut goal := targetGoal.mvarId!
        let mut scope := #[]
        while (← goal.withContext <| withReducible <| whnf (← goal.getType)).isForall do
          let (fvar, next) ← goal.intro1
          seeds := seeds.push (mkFVar fvar)
          scope := scope.push (mkFVar fvar)
          goal := next
        goal.withContext do
          let mut slots := #[]
          let mut sharedData := false
          let mut obligations := #[]
          let plan? := plan?.orElse (fun _ => head.map (fun h => SpinePlan.app h data []))
          if let some plan := plan? then
            let cleanContext := residuals.foldl (fun context fact => context.erase fact.fvarId!) (← getLCtx)
            let localInstances ← getLocalInstances
            let hidden ← withLCtx cleanContext localInstances <|
              replayPlan plan scope visible (← goal.getType)
            slots := hidden.dataSlots
            for slot in slots do
              for variableId in ← getMVars slot do
                let mut occurrences := 0
                for proof in hidden.proofSlots do
                  if (← getMVars (← inferType proof)).contains variableId then
                    occurrences := occurrences + 1
                if occurrences > 1 then sharedData := true
            unless ← withReducible <| isDefEq (← inferType hidden.skeleton) (← goal.getType) do
              return {cost := .one, detail := "head-result-mismatch"}
            for inst in hidden.instances do
              if (← instantiateMVars inst).hasMVar then
                let instanceType ← instantiateMVars (← inferType inst)
                if !instanceType.hasMVar then
                  let synthesized ← synthInstance instanceType
                  unless ← isDefEq inst synthesized do
                    return {cost := .one, detail := "instance-mismatch"}
            for proof in hidden.proofSlots do
              let proof ← instantiateMVars proof
              if proof.isMVar then
                let saved ← saveState
                if !(← solveLocalGoal proof.mvarId! seeds residuals) then saved.restore
                if !(← proof.mvarId!.isAssigned) then obligations := obligations.push proof.mvarId!
            for slot in slots do
              if hidden.instances.contains slot then continue
              let value ← instantiateMVars slot
              if value.hasMVar then
                let variables ← getMVars value
                let occurs ← obligations.anyM fun obligation => do
                  let remaining ← getMVars (← instantiateMVars (← obligation.getType))
                  return variables.any remaining.contains
                if occurs then
                  return {cost := .one, detail := "unresolved-hidden-data", hiddenSlots := slots.size, sharedData? := some sharedData}
                let type ← instantiateMVars (← inferType slot)
                let defaultInstance ← synthInstance (← mkAppM ``Inhabited #[type])
                let defaultValue ← mkAppOptM ``default #[some type, some defaultInstance]
                unless ← isDefEq slot defaultValue do
                  return {cost := .unknown, detail := "unconstrained-default-unavailable"}
            for inst in hidden.instances do
              if (← instantiateMVars inst).hasMVar then
                let instanceType ← instantiateMVars (← inferType inst)
                if instanceType.hasMVar then
                  return {cost := .one, detail := "unresolved-instance-data"}
                let synthesized ← synthInstance instanceType
                unless ← isDefEq inst synthesized do
                  return {cost := .one, detail := "instance-mismatch"}
            for obligation in obligations do
              let type ← instantiateMVars (← obligation.getType)
              let residualGoal ← mkFreshExprMVar type
              unless ← tryAssumptions residualGoal.mvarId! (residuals ++ seeds) do
                return {cost := .one, detail := "residual-interface-mismatch", hiddenSlots := slots.size, sharedData? := some sharedData}
              obligation.assign (← instantiateMVars residualGoal)
            -- Comparison happens after all data is fixed, so the author
            -- instance cannot assign a hidden data metavariable.
            for h : i in [:hidden.instances.size] do
              if let some author := hidden.instanceAuthors[i]?.join then
                let instanceValue ← instantiateMVars hidden.instances[i]
                unless !instanceValue.hasMVar do
                  return {cost := .unknown, detail := "unresolved-instance"}
                unless ← withReducible <| isDefEq instanceValue author do
                  return {cost := .one, detail := "author-instance-mismatch"}
            goal.assign hidden.skeleton
          else
            let mut solved ← solveLocalGoal goal seeds residuals
            if !solved then
              -- Administrative scope/let edges may consume their complete
              -- child sequent without exposing an author data argument.
              solved ← tryAssumptions goal (residuals ++ seeds)
            unless solved do return {cost := .one, detail := "normal-exhaustion"}
          let proof ← instantiateMVars targetGoal
          let proof ← mkLambdaFVars allFacts proof
          let certificateType ← mkForallFVars allFacts target
          checkLocalProof certificateType proof
          return {cost := .zero, proof? := some proof, detail := "kernel-checked", hiddenSlots := slots.size, sharedData? := some sharedData}
    original.restore
    if result.cost == .one && (head.isSome || plan?.isSome) then
      let alternate ← localRebuild target none #[] seedTypes residualTypes visible
      if alternate.cost != .one then return alternate
    return result
  catch ex =>
    original.restore
    let detail ← ex.toMessageData.toString
    if detail == "graph.hidden_spine_blocked" then
      let alternate ← localRebuild target none #[] seedTypes residualTypes visible
      if alternate.cost != .one then return alternate
      return {cost := .one, detail := "unresolved-hidden-telescope"}
    if detail == "graph.replay_head_result_mismatch" || detail == "graph.frontier_interface_mismatch" then
      return ← localRebuild target none #[] seedTypes residualTypes visible
    return {cost := .unknown, detail :=
      if ex.isMaxHeartbeat then "heartbeat"
      else if ex.isInterrupt then "cancelled"
      else s!"execution:{detail}"}

private def vertex (graph : ProofGraph) (id : Nat) : GraphVertex :=
  (graph.vertices.find? (·.id == id)).getD default

/-- Each arm invokes the same frozen function with its own seed set. -/
def priceGraph (graph : ProofGraph) (paired := false) (visible := false) : MetaM ProofGraph := do
  let mut edges := []
  for edge in graph.edges do
    let mut seeds := []
    let mut residuals := []
    for id in edge.premises do
      let v := vertex graph id
      if v.seed || (paired && v.structureSeed) then seeds := seeds ++ [v.type]
      else residuals := residuals ++ [v.type]
    let result ← localRebuild (vertex graph edge.conclusion).type edge.head edge.authorData seeds residuals visible edge.plan?
    let edge := if visible then
        if paired then {edge with pairedVisibleCost := result.cost}
        else {edge with visibleCost := result.cost}
      else if paired then {edge with pairedCost := result.cost, pairedZeroProof := result.proof?}
      else {edge with cost := result.cost, zeroProof := result.proof?, detail := result.detail, sharedData? := result.sharedData?}
    edges := edges ++ [edge]
  return {graph with edges}

/-- Roots are actual R_loc attempts; finite DP values are never probe success. -/
def rootProbe (graph : ProofGraph) (paired := false) : MetaM ProbeResult := do
  let seeds := graph.vertices.filter (fun v => v.seed || (paired && v.structureSeed))
  let types := seeds.map GraphVertex.type
  let result ← localRebuild (vertex graph graph.root).type none #[] types []
  let outcome := match result.cost with
    | .zero => Run.found | .one => .exhausted | .unknown => .incomplete .undecided
  return {outcome, checked := result.proof?.isSome, proof? := result.proof?, detail := result.detail}

private def armGraph (graph : ProofGraph) (paired visible : Bool) : ProofGraph :=
  {graph with edges := graph.edges.map fun edge =>
    {edge with cost := if visible then
      (if paired then edge.pairedVisibleCost else edge.visibleCost)
      else if paired then edge.pairedCost else edge.cost}}

private def armSeeds (graph : ProofGraph) (paired : Bool) : List Nat :=
  (graph.vertices.filter (fun v => v.seed || (paired && v.structureSeed))).map (·.id)

/-- Assemble only selected zero-cost certificates, never author nonseed bodies. -/
def assembleZero (graph : ProofGraph) (paired := false) : MetaM (Option Expr) := do
  let arm := armGraph graph paired false
  let seeds := armSeeds graph paired
  let table := dpTable arm costUpper seeds
  let rec go (fuel : Nat) (id : Nat) : MetaM (Option Expr) := do
    if h : fuel = 0 then return none
    let v := vertex graph id
    if v.seed then
      return some (← withLCtx v.lctx v.instances <| mkLambdaFVars v.scope v.origin)
    if paired && v.structureSeed then return v.structureProof?
    let some index := (table[id]?.getD {}).edge? | return none
    let some edge := graph.edges[index]? | return none
    let some schema := if paired then edge.pairedZeroProof else edge.zeroProof | return none
    let ordered := if edge.window == 0 then edge.premises else
      edge.premises.filter (fun p => seeds.contains p) ++
        edge.premises.filter (fun p => !seeds.contains p)
    let mut arguments := #[]
    for p in ordered do
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

/-- Freeze the author graph, add one k=2 cut per edge, price both arms and the
visible-data ablation, and perform the two independent checked root probes. -/
def evaluateGraph (raw : ProofGraph) : MetaM GraphReading := do
  let cuts := k2Frontier raw
  -- The deterministic frontier contributes at most one edge per author edge.
  let graph := {raw with edges := raw.edges ++ cuts}
  let graph ← priceGraph graph
  let graph ← priceGraph graph true
  let graph ← priceGraph graph false true
  let graph ← priceGraph graph true true
  let baseProbe ← rootProbe graph
  let pairedProbe ← rootProbe graph true
  let mut graph := graph
  if baseProbe.checked then
    graph := {graph with edges := graph.edges ++ [{
      conclusion := graph.root, premises := armSeeds graph false, window := 0,
      cost := .zero, pairedCost := .zero, visibleCost := .zero, pairedVisibleCost := .zero,
      zeroProof := baseProbe.proof?, pairedZeroProof := baseProbe.proof?, detail := "baseline-root-probe"}]}
  if pairedProbe.checked && !baseProbe.checked then
    graph := {graph with edges := graph.edges ++ [{
      conclusion := graph.root, premises := armSeeds graph true, window := 0,
      cost := if baseProbe.outcome == .exhausted then .one else .unknown,
      pairedCost := .zero, visibleCost := .unknown, pairedVisibleCost := .zero,
      pairedZeroProof := pairedProbe.proof?, detail := "paired-root-probe"}]}
  let pairedGraph := armGraph graph true false
  let baseSeeds := armSeeds graph false
  let pairSeeds := armSeeds graph true
  let k1 := {graph with edges := graph.edges.filter (·.window != 2)}
  let selectedSeeds := optimalSeeds pairedGraph costUpper pairSeeds
  return {
    graph, baseline := graphInterval graph baseSeeds,
    paired := graphInterval pairedGraph pairSeeds,
    baselineK1 := graphInterval k1 baseSeeds,
    pairedK1 := graphInterval (armGraph k1 true false) pairSeeds,
    baselineVisible := graphInterval (armGraph graph false true) baseSeeds,
    pairedVisible := graphInterval (armGraph graph true true) pairSeeds,
    baselineProbe := baseProbe, pairedProbe, selectedSeeds,
    pairedUsesSeed := selectedSeeds.any (fun id =>
      let v := vertex graph id
      v.structureSeed && !v.seed)}

end LeanInformationAudit.SearchReduction
