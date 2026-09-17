import LeanInformationAudit.ReadoutProvenance.Types
namespace LeanInformationAudit.RegistrationGates
open Lean


-- The sole admission entry: infer the occurrence in its lexical context, then
-- fold its inferred type. Nested type syntax is handled by the same type fold.
private def classifyOccurrence (env : Environment) (occurrence : Expr)
    (context : Array Expr) : WalkM TypeClassification := do
  let context := if occurrence.hasLooseBVars then context else #[]
  unless ← chargeTraversal (2 * context.size + 1) do return .incomplete
  let key := (occurrence, context, (← get).currentFirst)
  -- admission-exit: classifyOccurrence.1 rule=retained-witness.rule
  if let some cached := (← get).typeChecks[key]? then return cached
  let verdict ← inBinderContext context fun locals => do
    let some occurrence ← substitute occurrence locals | return .incomplete
    let some type ← occurrenceType occurrence | return .incomplete
    let exact ← exactScalarStatement type
    let decision ← if type.isAppOfArity ``Decidable 1 then
        exactScalarStatement type.getAppArgs[0]! else pure false
    let classification ← observedType env type
    let (mentions, _) := classification.flags
    if exact || decision then return .forbidden
    if mentions then return .statementMention
    let state ← get
    if state.forbidden then return .forbidden
    if state.incomplete then return .incomplete
    if let some site := state.unclassified then return .unclassified site
    -- admission-exit: classifyOccurrence.2 rule=retained-witness.rule
    return classification
  let verdict ← match verdict with
    | some verdict => pure verdict
    | none => if (← get).incomplete then pure .incomplete else unknownType occurrence
  unless ← chargeTraversal context.size do return .incomplete
  modify fun s => { s with typeChecks := s.typeChecks.insert key verdict }
  -- admission-exit: classifyOccurrence.3 rule=retained-witness.rule
  return verdict

-- Check a node before requesting its children. Independent Prop proofs are
-- leaves after identity and inferred-type checks; their bodies are never cached
-- or traversed. Type-valued decision dictionaries remain executable nodes.
private partial def visitOccurrence (env : Environment) (pos : Position)
    (origin : Name) (e : Expr) (context : Array Expr := #[]) : WalkM Unit := do
  unless ← chargeSummaryWork (fun c => { c with dispatchWork := c.dispatchWork + 1 }) do return
  let first := e.getAppFn.constName?.getD origin
  modify fun s => { s with currentFirst := first, currentOrigin := origin }
  if let .const n _ := e.getAppFn then
    modify fun s => { s with retainedInputs := s.retainedInputs.insert n }
    directConstant env n
  if let .proj n _ _ := e then directProjection env n
  if (← get).forbidden then return
  if ReadoutFamily.carrierHeads.contains first && e.isApp then
    let decoded ← inBinderContext context fun locals => do
      let some actual ← substitute e locals | return false
      let (value, work) := ReadoutFamily.carrier env actual (← get).exprFuel
      unless ← chargeTraversal work do return false
      let some value := value | return false
      if value == actual then return false
      visitOccurrence env .typePos origin value
      return true
    -- admission-exit: visitOccurrence.1 rule=retained-witness.rule
    if decoded == some true then return
  let key := (e, pos, context)
  -- admission-exit: visitOccurrence.2 rule=retained-witness.rule
  if (← get).visited.contains key then return
  modify fun s => { s with visited := s.visited.insert key }
  let verdict ← classifyOccurrence env e context
  match verdict with
  | .forbidden => modify fun s => { s with forbidden := true }; return
  | .statementMention => noteUnclassified ⟨"statement_mentioning_type", first, namespaceLabel env first, origin⟩
  | .unclassified site => noteUnclassified site
  | .incomplete => noteIncomplete `incomplete_classification `type_classification; return
  -- admission-exit: visitOccurrence.forward.1 rule=retained-witness.rule
  | .allowlisted _ => pure ()
  let actualContext := if e.hasLooseBVars then context else #[]
  let proof ← inBinderContext actualContext fun locals => do
    let some actual ← substitute e locals | return false
    let some type ← occurrenceType actual | return false
    if pos == .dataPos && type == .sort .zero && closed actual then
      if let .const n _ := actual.getAppFn then
        if inProtected env n && (env.find? n).any (fun i => i.hasValue) then
          noteUnclassified ⟨"closed_decision", n, namespaceLabel env n, origin⟩
    if type == .sort .zero then
      -- Propositions are checked as statement-bearing types. Their mathematical
      -- operands are erased; executable decision dictionaries are visited on
      -- their own actual data occurrences.
      let classification ← observedType env actual
      let (mentions, unknown) := classification.flags
      if mentions then
        noteUnclassified ⟨"statement_mentioning_type", first, namespaceLabel env first, origin⟩
      if unknown then
        noteUnclassified ⟨"unclassified_argument_type", first, namespaceLabel env first, origin⟩
      return true
    let some proof ← boundedMeta (Meta.isProp type) `proof_boundary | return false
    return proof
  -- admission-exit: visitOccurrence.3 rule=retained-witness.rule
  if proof == some true then return
  let child := fun e context => visitOccurrence env pos origin e context
  match e with
  | .const n levels =>
    modify fun s => { s with walked := s.walked.insert n }
    if pos == .dataPos && n.getRoot == `Classical then
      noteUnclassified ⟨"classical_choice", n, namespaceLabel env n, origin⟩
    if pos == .dataPos && !inProtected env n && !Lean.Meta.isInstanceCore env n then
      if let some type ← occurrenceType e then
        if let some h ← resultHead type then
          if decisionFamily.contains h && !listedProducers.contains n then
            noteUnclassified ⟨"unlisted_decision_producer", n, namespaceLabel env n, origin⟩
    if (env.find? n).isNone then noteIncomplete `missing_constant `occurrence_lookup
    -- admission-exit: visitOccurrence.4 rule=retained-witness.rule
    else if inProtected env n then queue n levels
  | .app f a =>
    unless ← chargeSummaryWork (fun c => { c with spineArguments := c.spineArguments + 2 }) 2 do return
    child f context
    child a context
  | .lam _ type body _ | .forallE _ type body _ =>
    if pos == .dataPos && closed type then
      if let .const n _ := type.getAppFn then
        if inProtected env n then
          let some kind ← occurrenceType type | return
          if kind == .sort .zero then
            noteUnclassified ⟨"closed_decision", n, namespaceLabel env n, origin⟩
    visitOccurrence env .typePos origin type context
    child body (context.push e)
  | .letE _ type value body _ =>
    if pos == .dataPos && closed type then
      if let .const n _ := type.getAppFn then
        if inProtected env n then
          let some kind ← occurrenceType type | return
          if kind == .sort .zero then
            noteUnclassified ⟨"closed_decision", n, namespaceLabel env n, origin⟩
    visitOccurrence env .typePos origin type context
    child value context
    child body (context.push e)
  | .proj _ _ receiver => child receiver context
  | .mdata _ body => child body context
  | .mvar _ => noteIncomplete `unresolved_metavariable `occurrence_traversal
  | .lit _ | .sort _ | .fvar _ | .bvar _ =>
    match verdict with
    -- admission-exit: visitOccurrence.5 rule=retained-witness.rule
    | .allowlisted _ => pure () -- syntaxLeaf: already inferred in its real binder context
    | _ => noteUnclassified ⟨"unclassified_syntax_leaf", first, namespaceLabel env first, origin⟩

private def visitSummary (env : Environment) (origin : Name) (summary : Summary) : WalkM Unit := do
  if summary.incomplete then noteIncomplete `incomplete_summary `summary_traversal
  for index in summary.roots do
    let node := summary.nodes[index]!
    visitOccurrence env node.position origin node.expr

private def visit (env : Environment) (pos : Position) (origin : Name) (e : Expr) : WalkM Unit := do
  let summary ← summarise env #[(pos, e)] (← get).exprFuel
  unless ← chargeSummaryWork (fun c => { c with constructionWork := c.constructionWork + summary.constructionWork }) summary.constructionWork do return
  modify fun s => { s with counters.visits := s.counters.visits + summary.visits }
  visitSummary env origin summary

private def process (env : Environment) : WalkM Unit := do
  while !(← get).forbidden do
    unless ← chargeSummaryWork (fun c => { c with dispatchWork := c.dispatchWork + 1 }) do break
    let some n := (← get).pending.head? | break
    modify fun s => { s with pending := s.pending.tail!, walked := s.walked.insert n.1, currentFirst := n.1, currentOrigin := n.1 }
    if (← get).exprFuel == 0 then
      noteIncomplete `expression_budget `constant_dispatch
      break
    let some info := env.find? n.1 | noteIncomplete `missing_constant `constant_dispatch; continue
    let summary ← if let some cached := (← get).summaries[n]? then do
        modify fun s => { s with counters.memoHits := s.counters.memoHits + 1 }
        pure cached
      else do
        let some type ← occurrenceType (mkConst n.1 n.2) | continue
        let some proof ← boundedMeta (Meta.isProp type) `declaration_proof_boundary | continue
        let summary ← if proof then summarise env #[(.typePos, type)] (← get).exprFuel
          else if info.hasValue (allowOpaque := true) then do
            let valuePos := match info with | .thmInfo _ => .proofPos | _ => .dataPos
            let value ← Core.instantiateValueLevelParams info n.2 (allowOpaque := true)
            summarise env #[(.typePos, type), (valuePos, value)] (← get).exprFuel
          else do
            let summary ← summarise env #[(.typePos, type)] (← get).exprFuel
            pure { summary with incomplete := summary.incomplete || !isCtorOrInductive env n.1 &&
              !#[`propext, `Classical.choice, `Quot.sound].contains n.1 }
        let _ ← chargeSummaryWork (fun c => { c with constructionWork := c.constructionWork + summary.constructionWork }) summary.constructionWork
        modify fun s => { s with
          counters.summarisedConstants := s.counters.summarisedConstants + 1
          counters.visits := s.counters.visits + summary.visits }
        if !summary.incomplete then
          modify fun s => { s with summaries := s.summaries.insert n summary }
        pure summary
    visitSummary env n.1 summary

private structure WalkResult where
  forbidden : Bool
  unclassified : Option Unclassified
  incomplete : Bool
  admission : Option ProvenanceAdmissionWitness := none
  walked : Array String
  walkedNames : Array Name := #[]
  inputNames : Array Name := #[]

private def collectReadout (env : Environment) (theoremName address : Name) (readout : Expr) (extractionWork : Nat := 0) (extractionFailed : Bool := false) : CoreM WalkResult := do
  let scope := (moduleScopeCache.getState env).getD (classifyModules env)
  let env := moduleScopeCache.setState env (some scope)
  modifyEnv (moduleScopeCache.setState · (some scope))
  let some theoremInfo := env.find? theoremName | do
    trace[InformationProvenance.check]
      "incomplete cause=missing_constant operation=registered_statement first={theoremName} site={address}"
    return { forbidden := false, unclassified := none, incomplete := true, walked := #[] }
  let statement ← Meta.MetaM.run' <| Meta.inferType
    (mkConst theoremName (theoremInfo.levelParams.map Level.param))
  let decision := mkApp (mkConst ``Decidable) statement
  let computation : WalkM Unit := do
    unless ← chargeTraversal extractionWork do return
    if extractionFailed then
      noteIncomplete `extraction_failure `readout_extraction
      return
    statementAliases env
    visit env .dataPos address readout
    process env
  let budget := min provenanceExpressionFuel (provenanceExpressionLimit.get (← getOptions))
  let (_, state) ← Meta.MetaM.run' <| computation.run {
    theoremName, currentFirst := address, currentOrigin := address, statement, decision, summaries := summaryCache.getState env, exprFuel := budget }
  let counters := { state.counters with chargedVisits := budget - state.exprFuel }
  modifyEnv (summaryCache.setState · state.summaries)
  modifyEnv (countersCache.setState · counters)
  trace[InformationProvenance.check]
    "theorem={theoremName} P_constants_summarised={counters.summarisedConstants} visits={counters.visits} memo_hits={counters.memoHits} charged_visits={counters.chargedVisits} rechecked_nodes={counters.recheckedNodes} spine_arguments={counters.spineArguments} canonicalizations={counters.canonicalizations} construction_work={counters.constructionWork} traversal_work={counters.traversalWork} dispatch_work={counters.dispatchWork} inferred_occurrences={counters.inferredOccurrences} case_expansions={counters.caseExpansions} family_memo_hits={counters.familyMemoHits}"
  let rootProducer := readout.getAppFn.constName?.getD address
  let admission := (state.typeChecks[(readout, (#[] : Array Expr), rootProducer)]?).bind
    TypeClassification.witness?
  let names := state.walked.toArray.map Name.toString |>.qsort (· < ·)
  let unclassified := if admission.isNone && !state.incomplete && !state.forbidden &&
      state.unclassified.isNone then
    some ⟨"unclassified_root", address, namespaceLabel env address, address⟩
    else state.unclassified
  let inputNames := state.walked.toArray.foldl (fun inputs n => inputs.insert n) state.retainedInputs
  return ⟨state.forbidden, unclassified, state.incomplete, admission, names,
    state.walked.toArray, inputNames.toArray⟩

private def safeCollect (env : Environment) (theoremName address : Name) (readout : Expr)
    (extractionWork : Nat := 0) (extractionFailed : Bool := false) : CoreM WalkResult :=
  tryCatchRuntimeEx (collectReadout env theoremName address readout extractionWork extractionFailed)
    (fun ex => do
      trace[InformationProvenance.check] "incomplete cause=collection_failure operation=collect_readout first={address} site={address}: {ex.toMessageData}"
      pure { forbidden := false, unclassified := none, incomplete := true, walked := #[] })

/-- Query in the current environment, retaining only reusable syntax summaries. -/
def readoutClosureCurrent (theoremName : Name) (readout : Expr) : CoreM (Bool × Option (Array String)) := do
  let env ← getEnv
  let r ← safeCollect env theoremName `readout readout
  if r.incomplete then return (false, none)
  if r.forbidden || r.unclassified.isSome then return (true, some r.walked)
  -- admission-exit: readoutClosureCurrent.1 rule=retained-witness.rule
  if r.admission.isSome then return (false, some r.walked)
  return (true, some r.walked)

def readoutClosure (env : Environment) (theoremName : Name) (readout : Expr) : CoreM (Bool × Option (Array String)) :=
  withEnv env (readoutClosureCurrent theoremName readout)

private def unclassifiedJson (u : Unclassified) (walked : Array String) : Json :=
  Json.mkObj [
    ("class", Json.str u.className), ("first", Json.str u.firstName.toString),
    ("namespace", Json.str u.namespaceName), ("site", Json.str u.siteName.toString),
    ("walked", Json.arr (walked.map Json.str))]

private initialize wholeReadoutCalls : EnvExtension Nat ← registerEnvExtension (pure 0)

/-- Output-only count of actual legacy whole-realization audit invocations. -/
def observedWholeReadoutCalls : CoreM Nat :=
  return wholeReadoutCalls.getState (← getEnv)

def provenanceErrorCurrent (root catalog theoremName realization : Name) : CoreM (Option String) := do
  modifyEnv fun env => wholeReadoutCalls.modifyState env (· + 1)
  let env ← getEnv
  let budget := min provenanceExpressionFuel (provenanceExpressionLimit.get (← getOptions))
  let (readout, extractionWork) := ReadoutFamily.extract env realization budget
  let address := readout.map (·.2) |>.getD realization
  let result ← match readout with
    | some (e, _) => safeCollect env theoremName address e extractionWork
    | none => safeCollect env theoremName address (.sort .zero) extractionWork true
  -- admission-exit: provenanceErrorCurrent.1 rule=retained-witness.rule
  if result.admission.isSome && !result.forbidden && result.unclassified.isNone && !result.incomplete then return none
  let reason := if result.incomplete then "incomplete_closure"
    else if result.forbidden then "forbidden_dependency" else "unclassified_form"
  let payload := if result.incomplete then Json.null
    else if result.forbidden then Json.arr (result.walked.map Json.str)
    else if let some u := result.unclassified then unclassifiedJson u result.walked
    else Json.null
  return some s!"IE-C050 ClosedTruthReadout key={root}/{catalog}/{theoremName} readout={address} reason={reason} provenance={payload.compress}"

def provenanceError (env : Environment) (root catalog theoremName realization : Name) : CoreM (Option String) :=
  withEnv env (provenanceErrorCurrent root catalog theoremName realization)

/-- The independently retained P1 provider contract audits its raw reifier
arguments. Declared templates use the enrollment grammar instead. All arguments share one lower-only debit, including
reused syntax summaries; no template body is sent through this path. -/
def providerArgumentsCurrent (theoremName : Name) (arguments : Array Expr)
    (availableWork : Nat) : CoreM (Except String (Array Name × Nat)) := do
  let mut remaining := min 524288 availableWork
  let mut inputs : NameSet := {}
  for index in [:arguments.size] do
    if remaining == 0 then return .error "incomplete_closure:E8.argument_work"
    let argument := arguments[index]!
    let result ← withOptions (fun options => options.set
        `provenanceExpressionLimit (min remaining (provenanceExpressionLimit.get options))) <|
      safeCollect (← getEnv) theoremName (.num `argument index) argument
    let counters := countersCache.getState (← getEnv)
    let used := counters.chargedVisits
    if used > remaining then return .error "incomplete_closure:E8.argument_work"
    remaining := remaining - used
    if result.incomplete then return .error "incomplete_closure:dtr.argument_audit"
    if result.forbidden then return .error "forbidden_dependency:dtr.argument_audit"
    if result.unclassified.isSome || result.admission.isNone then
      return .error "unclassified_form:dtr.argument_audit"
    for name in result.inputNames do inputs := inputs.insert name
  return .ok (inputs.toArray, min 524288 availableWork - remaining)

/-- One raw node's occurrence-relative rejection checks. This grants no
executable/type admission; the shared E2–E5 compiler owns that judgment. -/
def argumentIdentityNode (env : Environment) (expression : Expr) : WalkM Unit := do
  unless ← chargeTraversal do return
  if let .const name _ := expression.getAppFn then directConstant env name
  if let .proj name _ _ := expression then directProjection env name
  let some type ← occurrenceType expression | return
  let exact ← exactScalarStatement type
  let decision ← if type.isAppOfArity ``Decidable 1 then
    exactScalarStatement type.getAppArgs[0]! else pure false
  if exact || decision then modify fun s => { s with forbidden := true }
  let proposition := type == .sort .zero
  let some proof ← boundedMeta (Meta.isProp type) `raw_argument_proof_type | return
  if proposition || proof then
    let candidate := if proposition then expression else type
    if candidate.equal (← get).statement then
      modify fun s => { s with forbidden := true }
    else if (← checkedStatementType env candidate).isNone then
      noteUnclassified ⟨"unresolved_statement_identity", (← get).currentFirst,
        "argument", (← get).currentOrigin⟩

/-- Initialize identity-only state once for the whole supplied telescope. -/
def argumentIdentityState (theoremName : Name) (available : Nat) : Meta.MetaM WalkState := do
  let env ← getEnv
  let info ← getConstInfo theoremName
  let (_, state) ← (statementAliases env).run {
    theoremName, statement := info.type,
    decision := mkApp (mkConst ``Decidable) info.type, exprFuel := available }
  return state

-- Enrollment supplies the positive E2 grammar judgment. Consumption checks
-- only statement identity in the retained, instantiated syntax and inferred
-- proof types. Unknown identity remains unclassified; proof implementations stop.
private partial def retainedTypeIdentity (env : Environment) (expression : Expr) : WalkM Unit := do
  unless ← chargeTraversal do return
  if let .const name _ := expression.getAppFn then directConstant env name
  if let .proj name _ _ := expression then directProjection env name
  let some type ← occurrenceType expression | return
  let proposition := type == .sort .zero
  let some proof ← boundedMeta (Meta.isProp type) `retained_proof_type | return
  if proposition || proof then
    let candidate := if proposition then expression else type
    if candidate.equal (← get).statement then
      modify fun s => { s with forbidden := true }
    else if (← checkedStatementType env candidate).isNone then
      noteUnclassified ⟨"unresolved_statement_identity", (← get).currentFirst,
        "template", (← get).currentOrigin⟩
  if proof then return
  let child := retainedTypeIdentity env
  match expression with
  | .app f a => child f; child a
  | .lam name domain body bi | .forallE name domain body bi =>
    child domain
    Meta.withLocalDecl name bi domain fun x => do
      let some body ← substitute body #[x] | return
      child body
  | .letE _ type value body _ =>
    child type
    child value
    let some body ← substitute body #[value] | return
    child body
  | .mdata _ body | .proj _ _ body => child body
  | .mvar _ | .bvar _ => noteIncomplete `open_type_obligation `instantiated_type
  | _ => pure ()

/-- Consume retained type obligations in their original lexical contexts. This
entry runs the occurrence-relative type judgment, never a template body or proof
implementation. All obligations share one lower-only traversal budget. -/
def templateTypesCurrent (theoremName : Name) (types : Array (Expr × Array Expr))
    (availableWork : Nat) : CoreM (Except String Nat) := do
  let env ← getEnv
  let some info := env.find? theoremName
    | return .error "incomplete_closure:dtr.instantiated_type"
  let statement := info.type
  let budget := min (min 524288 availableWork) (provenanceExpressionLimit.get (← getOptions))
  let action : WalkM Unit := do
    statementAliases env
    for (type, context) in types do
      let checked ← inBinderContext context fun locals => do
        let some type ← substitute type locals | return false
        retainedTypeIdentity env type
        return true
      if checked != some true then noteIncomplete `type_obligation `instantiated_type
  let (_, state) ← Meta.MetaM.run' <| action.run {
    theoremName, currentFirst := theoremName, currentOrigin := theoremName,
    statement, decision := mkApp (mkConst ``Decidable) statement, exprFuel := budget }
  if state.incomplete then return .error "incomplete_closure:dtr.instantiated_type"
  if state.forbidden then return .error "forbidden_dependency:dtr.instantiated_type"
  if state.unclassified.isSome then return .error "unclassified_form:dtr.instantiated_type"
  return .ok (budget - state.exprFuel)

end LeanInformationAudit.RegistrationGates
