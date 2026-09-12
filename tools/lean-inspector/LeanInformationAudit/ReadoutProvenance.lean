import Lean

namespace LeanInformationAudit.RegistrationGates
open Lean

def provenanceConstantFuel : Nat := 4096
def provenanceExpressionFuel : Nat := 524288

def provenanceJudgeAPIs : Array Name := #[
  `LeanInformationAudit.InformationRegistry.entries,
  `LeanInformationAudit.InformationRegistry.find?,
  `LeanInformationAudit.InformationRegistry.hasTheorem,
  `LeanInformationAudit.InformationRegistry.hasOccurrence,
  `LeanInformationAudit.InformationRegistry.hasUnit,
  `LeanInformationAudit.InformationRegistryEntry.statementIdentity,
  `LeanInformationAudit.ExpectedOccurrence.statementIdentity,
  `LeanInformationAudit.theoremStatementIdentity,
  `LeanInformationAudit.Sha256.digest, `LeanInformationAudit.Sha256.hex,
  `LeanInformationAudit.StatementKey.mk, `LeanInformationAudit.StatementKey.statementId,
  `LeanInformationAudit.ClosedNumericalObligation.mk,
  `LeanInformationAudit.InfinitePrimitiveObligation.mk,
  `LeanInformationAudit.UnfaithfulPrimitiveObligation.mk,
  `LeanInformationAudit.FiniteOccurrenceDisposition.mk,
  `LeanInformationAudit.StructuralOccurrenceDisposition.mk,
  `LeanInformationAudit.BoundedFiniteTruncationDisposition.mk,
  `LeanInformationAudit.UnreachableDisposition.mk]

initialize registerTraceClass `InformationProvenance.check

private def recordHead (env : Environment) : Nat → Expr → Option Expr
  | 0, _ => none
  | fuel + 1, e => do
    let args := e.getAppArgs
    match e.getAppFn with
    | .mdata _ body => recordHead env fuel (mkAppN body args)
    | .letE _ _ value body _ => recordHead env fuel (mkAppN (body.instantiate1 value) args)
    | .lam _ _ _ _ => if args.isEmpty then some e else recordHead env fuel (e.getAppFn.beta args)
    | .const name levels =>
      match env.find? name with
      | some (.defnInfo info) =>
        recordHead env fuel (mkAppN (info.value.instantiateLevelParams info.levelParams levels) args)
      | some _ => some e
      | none => none
    | .proj _ index value =>
      let value ← recordHead env fuel value
      let .const name _ := value.getAppFn | some e
      let some (.ctorInfo info) := env.find? name | some e
      let field ← value.getAppArgs[info.numParams + index]?
      recordHead env fuel (mkAppN field args)
    | _ => some e

private def familyCarriers (env : Environment) : Nat → Expr → Option Expr
  | 0, _ => none
  | fuel + 1, e => do
    if #[
      `D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index,
      `D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Output,
      `D5.S3.ConceptDynamics.InformationEscape.Arena.State,
      `LeanInformationAudit.StructuralPrimitiveSignature.Index,
      `LeanInformationAudit.StructuralPrimitiveSignature.Output,
      `LeanInformationAudit.StructuralArena.State].contains (e.getAppFn.constName?.getD .anonymous) then
      return ← familyCarriers env fuel (← recordHead env 256 e)
    let go := familyCarriers env fuel
    match e with
    | .app f a => return .app (← go f) (← go a)
    | .lam n t b bi => return .lam n (← go t) (← go b) bi
    | .forallE n t b bi => return .forallE n (← go t) (← go b) bi
    | .letE n t v b nd => return .letE n (← go t) (← go v) (← go b) nd
    | .mdata m b => return .mdata m (← go b)
    | .proj n i b => return .proj n i (← go b)
    | _ => return e

private def readoutFamily (env : Environment) (realization : Name) : Option Expr := do
  let info ← env.find? realization
  let root ← match info with
    | .thmInfo info => do
      let type ← recordHead env 256 info.type
      unless type.isAppOfArity `D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization 3 do none
      type.getAppArgs[2]?
    | .defnInfo _ => some (mkConst realization)
    | _ => none
  let value ← recordHead env 256 root
  let name ← value.getAppFn.constName?
  unless name == `D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.mk ||
      name == `LeanInformationAudit.StructuralPrimitiveRealization.mk do none
  familyCarriers env 256 (← value.getAppArgs[2]?)

private def generatedAddress : Name → Bool
  | .str parent suffix =>
      #["__information_unit", "__primitive_realization", "__structural_unit",
        "__structural_realization", "__information_catalog", "__lowers_escape",
        "__escape_enriched", "__trivial_in_catalog", "__state_enumeration",
        "__information_registration_diagnostic", "__kernel_projection"].contains suffix ||
      suffix.startsWith "__catalog_" || suffix.startsWith "__system_catalog_" || generatedAddress parent
  | .num parent _ => generatedAddress parent
  | .anonymous => false

private def judgePayload (info : ConstantInfo) : Bool :=
  match info with
  | .ctorInfo ctor => #[
      `LeanInformationAudit.InformationRegistryEntry, `LeanInformationAudit.ExpectedOccurrence,
      `LeanInformationAudit.CatalogUnitRecord, `LeanInformationAudit.CatalogRecord,
      `LeanInformationAudit.SealTheoremRecord, `LeanInformationAudit.SealArenaRecord,
      `LeanInformationAudit.SealedOccurrenceState, `LeanInformationAudit.StagedAnalysisState,
      `LeanInformationAudit.StructuralProvenanceEntry,
      `LeanInformationAudit.StructuralRegistrationEvidence,
      `LeanInformationAudit.BoundedTruncationFamily,
      `LeanInformationAudit.UnreachableElaborationEvidence,
      `LeanInformationAudit.AnalysisDisposition, `LeanInformationAudit.CensusAssessment,
      `LeanInformationAudit.AnalysisObservation, `LeanInformationAudit.DispositionInventory,
      `LeanInformationAudit.TruncationCertification].contains ctor.induct
  | _ => false

private def stripMData : Expr → Expr
  | .mdata _ e => stripMData e
  | e => e

private def eraseLevels (e : Expr) : Expr :=
  let params := (collectLevelParams {} e).params.toList
  stripMData (e.instantiateLevelParams params (params.map fun _ => .zero))

private def closed (e : Expr) : Bool := !e.hasLooseBVars && !e.hasFVar && !e.hasMVar

private def telescopeResult : Expr → Expr
  | .forallE _ _ body _ => telescopeResult body
  | .mdata _ e => telescopeResult e
  | e => e

private def resultHead (e : Expr) : Option Name := (telescopeResult e).getAppFn.constName?

private def decisionFamily : Array Name := #[
  ``Decidable, ``DecidablePred, ``DecidableRel, ``DecidableEq,
  ``DecidableLE, ``DecidableLT]

private def listedProducers : Array Name := #[
  ``Decidable.isTrue, ``Decidable.isFalse, ``decidable_of_iff, ``decidable_of_iff',
  ``decidable_of_bool, ``decidable_of_decidable_of_iff, ``decidable_of_decidable_of_eq,
  ``decEq, ``Nat.decEq, ``Nat.decLt, ``Nat.decLe, ``Bool.decEq,
  ``instDecidableEqOfLawfulBEq, ``inferInstance, `Equiv.decidableEq]

private def appliedType (env : Environment) (e : Expr) : Option Expr := do
  let .const n levels := e.getAppFn | none
  let info ← env.find? n
  let mut type := info.type.instantiateLevelParams info.levelParams levels
  for arg in e.getAppArgs do
    let .forallE _ _ body _ := stripMData type | none
    type := body.instantiate1 arg
  return stripMData type

private def propLooking (env : Environment) : Expr → CoreM Bool
  | .forallE _ _ body _ => propLooking env body
  | .mdata _ e => propLooking env e
  | e => pure (appliedType env e == some (.sort .zero))

private def isCtorOrInductive (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | some (.inductInfo _) | some (.ctorInfo _) | some (.recInfo _) | some (.quotInfo _) => true
  | _ => false

private def moduleName (env : Environment) (n : Name) : Name :=
  (env.getModuleIdxFor? n).map (env.header.moduleNames[·.toNat]!) |>.getD env.header.mainModule

private def inProtected (env : Environment) (n : Name) : Bool :=
  if (env.getModuleIdxFor? n).isNone then true else
    let m := moduleName env n
    m == env.header.mainModule || m.getRoot == `D5 || m.getRoot == `LeanInformationAudit

private def namespaceLabel (env : Environment) (n : Name) : String :=
  if n.getRoot == `Classical then "external:Classical"
  else if inProtected env n then
    if moduleName env n == env.header.mainModule then "protected:current"
    else if n.getRoot == `LeanInformationAudit then "protected:judge" else "protected:D5"
  else "external:other"

private structure Unclassified where
  className : String
  firstName : Name
  namespaceName : String
  siteName : Name

private inductive Position where | dataPos | proofPos | typePos
  deriving BEq, Hashable, Inhabited

-- These summaries contain syntax and its fixed classifications, never a verdict
-- for a registered statement. Child indices precede their parents, so subterm
-- membership is recomputed by a linear fold without walking Expr trees again.
private structure SyntaxNode where
  expr : Expr
  canonical : Expr
  position : Position
  children : Array Nat
  prop : Bool
  pContent : Bool
  declaredType : Option Expr
  deriving Inhabited

private structure Summary where
  nodes : Array SyntaxNode := #[]
  roots : Array Nat := #[]
  visits : Nat := 0
  incomplete : Bool := false
  deriving Inhabited

private structure SummaryBuild where
  summary : Summary := {}
  indices : Std.HashMap (Expr × Position) Nat := {}
  fuel : Nat

private abbrev SummaryM := StateRefT SummaryBuild CoreM

private partial def summariseExpr (env : Environment) (pos : Position) (raw : Expr) :
    SummaryM (Option Nat) := do
  let s ← get
  if s.fuel == 0 then
    modify fun s => { s with summary.incomplete := true }
    return none
  if s.summary.visits % 256 == 0 then Core.checkMaxHeartbeats "readout provenance"
  modify fun s => { s with fuel := s.fuel - 1, summary.visits := s.summary.visits + 1 }
  let e := stripMData raw
  if let some i := (← get).indices[(e, pos)]? then return some i
  let inputs : Array (Position × Expr) := match e with
    | .app f a => #[(pos, f), (pos, a)]
    | .lam _ t b _ | .forallE _ t b _ => #[(.typePos, t), (pos, b)]
    | .letE _ t v b _ => #[(.typePos, t), (pos, v), (pos, b)]
    | .proj _ _ b => #[(pos, b)]
    | _ => #[]
  let mut children := #[]
  for (childPos, child) in inputs do
    if let some i ← summariseExpr env childPos child then children := children.push i
  let ownContent := match e with
    | .const n _ => inProtected env n && !env.isProjectionFn n &&
        (env.find? n).any (fun info => match info with
          | .defnInfo _ | .opaqueInfo _ | .thmInfo _ => true
          | _ => false)
    | _ => false
  let nodes := (← get).summary.nodes
  let pContent := ownContent || children.any (fun i => nodes[i]!.pContent)
  let declaredType := e.constName?.bind (fun n => (env.find? n).map (fun i => eraseLevels i.type))
  let node : SyntaxNode := ⟨e, eraseLevels e, pos, children, ← propLooking env e, pContent, declaredType⟩
  modify fun s => { s with
    summary.nodes := s.summary.nodes.push node
    indices := s.indices.insert (e, pos) nodes.size }
  return some nodes.size

private def summarise (env : Environment) (inputs : Array (Position × Expr)) (fuel : Nat) :
    CoreM Summary := do
  let action : SummaryM Unit := do
    for (pos, e) in inputs do
      if let some i ← summariseExpr env pos e then
        modify fun s => { s with summary.roots := s.summary.roots.push i }
  let (_, state) ← action.run { fuel }
  return state.summary

/-- Counts for the last query; visits count syntax scanned to create summaries,
while chargedVisits also counts traversal of reused summaries against the fuel. -/
structure ProvenanceCounters where
  summarisedConstants : Nat := 0
  visits : Nat := 0
  memoHits : Nat := 0
  chargedVisits : Nat := 0
  deriving Inhabited, Repr

-- Ordinary environment extensions are compilation-local and not serialized.
private initialize summaryCache : EnvExtension (Std.HashMap Name Summary) ←
  registerEnvExtension (pure {})
private initialize countersCache : EnvExtension ProvenanceCounters ←
  registerEnvExtension (pure {})

def getProvenanceCounters : CoreM ProvenanceCounters := do
  return countersCache.getState (← getEnv)

private structure WalkState where
  theoremName : Name
  statement : Expr
  decision : Expr
  summaries : Std.HashMap Name Summary := {}
  counters : ProvenanceCounters := {}
  visited : Std.HashSet Expr := {}
  walked : NameHashSet := {}
  queued : NameHashSet := {}
  pending : List (Name × Position × Name) := []
  forbidden : Bool := false
  unclassified : Option Unclassified := none
  incomplete : Bool := false
  exprFuel : Nat := provenanceExpressionFuel
  constFuel : Nat := provenanceConstantFuel

private abbrev WalkM := StateRefT WalkState CoreM

private def noteUnclassified (u : Unclassified) : WalkM Unit := do
  if (← get).unclassified |>.isNone then modify fun s => { s with unclassified := some u }

private def queue (n : Name) (pos : Position) (site : Name) : WalkM Unit := do
  let s ← get
  if s.queued.contains n then return
  if s.constFuel == 0 then modify fun s => { s with incomplete := true } else
    modify fun s => { s with queued := s.queued.insert n, pending := List.cons (n, pos, site) s.pending, constFuel := s.constFuel - 1 }

private def compareCanonical (a b : Expr) : Bool := eraseLevels a == eraseLevels b

private def visitSummary (env : Environment) (origin : Name) (summary : Summary) : WalkM Unit := do
  let statement := (← get).statement
  let mut containsStatement : Array Bool := #[]
  for node in summary.nodes do
    containsStatement := containsStatement.push (node.canonical == statement ||
      node.children.any (fun i => containsStatement[i]!))
  if summary.incomplete then modify fun s => { s with incomplete := true }
  let mut pending := summary.roots.toList
  while !(← get).forbidden do
    let some index := pending.head? | break
    pending := pending.tail!
    if (← get).exprFuel == 0 then
      modify fun s => { s with incomplete := true }
      break
    modify fun s => { s with exprFuel := s.exprFuel - 1 }
    let node := summary.nodes[index]!
    let e := node.expr
    if (← get).visited.contains e then continue
    modify fun s => { s with visited := s.visited.insert e }
    let dataPos := node.position == .dataPos
    let checkU (x : SyntaxNode) : WalkM Unit := do
      if dataPos && x.prop && closed x.expr && x.pContent then
        noteUnclassified (Unclassified.mk "closed_decision"
          (x.expr.getAppFn.constName?.getD `closed_decision) "protected:D5" origin)
    if dataPos && closed e && containsStatement[index]! && node.canonical != statement then
      noteUnclassified (Unclassified.mk "statement_subterm"
        (e.getAppFn.constName?.getD `statement_subterm) "protected:current" origin)
    checkU node
    match e with
    | .const n _ =>
      let info := env.find? n
      modify fun s => { s with walked := s.walked.insert n }
      if n == (← get).theoremName then modify fun s => { s with forbidden := true }
      if provenanceJudgeAPIs.contains n || generatedAddress n || info.any judgePayload then
        modify fun s => { s with forbidden := true }
      if dataPos && n.getRoot == `Classical then
        noteUnclassified (Unclassified.mk "classical_choice" n "external:Classical" origin)
      if dataPos && !inProtected env n then
        if let some i := info then
          if !Lean.Meta.isInstanceCore env n then
            if let some h := resultHead i.type then
              if decisionFamily.contains h && !listedProducers.contains n then
                noteUnclassified (Unclassified.mk "unlisted_decision_producer" n (namespaceLabel env n) origin)
      if let some type := node.declaredType then
        if type == (← get).statement || type == (← get).decision then
          modify fun s => { s with forbidden := true }
        if inProtected env n && !(← get).queued.contains n then queue n node.position origin
      else modify fun s => { s with incomplete := true }
    | .app _ _ =>
      let args := e.getAppArgs
      if let .const head _ := e.getAppFn then
        if (head == ``Decidable.isTrue || head == ``Decidable.isFalse) && args.size > 0 then
          if compareCanonical args[0]! (← get).statement then modify fun s => { s with forbidden := true }
    | .lam _ t _ _ | .forallE _ t _ _ | .letE _ t _ _ _ =>
      let exactType := compareCanonical t (← get).statement || compareCanonical t (← get).decision
      if exactType then
        modify fun s => { s with forbidden := true }
      if let some typeIndex := node.children[0]? then
        if !exactType && containsStatement[typeIndex]! then
          noteUnclassified (Unclassified.mk "statement_mentioning_type"
            (t.getAppFn.constName?.getD `statement_mentioning_type) "protected:current" origin)
      if let some typeIndex := node.children[0]? then checkU summary.nodes[typeIndex]!
    | .proj n _ _ =>
      if provenanceJudgeAPIs.contains n || generatedAddress n || (env.find? n).any judgePayload then
        modify fun s => { s with forbidden := true }
    | .mvar _ => modify fun s => { s with incomplete := true }
    | _ => pure ()
    pending := node.children.toList ++ pending

private def visit (env : Environment) (pos : Position) (origin : Name) (e : Expr) : WalkM Unit := do
  let summary ← summarise env #[(pos, e)] (← get).exprFuel
  modify fun s => { s with counters.visits := s.counters.visits + summary.visits }
  visitSummary env origin summary

private def process (env : Environment) : WalkM Unit := do
  while !(← get).forbidden do
    let some (n, _, _) := (← get).pending.head? | break
    modify fun s => { s with pending := s.pending.tail! }
    if (← get).exprFuel == 0 then
      modify fun s => { s with incomplete := true }
      break
    let some info := env.find? n | modify fun s => { s with incomplete := true }; continue
    let summary ← if let some cached := (← get).summaries[n]? then do
        modify fun s => { s with counters.memoHits := s.counters.memoHits + 1 }
        pure cached
      else do
        let summary ← if let some value := info.value? (allowOpaque := true) then
            let valuePos := match info with | .thmInfo _ => .proofPos | _ => .dataPos
            summarise env #[(.typePos, info.type), (valuePos, value)] (← get).exprFuel
          else pure { incomplete := !isCtorOrInductive env n &&
            !#[`propext, `Classical.choice, `Quot.sound].contains n }
        modify fun s => { s with
          counters.summarisedConstants := s.counters.summarisedConstants + 1
          counters.visits := s.counters.visits + summary.visits }
        if !summary.incomplete then
          modify fun s => { s with summaries := s.summaries.insert n summary }
        pure summary
    visitSummary env n summary

private structure WalkResult where
  forbidden : Bool
  unclassified : Option Unclassified
  incomplete : Bool
  walked : Array String

private def collectReadout (env : Environment) (theoremName : Name) (readout : Expr) : CoreM WalkResult := do
  let some theoremInfo := env.find? theoremName | return { forbidden := false, unclassified := none, incomplete := true, walked := #[] }
  let statement := eraseLevels theoremInfo.type
  let decision := mkApp (mkConst ``Decidable) statement
  let computation : WalkM Unit := do
    visit env .dataPos (readout.getAppFn.constName?.getD theoremName) readout
    process env
  let (_, state) ← computation.run {
    theoremName, statement, decision, summaries := summaryCache.getState env }
  let counters := { state.counters with chargedVisits := provenanceExpressionFuel - state.exprFuel }
  modifyEnv (summaryCache.setState · state.summaries)
  modifyEnv (countersCache.setState · counters)
  trace[InformationProvenance.check]
    "theorem={theoremName} P_constants_summarised={counters.summarisedConstants} visits={counters.visits} memo_hits={counters.memoHits} charged_visits={counters.chargedVisits}"
  let names := state.walked.toArray.map Name.toString |>.qsort (· < ·)
  return (WalkResult.mk state.forbidden state.unclassified state.incomplete names)

private def safeCollect (env : Environment) (theoremName : Name) (readout : Expr) : CoreM WalkResult :=
  tryCatchRuntimeEx (collectReadout env theoremName readout)
    (fun _ => pure { forbidden := false, unclassified := none, incomplete := true, walked := #[] })

private def readoutClosureCurrent (theoremName : Name) (readout : Expr) : CoreM (Bool × Option (Array String)) := do
  let env ← getEnv
  let r ← safeCollect env theoremName readout
  if r.forbidden || r.unclassified.isSome then return (true, some r.walked)
  if r.incomplete then return (false, none)
  return (false, some r.walked)

def readoutClosure (env : Environment) (theoremName : Name) (readout : Expr) : CoreM (Bool × Option (Array String)) :=
  withEnv env (readoutClosureCurrent theoremName readout)

private def unclassifiedJson (u : Unclassified) (walked : Array String) : Json :=
  Json.mkObj [
    ("class", Json.str u.className), ("first", Json.str u.firstName.toString),
    ("namespace", Json.str u.namespaceName), ("site", Json.str u.siteName.toString),
    ("walked", Json.arr (walked.map Json.str))]

def provenanceErrorCurrent (root catalog theoremName realization : Name) : CoreM (Option String) := do
  let env ← getEnv
  let readout := readoutFamily env realization
  let address := readout.bind (·.getAppFn.constName?) |>.getD realization
  let result ← match readout with
    | some e => safeCollect env theoremName e
    | none => pure { forbidden := false, unclassified := none, incomplete := true, walked := #[] }
  if !result.forbidden && result.unclassified.isNone && !result.incomplete then return none
  let reason := if result.forbidden then "forbidden_dependency"
    else if result.unclassified.isSome then "unclassified_form" else "incomplete_closure"
  let payload := if result.forbidden then Json.arr (result.walked.map Json.str)
    else if let some u := result.unclassified then unclassifiedJson u result.walked
    else Json.null
  return some s!"IE-C050 ClosedTruthReadout key={root}/{catalog}/{theoremName} readout={address} reason={reason} provenance={payload.compress}"

def provenanceError (env : Environment) (root catalog theoremName realization : Name) : CoreM (Option String) :=
  withEnv env (provenanceErrorCurrent root catalog theoremName realization)

end LeanInformationAudit.RegistrationGates
