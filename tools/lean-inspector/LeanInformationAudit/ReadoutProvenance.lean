import LeanInformationAudit.ReadoutFamily
import Lean.Structure

namespace LeanInformationAudit.RegistrationGates
open Lean

-- §10.1 budget record: relation-derived safety limit; owner=governance lane;
-- date=2026-09-13; basis=the existing 4100-link closure-exhaustion fixture;
-- exit condition=the supported closure corpus or pinned Lean version changes,
-- then rerun that fixture and register a new relation before changing this cap.
def provenanceConstantFuel : Nat := 4096
-- Completed InformationRoot and TemplateShadow profiles, Lean 4.33.0,
-- 2026-09-13: the context-selection query consumed 8,034,836 work units;
-- InformationRoot's largest query consumed 3,247,448.
private def provenanceReferenceQueryWork : Nat := 8034836
-- §10.1 budget record: capacity-derived limit; owner=governance lane;
-- date=2026-09-13; basis=the measured 8,034,836 work-unit maximum plus 25%
-- policy headroom, rounded upward; exit condition=the pinned Lean version,
-- supported readout corpus, or measurement profile changes, then remeasure.
def provenanceExpressionFuel : Nat := (5 * provenanceReferenceQueryWork + 3) / 4
register_option provenanceExpressionLimit : Nat := {
  defValue := provenanceExpressionFuel
  descr := "Readout work limit, capped by the production expression policy" }

-- §10.1 budget record: policy-override safety limit; owner=governance lane;
-- date=2026-09-13; basis=bounded raw Lean allocation per definitional comparison;
-- exit condition=the supported readout corpus or pinned Lean version changes,
-- then rerun real heartbeat-exhaustion and boundary fixtures. This is exempt
-- from capacity derivation because it is a correctness fail-closed limit.
def provenanceDefEqHeartbeats : Nat := 20000

register_option provenanceDefEqLimit : Nat := {
  defValue := provenanceDefEqHeartbeats
  descr := "Maximum raw heartbeats for a readout type/defeq query; zero fails closed" }

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

private def generatedAddress : Name → Bool
  | .str parent suffix =>
      #["__information_unit", "__primitive_realization", "__structural_unit",
        "__structural_realization", "__information_catalog", "__lowers_escape",
        "__escape_enriched", "__trivial_in_catalog", "__state_enumeration",
        "__information_registration_diagnostic", "__kernel_projection"].contains suffix ||
      suffix.startsWith "__catalog_" || suffix.startsWith "__system_catalog_" || generatedAddress parent
  | .num parent _ => generatedAddress parent
  | .anonymous => false

private def judgePayloadType (name : Name) : Bool :=
  #[
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
      `LeanInformationAudit.TruncationCertification].contains name

private def judgePayload (info : ConstantInfo) : Bool :=
  match info with
  | .ctorInfo ctor => judgePayloadType ctor.induct
  | _ => false

private def closed (e : Expr) : Bool := !e.hasLooseBVars && !e.hasFVar && !e.hasMVar

private def decisionFamily : Array Name := #[
  ``Decidable, ``DecidablePred, ``DecidableRel, ``DecidableEq,
  ``DecidableLE, ``DecidableLT]

private def listedProducers : Array Name := #[
  ``Decidable.isTrue, ``Decidable.isFalse, ``decidable_of_iff, ``decidable_of_iff',
  ``decidable_of_bool, ``decidable_of_decidable_of_iff, ``decidable_of_decidable_of_eq,
  ``decEq, ``Nat.decEq, ``Nat.decLt, ``Nat.decLe, ``Bool.decEq,
  ``instDecidableEqOfLawfulBEq, ``inferInstance, `Equiv.decidableEq]

private def isCtorOrInductive (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | some (.inductInfo _) | some (.ctorInfo _) | some (.recInfo _) | some (.quotInfo _) => true
  | _ => false

private def moduleName (env : Environment) (n : Name) : Name :=
  (env.getModuleIdxFor? n).map (env.header.modules[·.toNat]!.module) |>.getD env.header.mainModule

-- Lean orders imported modules after their dependencies. Protect every module
-- importing a protected module, regardless of its library or declaration names.
-- Missing import metadata is protected too; it cannot justify an external leaf.
private def classifyModules (env : Environment) : Std.HashMap Name Bool := Id.run do
  let mut classes : Std.HashMap Name Bool := {}
  for index in [:env.header.modules.size] do
    let name := env.header.modules[index]!.module
    let inherited := match env.header.moduleData[index]? with
      | none => true
      | some data => data.imports.any (fun i => classes[i.module]?.getD true)
    classes := classes.insert name
      (name.getRoot == `D5 || name.getRoot == `LeanInformationAudit || inherited)
  return classes

private initialize moduleScopeCache : EnvExtension (Option (Std.HashMap Name Bool)) ←
  registerEnvExtension (pure none)

private def inProtected (env : Environment) (n : Name) : Bool :=
  if (env.getModuleIdxFor? n).isNone then true else
    let m := moduleName env n
    m == env.header.mainModule ||
      ((moduleScopeCache.getState env).bind (·[m]?)).getD true

private def namespaceLabel (env : Environment) (n : Name) : String :=
  if inProtected env n then
    if moduleName env n == env.header.mainModule then "protected:current"
    else if (moduleName env n).getRoot == `LeanInformationAudit then "protected:judge" else "protected:D5"
  else if n.getRoot == `Classical then "external:Classical"
  else "external:other"

private structure Unclassified where
  className : String
  firstName : Name
  namespaceName : String
  siteName : Name

private inductive TypeClassification where
  /-- The only verdicts accepted by the walker: a positive allowlist result,
  statement mention, direct forbidden dependency, or an explicit failure to
  classify.  Callers must handle every constructor. -/
  | allowlisted
  | statementMention
  | forbidden
  | unclassified
  deriving Inhabited

private inductive Position where | dataPos | proofPos | typePos
  deriving BEq, Hashable, Inhabited

-- These summaries contain syntax and its fixed classifications, never a verdict
-- for a registered statement. Child indices precede their parents, so subterm
-- membership is recomputed by a linear fold without walking Expr trees again.
private structure SyntaxNode where
  expr : Expr
  context : Array Expr
  position : Position
  children : Array Nat
  pContent : Bool
  declaredType : Option Expr
  appHead : Expr
  firstArg : Option Expr
  deriving Inhabited

private structure Summary where
  nodes : Array SyntaxNode := #[]
  roots : Array Nat := #[]
  visits : Nat := 0
  constructionWork : Nat := 0
  incomplete : Bool := false
  deriving Inhabited

private structure SummaryBuild where
  summary : Summary := {}
  indices : Std.HashMap (Expr × Position × Array Expr) Nat := {}
  fuel : Nat

private abbrev SummaryM := StateRefT SummaryBuild CoreM

-- Every construction reservation consumes this local budget.
-- The caller transfers constructionWork to its query's single debit point.
private def chargeConstruction (amount : Nat := 1) : SummaryM Bool := do
  let s ← get
  if amount > s.fuel then
    modify fun s => { s with summary.incomplete := true }
    return false
  -- Retain the existing checkpoint cadence, including for weighted operations.
  if s.summary.constructionWork / 256 != (s.summary.constructionWork + amount) / 256 then
    Core.checkMaxHeartbeats "readout summary construction"
  modify fun s => { s with
    fuel := s.fuel - amount
    summary.constructionWork := s.summary.constructionWork + amount }
  return true

private partial def stripSummaryMData (e : Expr) : SummaryM (Option Expr) := do
  match e with
  | .mdata _ body =>
    unless ← chargeConstruction do return none
    stripSummaryMData body
  | _ => return some e

private partial def summariseExpr (env : Environment) (pos : Position) (raw : Expr)
    (context : Array Expr := #[]) : SummaryM (Option Nat) := do
  unless ← chargeConstruction do return none
  modify fun s => { s with summary.visits := s.summary.visits + 1 }
  let some e ← stripSummaryMData raw | return none
  let keyContext := if e.hasLooseBVars then context else #[]
  -- Array hashing and a matching-key comparison each inspect context entries.
  unless ← chargeConstruction (keyContext.size + keyContext.size) do return none
  if let some i := (← get).indices[(e, pos, keyContext)]? then return some i
  let binder := match e with | .lam .. | .forallE .. | .letE .. => true | _ => false
  if binder then
    unless ← chargeConstruction (context.size + 1) do return none
  let inputs : Array (Position × Expr × Array Expr) := match e with
    | .app f a => #[(pos, f, context), (pos, a, context)]
    | .lam _ t b _ | .forallE _ t b _ => #[(.typePos, t, context), (pos, b, context.push e)]
    | .letE _ t v b _ => #[(.typePos, t, context), (pos, v, context), (pos, b, context.push e)]
    | .proj _ _ b => #[(pos, b, context)]
    | _ => #[]
  let mut children := #[]
  for (childPos, child, childContext) in inputs do
    let some i ← summariseExpr env childPos child childContext | return none
    children := children.push i
  let ownContent := match e with
    | .const n _ => inProtected env n && !env.isProjectionFn n &&
        (env.find? n).any (fun info => match info with
          | .defnInfo _ | .opaqueInfo _ | .thmInfo _ => true
          | _ => false)
    | _ => false
  let nodes := (← get).summary.nodes
  let pContent := ownContent || children.any (fun i => nodes[i]!.pContent)
  let declaredType := e.constName?.bind (fun n => (env.find? n).map
    (·.instantiateTypeLevelParams e.constLevels!))
  if (← get).summary.incomplete then return none
  let (appHead, firstArg) := match e with
    | .app f arg =>
      let fn := nodes[children[0]!]!
      (if f.isApp then fn.appHead else f,
        if f.isApp then fn.firstArg else some arg)
    | _ => (e, none)
  let node : SyntaxNode := {
    expr := e, context := keyContext, position := pos, children, pContent,
    declaredType, appHead, firstArg }
  -- Retain only the index across insertion. Keeping the old array alive for a
  -- later size read would force Array.push to copy every preceding node.
  let index := nodes.size
  -- A second key hash is required by insertion; the node write is one dispatch.
  unless ← chargeConstruction (keyContext.size + 1) do return none
  modify fun s => { s with
    summary.nodes := s.summary.nodes.push node
    indices := s.indices.insert (e, pos, keyContext) index }
  return some index

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
  /-- Nodes of a cached summary rechecked against the current statement. -/
  recheckedNodes : Nat := 0
  /-- Child edges (application/binder spines) inspected while rechecking. -/
  spineArguments : Nat := 0
  /-- Bounded comparison/classification requests, including memo hits. -/
  canonicalizations : Nat := 0
  constructionWork : Nat := 0
  traversalWork : Nat := 0
  dispatchWork : Nat := 0
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
  visited : Std.HashSet (Expr × Position × Array Expr) := {}
  walked : NameHashSet := {}
  queued : NameHashSet := {}
  pending : List Name := []
  typeObligations : List (Expr × Array Expr × Bool × Name × Name) := []
  appObligations : List (Expr × Array Expr × Bool × Name) := []
  comparisons : Std.HashMap (Expr × Expr) Bool := {}
  typeChecks : Std.HashMap (Expr × Array Expr × Bool) TypeClassification := {}
  forbidden : Bool := false
  unclassified : Option Unclassified := none
  incomplete : Bool := false
  weights : Std.HashMap Expr Nat := {}
  levelWeights : Std.HashMap Level Nat := {}
  applications : Std.HashMap Expr (Expr × Array Expr) := {}
  mentionsCache : Std.HashMap Expr Bool := {}
  cleanTypes : Std.HashSet (Expr × Bool) := {}
  cleanKinds : Std.HashSet Expr := {}
  dataFunctionTypes : Std.HashSet Expr := {}
  binderContexts : Std.HashMap (Array Expr) (LocalContext × LocalInstances × Array Expr) := {}
  exprFuel : Nat := provenanceExpressionFuel
  constFuel : Nat := provenanceConstantFuel

private abbrev WalkM := StateRefT WalkState MetaM

-- Every pass over a summary is charged to the same per-query expression fuel
-- as syntax construction.  In particular, a cache hit must not make the
-- statement fold free: otherwise a large cached summary could be replayed
-- without consuming the bound that protects the allowlist check.
private def chargeSummaryWork (update : ProvenanceCounters → ProvenanceCounters) (amount : Nat := 1) :
    WalkM Bool := do
  if amount > (← get).exprFuel then
    modify fun s => { s with incomplete := true }
    return false
  modify fun s => { s with
    exprFuel := s.exprFuel - amount
    counters := update s.counters }
  return true

private def chargeTraversal (amount : Nat := 1) : WalkM Bool :=
  chargeSummaryWork (fun c => { c with traversalWork := c.traversalWork + amount }) amount

private partial def levelWeight (level : Level) : WalkM (Option Nat) := do
  unless ← chargeTraversal do return none
  if let some n := (← get).levelWeights[level]? then return some n
  let children := match level with
    | .succ a => #[a] | .max a b | .imax a b => #[a, b] | _ => #[]
  let mut size := 1
  for child in children do
    let some n ← levelWeight child | return none
    size := min (provenanceExpressionFuel + 1) (size + n)
  modify fun s => { s with levelWeights := s.levelWeights.insert level size }
  return some size

-- Computing a weight consumes fuel too. Cached Expr hashes and occurrence flags
-- are constant-time; weights cap at the query budget before arithmetic grows.
private partial def expressionWeight (e : Expr) : WalkM (Option Nat) := do
  unless ← chargeTraversal do return none
  if let some n := (← get).weights[e]? then return some n
  let children := match e with
    | .app f a => #[f, a]
    | .lam _ t b _ | .forallE _ t b _ => #[t, b]
    | .letE _ t v b _ => #[t, v, b]
    | .mdata _ b | .proj _ _ b => #[b]
    | _ => #[]
  let mut weight := 1
  for child in children do
    let some n ← expressionWeight child | return none
    weight := min (provenanceExpressionFuel + 1) (weight + n)
  let levels := match e with | .const _ ls => ls | .sort l => [l] | _ => []
  for level in levels do
    let some n ← levelWeight level | return none
    weight := min (provenanceExpressionFuel + 1) (weight + n)
  modify fun s => { s with weights := s.weights.insert e weight }
  return some weight

private def chargeExpression (e : Expr) : WalkM Bool := do
  let some size ← expressionWeight e | return false
  chargeTraversal size

private def substitute (e : Expr) (locals : Array Expr) : WalkM (Option Expr) := do
  if !e.hasLooseBVars then return some e
  unless ← chargeExpression e do return none
  unless ← chargeTraversal locals.size do return none
  return some (e.instantiateRev locals)

private def substituteLevels (info : ConstantInfo) (levels : List Level) : WalkM (Option Expr) := do
  let type := info.instantiateTypeLevelParams levels
  if !type.hasLevelParam then return some type
  let some size ← expressionWeight type | return none
  let mut factor := 1
  for _ in info.levelParams do
    unless ← chargeTraversal do return none
    factor := factor + 1
  unless ← chargeTraversal (size * factor) do return none
  return some type

private def applicationParts (e : Expr) : WalkM (Option (Expr × Array Expr)) := do
  unless ← chargeTraversal do return none
  if let some cached := (← get).applications[e]? then return some cached
  let mut head := e
  let mut args := []
  let mut arity := 0
  repeat
    unless ← chargeTraversal do return none
    match head with
    | .app f a => head := f; args := a :: args; arity := arity + 1
    | _ => break
  unless ← chargeTraversal arity do return none
  let result := (head, args.toArray)
  modify fun s => { s with applications := s.applications.insert e result }
  return some result

private def resultHead (raw : Expr) : WalkM (Option Name) := do
  let mut e := raw
  repeat
    unless ← chargeTraversal do return none
    match e with
    | .forallE _ _ body _ | .mdata _ body => e := body
    | _ => break
  let some (head, _) ← applicationParts e | return none
  return head.constName?

private def noteUnclassified (u : Unclassified) : WalkM Unit := do
  if (← get).unclassified |>.isNone then modify fun s => { s with unclassified := some u }

private def queue (n : Name) : WalkM Unit := do
  let s ← get
  if s.queued.contains n then return
  if s.constFuel == 0 then modify fun s => { s with incomplete := true } else
    modify fun s => { s with queued := s.queued.insert n, pending := List.cons n s.pending, constFuel := s.constFuel - 1 }

-- No failed or exhausted Meta query can supply a positive allowlist verdict.
-- Open subterms are checked structurally below, without inventing a context
-- for their loose bound variables. Closed aliases use Lean's defeq relation.
private def compareCanonical (a b : Expr) : WalkM Bool := do
  unless ← chargeSummaryWork (fun c => { c with canonicalizations := c.canonicalizations + 1 }) do
    return false
  if let some result := (← get).comparisons[(a, b)]? then return result
  if a.hasLooseBVars || b.hasLooseBVars then return false
  let budget := min provenanceDefEqHeartbeats (provenanceDefEqLimit.get (← getOptions))
  if budget == 0 then
    noteUnclassified ⟨"defeq_budget", `defeq, "unclassified", `defeq⟩
    return false
  let result ← (tryCatchRuntimeEx (do
    let start ← IO.getNumHeartbeats
    controlAt CoreM fun runInBase => withReader (fun ctx : Core.Context =>
      { ctx with initHeartbeats := start, maxHeartbeats := budget }) do
      -- Defeq is a typed relation. Comparing a large data computation directly
      -- with a proposition needlessly reduces the data before rejecting it.
      let result ← runInBase do
        unless ← Meta.isDefEq (← Meta.inferType a) (← Meta.inferType b) do return false
        Meta.isDefEq a b
      Core.checkMaxHeartbeats "readout definitional comparison"
      pure (some result)) (fun _ => pure none) : MetaM (Option Bool))
  match result with
  | some result =>
    modify fun s => { s with comparisons := s.comparisons.insert (a, b) result }
    return result
  | none =>
    noteUnclassified ⟨"defeq_budget", `defeq, "unclassified", `defeq⟩
    return false

-- Preserve constant provenance before reduction, including constants discovered
-- only in a constructor field's type. Direct forbidden sources take precedence.
private def directConstant (env : Environment) (n : Name) : WalkM Unit := do
  let payload := (env.find? n).any judgePayload ||
    ((env.getProjectionFnInfo? n).bind (fun p => env.find? p.ctorName)).any judgePayload
  if n == (← get).theoremName || provenanceJudgeAPIs.contains n || generatedAddress n || payload then
    modify fun s => { s with forbidden := true, walked := s.walked.insert n }

private def directProjection (env : Environment) (n : Name) : WalkM Unit := do
  if provenanceJudgeAPIs.contains n || generatedAddress n || judgePayloadType n then
    modify fun s => { s with forbidden := true, walked := s.walked.insert n }

private def typeConstant (env : Environment) (n : Name) (levels : List Level := []) : WalkM Unit := do
  directConstant env n
  if let some info := env.find? n then
    let type := info.instantiateTypeLevelParams levels
    -- Nested constants contribute their instantiated declared type to the same
    -- obligation queue as summary roots; process sends every entry through the
    -- single classifyType funnel.
    let origin := (← get).theoremName
    modify fun s => { s with typeObligations :=
      (type, #[], !info.hasValue (allowOpaque := true), n, origin) :: s.typeObligations }
    if inProtected env n then queue n
  else modify fun s => { s with incomplete := true }

-- Positive policies for instance types whose parameters are still checked by
-- the same structural fold. An unfamiliar class never inherits external-leaf
-- status from its module. In particular proof-carrying user classes are unclassified.
private def listedTypeClasses : Array Name := #[
  ``Decidable, ``OfNat, ``Inhabited, ``Subsingleton, ``Nonempty, ``BEq, ``LawfulBEq,
  `Fintype, `Finite, `NeZero,
  -- Collection and relation interfaces used by the frozen readout corpus.
  ``Membership, ``GetElem?, ``Setoid, `SetLike, ``Singleton, ``Insert,
  ``Std.Associative, ``Std.Commutative,
  -- Scalar operator interfaces: their actual type parameters are checked too.
  ``Zero, ``One, ``Add, ``HAdd, ``Mul, ``HMul, ``Sub, ``HSub, ``Div, ``HDiv,
  ``Neg, ``Inv, ``Pow, ``HPow, ``Mod, ``HMod, ``LT, ``LE, ``NatPow]

-- These families expose their proof fields in type-valued arguments. Exists
-- is intentionally classified through its constructor and predicate application.
private def listedPropositions : Array Name := #[
  ``Eq, ``HEq, ``True, ``False, ``And, ``Or, ``Iff, ``Nat.le]

private def boundedMeta (action : MetaM α) : WalkM (Option α) := do
  unless ← chargeSummaryWork (fun c => { c with canonicalizations := c.canonicalizations + 1 }) do
    return none
  let budget := min provenanceDefEqHeartbeats (provenanceDefEqLimit.get (← getOptions))
  if budget == 0 then
    noteUnclassified ⟨"defeq_budget", `defeq, "unclassified", `defeq⟩
    return none
  let result ← (tryCatchRuntimeEx (do
    let start ← IO.getNumHeartbeats
    controlAt CoreM fun runInBase => withReader (fun ctx : Core.Context =>
      { ctx with initHeartbeats := start, maxHeartbeats := budget }) do
      let result ← runInBase action
      Core.checkMaxHeartbeats "readout type classification"
      pure (some result)) (fun _ => pure none) : MetaM (Option α))
  if result.isNone then
    noteUnclassified ⟨"defeq_budget", `defeq, "unclassified", `defeq⟩
  return result

private def appliedValueType (e : Expr) : WalkM (Option Expr) := do
  let some type ← boundedMeta (Meta.inferType e) | return none
  return some type

-- Projection syntax does not carry a level list. Recover the projection
-- declaration from its structure/index and instantiate it with the universe
-- levels of the occurrence's receiver type before sending it to classifyType.
private def projectionDeclaredType (env : Environment) (e : Expr) :
    WalkM (Option (Name × Expr)) := do
  let .proj structName index receiver := e | return none
  let some structureInfo := getStructureInfo? env structName | return none
  let some projectionName := structureInfo.getProjFn? index | return none
  let some projectionInfo := env.find? projectionName | return none
  let some receiverType ← boundedMeta (Meta.inferType receiver) | return none
  let some receiverType ← boundedMeta (Meta.whnf receiverType) | return none
  let levels := receiverType.getAppFn.constLevels!
  return some (projectionName, projectionInfo.instantiateTypeLevelParams levels)

private partial def buildBinderContext (context : Array Expr) (k : Array Expr → WalkM α)
    (index : Nat := 0) (locals : Array Expr := #[]) : WalkM (Option α) := do
  unless ← chargeTraversal do return none
  if h : index < context.size then
    -- Parent contexts retain their local arrays while the body runs, so pushing
    -- the next local can copy the prefix as well as append one entry.
    unless ← chargeTraversal (locals.size + 1) do return none
    let next := fun locals => buildBinderContext context k (index + 1) locals
    match context[index] with
    | .lam n t _ bi | .forallE n t _ bi =>
      let some t ← substitute t locals | return none
      Meta.withLocalDecl n bi t fun x => next (locals.push x)
    | .letE n t v _ nd =>
      let some t ← substitute t locals | return none
      let some v ← substitute v locals | return none
      Meta.withLetDecl n t v (fun x => next (locals.push x)) (nondep := nd)
    | _ => return none
  else return some (← k locals)

-- Reuse reconstructed binders only when the original parent context is empty.
-- Restoring both locals and local instances preserves their actual types and
-- stable fvar identities; nested callers retain their existing parent context.
private def inBinderContext (context : Array Expr) (k : Array Expr → WalkM α) :
    WalkM (Option α) := do
  if context.isEmpty then return some (← k #[])
  if !(← getLCtx).isEmpty then return ← buildBinderContext context k
  unless ← chargeTraversal (2 * context.size + 1) do return none
  if let some (lctx, instances, locals) := (← get).binderContexts[context]? then
    return some (← Meta.withLCtx lctx instances (k locals))
  unless ← chargeTraversal context.size do return none
  buildBinderContext context fun locals => do
    let lctx ← getLCtx
    let instances ← Meta.getLocalInstances
    modify fun s => { s with binderContexts := s.binderContexts.insert context (lctx, instances, locals) }
    k locals

-- The syntax scan checks TERM occurrences inside types. They are not themselves
-- assumed to be types (e.g. Classical constants on either side of an equality).
private partial def typeMentions (env : Environment) (e : Expr) : WalkM Bool := do
  unless ← chargeSummaryWork (fun c => { c with recheckedNodes := c.recheckedNodes + 1 }) do
    return false
  if let some cached := (← get).mentionsCache[e]? then return cached
  let mut result ← compareCanonical e (← get).statement
  if !result then
    result ← match e with
    | .const n levels => typeConstant env n levels; pure false
    | .app f a =>
      let _ ← appliedValueType e
      pure ((← typeMentions env f) || (← typeMentions env a))
    | .lam n t b bi | .forallE n t b bi =>
      let domain ← typeMentions env t
      let body ← Meta.withLocalDecl n bi t fun x => do
        let some body ← substitute b #[x] | return false
        typeMentions env body
      pure (domain || body)
    | .letE n t v b nd =>
      let domain ← typeMentions env t
      let value ← typeMentions env v
      let body ← Meta.withLetDecl n t v (fun x => do
        let some body ← substitute b #[x] | return false
        typeMentions env body) (nondep := nd)
      pure (domain || value || body)
    | .mdata _ b => typeMentions env b
    | .proj n _ b => directProjection env n; typeMentions env b
    | _ => pure false
  modify fun s => { s with mentionsCache := s.mentionsCache.insert e result }
  return result

-- Local projections are neutral families just like local function variables.
-- An opaque or closed receiver cannot use this rule: its projected type still
-- needs reduction or another positive classification.
private partial def localNeutral (e : Expr) : WalkM Bool := do
  unless ← chargeTraversal do return false
  match e with
  | .fvar id =>
    if let some value := ((← getLCtx).get! id).value? (allowNondep := true) then localNeutral value
    else return true
  | .app f _ | .proj _ _ f | .mdata _ f => localNeutral f
  | _ => return false

-- Every binder origin has a domain obligation: inputType and family telescopes
-- combine it with their body verdict, while summary binders enqueue it. A plain
-- binder receiver has that same immutable domain; applications/projections can
-- specialize it and must keep their separate receiver-type check.
private partial def binderReceiver (e : Expr) : WalkM Bool := do
  unless ← chargeTraversal do return false
  match e with
  | .fvar id =>
    if let some value := ((← getLCtx).get! id).value? (allowNondep := true) then binderReceiver value
    else return true
  | .mdata _ body => binderReceiver body
  | _ => return false

mutual
-- Constructor scans quantify every index. Recursion may reuse that family
-- obligation only after checking current arguments and identical parameters.
private partial def inputType (env : Environment) (type : Expr)
    (active : Array Expr := #[]) (checkResult : Bool := true) : WalkM (Bool × Bool) := do
  unless ← chargeSummaryWork (fun c => { c with recheckedNodes := c.recheckedNodes + 1 }) do
    return (false, true)
  if type.hasLooseBVars || type.hasMVar || type.hasLevelMVar then return (false, true)
  let key := (type, checkResult)
  if (← get).cleanTypes.contains key then return (false, false)
  let classify : WalkM (Bool × Bool) := do
    -- A family enters active only after its kind and every actual argument have
    -- been checked. An identical application therefore needs no second argument
    -- check. Different indices/aliases still take the full classifier below.
    for previous in active do
      unless ← chargeTraversal do return (false, true)
      if hash previous == hash type then
        unless ← chargeExpression previous do return (false, true)
        unless ← chargeExpression type do return (false, true)
        if previous == type then return (false, false)
    -- A telescope is already traversed domain by domain by this classifier.
    -- Rescanning each complete suffix with typeMentions would duplicate its
    -- binder reconstruction and comparisons at every level.
    if let .forallE n domain body bi := type then
      let exact ← compareCanonical type (← get).statement
      let decision ← compareCanonical type (← get).decision
      let (dm, du) ← inputType env domain active
      let (bm, bu) ← Meta.withLocalDecl n bi domain fun x => do
        let some body ← substitute body #[x] | return (false, true)
        inputType env body active checkResult
      return (exact || decision || dm || bm, du || bu)
    let mut mentions ← typeMentions env type
    if ← compareCanonical type (← get).decision then mentions := true
    let some reduced ← boundedMeta (Meta.whnf type) | return (mentions, true)
    mentions := (← typeMentions env reduced) || mentions
    match reduced with
    | .forallE n domain body bi =>
      let (dm, du) ← inputType env domain active
      let (bm, bu) ← Meta.withLocalDecl n bi domain fun x =>
        do
          let some body ← substitute body #[x] | return (false, true)
          inputType env body active checkResult
      return (mentions || dm || bm, du || bu)
    | .lam n domain body bi =>
      -- Type-valued lambda expressions are generated by dependent recursors
      -- (for example `Fin.casesOn` motives).  Inspect their domains and bodies
      -- through this same classifier instead of treating the lambda head as
      -- an unknown escape.
      let (dm, du) ← inputType env domain active
      let (bm, bu) ← Meta.withLocalDecl n bi domain fun x => do
        let some body ← substitute body #[x] | return (false, true)
        inputType env body active checkResult
      return (mentions || dm || bm, du || bu)
    | .letE n domain value body nd =>
      let (dm, du) ← inputType env domain active
      let (vm, vu) ← inputType env value active
      let (bm, bu) ← Meta.withLetDecl n domain value (fun x => do
        let some body ← substitute body #[x] | return (false, true)
        inputType env body active checkResult) (nondep := nd)
      return (mentions || dm || vm || bm, du || vu || bu)
    | .mdata _ body =>
      let (bm, bu) ← inputType env body active checkResult
      return (mentions || bm, bu)
    | _ =>
      if reduced.isSort then return (mentions, false)
      let some (head, args) ← applicationParts reduced | return (mentions, true)
      let mut unclassified := false
      for arg in args do
        let some argType ← boundedMeta (Meta.inferType arg) | return (mentions, true)
        if let some (am, au) ← typeFamilyArgument env arg argType active then
          mentions := mentions || am
          unclassified := unclassified || au
      -- A local type-family head is allowed only after its inferred type has
      -- itself passed the funnel.  This keeps local neutral syntax from being
      -- an unknown-tolerant escape hatch.
      if head.isFVar then
        let some neutralType ← appliedValueType reduced | return (mentions, true)
        let (fm, fu) ← inputType env neutralType active
        return (mentions || fm, unclassified || fu)
      if let .proj _ _ receiver := head then
        -- Projection heads have no level list in their syntax.  Classify both
        -- the actual receiver type and the projection's instantiated declared
        -- type before accepting the result.  This covers ordinary projections
        -- such as `LT.lt`, whose receiver is an instance constant rather than
        -- a local neutral, and keeps the nominal `checkResult=false` path
        -- inside the same funnel.
        let some receiverType ← appliedValueType receiver | return (mentions, true)
        let (rm, ru) ← inputType env receiverType active
        let some (_, projectionType) ← projectionDeclaredType env head |
          return (mentions || rm, true)
        let (pm, pu) ← inputType env projectionType active
        return (mentions || rm || pm, ru || pu || unclassified)
      let .const name levels := head | do
        -- Neutral type expressions have no declaration head to inspect.  Their
        -- inferred type is still an obligation: classify it before accepting
        -- the neutral expression, and fail closed if inference is unavailable.
        let some neutralType ← appliedValueType reduced | return (mentions, true)
        let (nm, nu) ← inputType env neutralType active
        return (mentions || nm, unclassified || nu)
      let some declaration := env.find? name | return (mentions, true)
      unless ← chargeTraversal do return (mentions, true)
      if !declaration.hasValue (allowOpaque := true) && !(← get).cleanKinds.contains head then
        -- Synthetic type heads obey the same declared-type obligation as
        -- constants in value summaries. Their closed kind is independent of
        -- the caller's recursive-family assumptions.
        let some kind ← substituteLevels declaration levels | return (mentions, true)
        let (km, ku) ← inputType env kind #[] false
        mentions := mentions || km
        unclassified := unclassified || ku
        let state ← get
        if !km && !ku && !state.incomplete && !state.forbidden && state.unclassified.isNone then
          unless ← chargeTraversal do return (mentions, true)
          modify fun s => { s with cleanKinds := s.cleanKinds.insert head }
      if Lean.isClass env name then
        return (mentions, unclassified || !listedTypeClasses.contains name)
      if listedPropositions.contains name then return (mentions, unclassified)
      -- Quotient carriers and lifted type families expose their relation or
      -- predicate to the same argument classifier; no predicate is a leaf.
      if let some (.quotInfo info) := env.find? name then
        if match info.kind with | .type | .lift => true | _ => false then
          return (mentions, unclassified)
      if let some (.recInfo _) := env.find? name then return (mentions, unclassified)
      if let some (.defnInfo _) := env.find? name then
        -- Expose the actual body of a stuck type computation. Matcher metadata
        -- grants no authority; every unfolded body re-enters the same classifier.
        let some unfolded? ← boundedMeta (withOptions (·.setBool `smartUnfolding false)
          (Meta.unfoldDefinition? reduced (ignoreTransparency := true))) | return (mentions, true)
        let some unfolded := unfolded? | return (mentions, true)
        let (um, uu) ← inputType env unfolded active
        return (mentions || um, unclassified || uu)
      let some (.inductInfo info) := env.find? name | return (mentions, true)
      -- A nominal result may be checked in a reduced context (`checkResult=false`),
      -- but its actual family arguments and head kind are still mandatory.  The
      -- flag only controls whether constructor fields are expanded below.
      if !checkResult then return (mentions, unclassified)
      for previous in active do
        let some (previousHead, previousArgs) ← applicationParts previous | return (mentions, true)
        unless ← chargeExpression previousHead do return (mentions, true)
        unless ← chargeExpression head do return (mentions, true)
        if previousHead == head then
          let mut sameParameters := true
          for index in [:info.numParams] do
            unless ← chargeTraversal do return (mentions, true)
            let some a := previousArgs[index]? | return (mentions, true)
            let some b := args[index]? | return (mentions, true)
            sameParameters := (← compareCanonical a b) && sameParameters
          if sameParameters then return (mentions, unclassified)
          -- Different parameters are a fresh obligation, as in nested products.
      for ctorName in info.ctors do
        let some ctor := env.find? ctorName | return (mentions, true)
        let some initialType ← substituteLevels ctor levels | return (mentions, true)
        let mut ctorType := initialType
        for arg in args[:info.numParams] do
          let .forallE _ _ body _ := ctorType | return (mentions, true)
          let some next ← substitute body #[arg] | return (mentions, true)
          ctorType := next
        unless ← chargeTraversal (active.size + 1) do return (mentions, true)
        let (cm, cu) ← inputType env ctorType (active.push reduced) false
        mentions := mentions || cm
        unclassified := unclassified || cu
      return (mentions, unclassified)

  let result ← classify
  -- Only an independent, completed check can seed the cache. Recursive cutoffs
  -- never publish a provisional verdict. A stored result is independent of any
  -- caller's active stack and remains valid throughout this statement query.
  -- Fvar identities are unique and their local declarations are immutable.
  let state ← get
  if active.isEmpty && !type.hasLooseBVars && !type.hasMVar && !type.hasLevelMVar &&
      !result.1 && !result.2 &&
      !state.incomplete && !state.forbidden && state.unclassified.isNone then
    unless ← chargeTraversal do return (false, true)
    modify fun s => { s with cleanTypes := s.cleanTypes.insert key }
  return result

-- Probe the inferred telescope first. Only functions ending in Sort supply
-- type families; ordinary data functions keep their term-provenance treatment.
private partial def typeFamilyArgument (env : Environment) (value type : Expr)
    (active : Array Expr) : WalkM (Option (Bool × Bool)) := do
  unless ← chargeTraversal do return some (false, true)
  if (← get).dataFunctionTypes.contains type then return none
  let inspect : WalkM (Option (Bool × Bool)) := do
    let some reduced ← boundedMeta (Meta.whnf type) | return some (false, true)
    match reduced with
    | .forallE n domain body bi =>
      let result ← Meta.withLocalDecl n bi domain fun x => do
        let some body ← substitute body #[x] | return some (false, true)
        unless ← chargeTraversal do return some (false, true)
        typeFamilyArgument env (mkApp value x) body active
      let some (bm, bu) := result | return none
      let (dm, du) ← inputType env domain active
      return some (dm || bm, du || bu)
    | .sort _ => return some (← inputType env value active)
    | _ => return none
  let result ← inspect
  -- A non-family telescope performs no domain/value classification, so this
  -- completed negative result is independent of recursive-family assumptions.
  if result.isNone && closed type then
    unless ← chargeTraversal do return some (false, true)
    modify fun s => { s with dataFunctionTypes := s.dataFunctionTypes.insert type }
  return result
end

-- Declared types and value binders share this contextual classifier. Constructor
-- results are scanned nominally; their input types require a positive verdict.
private def classifyType (env : Environment) (type : Expr) (context : Array Expr)
    (checkResult : Bool) : WalkM TypeClassification := do
  let context := if type.hasLooseBVars then context else #[]
  unless ← chargeTraversal (2 * context.size + 1) do return .unclassified
  let key := (type, context, checkResult)
  if let some cached := (← get).typeChecks[key]? then return cached
  let verdict ← inBinderContext context fun locals => do
    let some type ← substitute type locals | return .unclassified
    let exact ← compareCanonical type (← get).statement
    let decision ← compareCanonical type (← get).decision
    let (mentions, unclassified) ← inputType env type #[] checkResult
    if exact || decision then return .forbidden
    if mentions then return .statementMention
    if unclassified then return .unclassified
    return .allowlisted
  let verdict := verdict.getD .unclassified
  unless ← chargeTraversal context.size do return .unclassified
  modify fun s => { s with typeChecks := s.typeChecks.insert key verdict }
  return verdict

private def visitSummary (env : Environment) (origin : Name) (summary : Summary) : WalkM Unit := do
  for node in summary.nodes do
    unless ← chargeSummaryWork (fun c => { c with dispatchWork := c.dispatchWork + 1 }) do return
    if let .const n _ := node.expr then directConstant env n
    if let .proj n _ _ := node.expr then directProjection env n
  if (← get).forbidden then return
  let statement := (← get).statement
  let mut containsStatement : Array Bool := #[]
  for node in summary.nodes do
    unless ← chargeSummaryWork (fun counters =>
      { counters with recheckedNodes := counters.recheckedNodes + 1 }) do
      return
    let mut mentions ← compareCanonical node.expr statement
    for child in node.children do
      unless ← chargeSummaryWork (fun counters =>
        { counters with spineArguments := counters.spineArguments + 1 }) do
        return
      mentions := mentions || containsStatement[child]!
    containsStatement := containsStatement.push mentions
  if summary.incomplete then modify fun s => { s with incomplete := true }
  let mut pending := summary.roots.toList
  while !(← get).forbidden do
    let some index := pending.head? | break
    pending := pending.tail!
    if (← get).exprFuel == 0 then
      modify fun s => { s with incomplete := true }
      break
    unless ← chargeSummaryWork (fun c => { c with dispatchWork := c.dispatchWork + 1 }) do break
    let node := summary.nodes[index]!
    unless ← chargeTraversal (2 * node.context.size) do break
    let e := node.expr
    let occurrence := (e, node.position, node.context)
    if (← get).visited.contains occurrence then continue
    modify fun s => { s with visited := s.visited.insert occurrence }
    let dataPos := node.position == .dataPos
    let checkU (x : SyntaxNode) : WalkM Unit := do
      if dataPos && closed x.expr && x.pContent then
        -- isPropQuick scans application/forall spines before bounded inference.
        unless ← chargeExpression x.expr do return
        let some prop ← boundedMeta (Meta.isProp x.expr) | return
        if prop then
          noteUnclassified (Unclassified.mk "closed_decision"
            (x.appHead.constName?.getD `closed_decision)
            (namespaceLabel env (x.appHead.constName?.getD origin)) origin)
    if dataPos && closed e && containsStatement[index]! && !(← compareCanonical e statement) then
      noteUnclassified (Unclassified.mk "statement_subterm"
        (node.appHead.constName?.getD `statement_subterm)
        (namespaceLabel env (node.appHead.constName?.getD origin)) origin)
    checkU node
    match e with
    | .const n _ =>
      let info := env.find? n
      modify fun s => { s with walked := s.walked.insert n }
      directConstant env n
      if dataPos && n.getRoot == `Classical then
        noteUnclassified (Unclassified.mk "classical_choice" n (namespaceLabel env n) origin)
      if dataPos && !inProtected env n then
        if let some i := info then
          if !Lean.Meta.isInstanceCore env n then
            if let some h ← resultHead i.type then
              if decisionFamily.contains h && !listedProducers.contains n then
                noteUnclassified (Unclassified.mk "unlisted_decision_producer" n (namespaceLabel env n) origin)
      if let some type := node.declaredType then
        modify fun s => { s with typeObligations :=
          (type, #[], info.any (fun i => !i.hasValue (allowOpaque := true)), n, origin) :: s.typeObligations }
        if inProtected env n && !(← get).queued.contains n then queue n
      else modify fun s => { s with incomplete := true }
    | .app _ _ =>
      -- Check instantiated domains after scanning constant dependencies, so a
      -- large type cannot hide a known forbidden API behind budget exhaustion.
      modify fun s => { s with appObligations := (e, node.context, false, origin) :: s.appObligations }
      if let .const head _ := node.appHead then
        if head == ``Decidable.isTrue || head == ``Decidable.isFalse then
          if let some arg := node.firstArg then
            if ← compareCanonical arg (← get).statement then
              modify fun s => { s with forbidden := true }
    | .lam _ t _ _ | .forallE _ t _ _ | .letE _ t _ _ _ =>
      modify fun s => { s with typeObligations :=
        (t, node.context, true, (summary.nodes[node.children[0]!]!).appHead.constName?.getD origin, origin) :: s.typeObligations }
      if let some typeIndex := node.children[0]? then checkU summary.nodes[typeIndex]!
    | .proj n _ _ =>
      directProjection env n
      modify fun s => { s with appObligations := (e, node.context, true, origin) :: s.appObligations }
    | .mvar _ => modify fun s => { s with incomplete := true }
    | _ => pure ()
    pending := node.children.toList ++ pending

private def visit (env : Environment) (pos : Position) (origin : Name) (e : Expr) : WalkM Unit := do
  let summary ← summarise env #[(pos, e)] (← get).exprFuel
  unless ← chargeSummaryWork (fun c => { c with constructionWork := c.constructionWork + summary.constructionWork }) summary.constructionWork do return
  modify fun s => { s with counters.visits := s.counters.visits + summary.visits }
  visitSummary env origin summary

private def process (env : Environment) : WalkM Unit := do
  while !(← get).forbidden do
    unless ← chargeSummaryWork (fun c => { c with dispatchWork := c.dispatchWork + 1 }) do break
    let some n := (← get).pending.head? | do
      if let some (type, context, checkResult, first, origin) := (← get).typeObligations.head? then
        modify fun s => { s with typeObligations := s.typeObligations.tail! }
        match ← classifyType env type context checkResult with
        | .forbidden => modify fun s => { s with forbidden := true }
        | .statementMention =>
          noteUnclassified ⟨"statement_mentioning_type", first, namespaceLabel env first, origin⟩
        | .unclassified =>
          noteUnclassified ⟨"unclassified_argument_type", first, namespaceLabel env first, origin⟩
        | .allowlisted => pure ()
        continue
      if let some (e, context, isProjection, origin) := (← get).appObligations.head? then
        modify fun s => { s with appObligations := s.appObligations.tail! }
        let _ ← inBinderContext context fun locals => do
          let some applied ← substitute e locals | return
          if isProjection then
            match ← projectionDeclaredType env applied with
            | some (projectionName, declaredType) =>
              match ← classifyType env declaredType #[] true with
              | .forbidden => modify fun s => { s with forbidden := true }
              | .statementMention | .unclassified =>
                noteUnclassified ⟨"unclassified_projection_type", projectionName,
                  namespaceLabel env projectionName, origin⟩
              | .allowlisted => pure ()
            | none =>
              noteUnclassified ⟨"unclassified_projection_type", origin,
                namespaceLabel env origin, origin⟩
          let some type ← appliedValueType applied | return
          match ← classifyType env type #[] true with
          | .forbidden => modify fun s => { s with forbidden := true }
          | .statementMention | .unclassified =>
            noteUnclassified ⟨"unclassified_argument_type", origin, namespaceLabel env origin, origin⟩
          | .allowlisted => pure ()
        continue
      break
    modify fun s => { s with pending := s.pending.tail!, walked := s.walked.insert n }
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
          else do
            let summary ← summarise env #[(.typePos, info.type)] (← get).exprFuel
            pure { summary with incomplete := summary.incomplete || !isCtorOrInductive env n &&
              !#[`propext, `Classical.choice, `Quot.sound].contains n }
        let _ ← chargeSummaryWork (fun c => { c with constructionWork := c.constructionWork + summary.constructionWork }) summary.constructionWork
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

private def collectReadout (env : Environment) (theoremName address : Name) (readout : Expr) (extractionWork : Nat := 0) (extractionFailed : Bool := false) : CoreM WalkResult := do
  let scope := (moduleScopeCache.getState env).getD (classifyModules env)
  let env := moduleScopeCache.setState env (some scope)
  modifyEnv (moduleScopeCache.setState · (some scope))
  let some theoremInfo := env.find? theoremName | return { forbidden := false, unclassified := none, incomplete := true, walked := #[] }
  let statement := theoremInfo.type
  let decision := mkApp (mkConst ``Decidable) statement
  let computation : WalkM Unit := do
    unless ← chargeTraversal extractionWork do return
    if extractionFailed then
      modify fun s => { s with incomplete := true }
      return
    visit env .dataPos address readout
    process env
  let budget := min provenanceExpressionFuel (provenanceExpressionLimit.get (← getOptions))
  let (_, state) ← Meta.MetaM.run' <| computation.run {
    theoremName, statement, decision, summaries := summaryCache.getState env, exprFuel := budget }
  let counters := { state.counters with chargedVisits := budget - state.exprFuel }
  modifyEnv (summaryCache.setState · state.summaries)
  modifyEnv (countersCache.setState · counters)
  trace[InformationProvenance.check]
    "theorem={theoremName} P_constants_summarised={counters.summarisedConstants} visits={counters.visits} memo_hits={counters.memoHits} charged_visits={counters.chargedVisits} rechecked_nodes={counters.recheckedNodes} spine_arguments={counters.spineArguments} canonicalizations={counters.canonicalizations} construction_work={counters.constructionWork} traversal_work={counters.traversalWork} dispatch_work={counters.dispatchWork}"
  let names := state.walked.toArray.map Name.toString |>.qsort (· < ·)
  return (WalkResult.mk state.forbidden state.unclassified state.incomplete names)

private def safeCollect (env : Environment) (theoremName address : Name) (readout : Expr)
    (extractionWork : Nat := 0) (extractionFailed : Bool := false) : CoreM WalkResult :=
  tryCatchRuntimeEx (collectReadout env theoremName address readout extractionWork extractionFailed)
    (fun _ => pure { forbidden := false, unclassified := none, incomplete := true, walked := #[] })

private def readoutClosureCurrent (theoremName : Name) (readout : Expr) : CoreM (Bool × Option (Array String)) := do
  let env ← getEnv
  let r ← safeCollect env theoremName `readout readout
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
  let budget := min provenanceExpressionFuel (provenanceExpressionLimit.get (← getOptions))
  let (readout, extractionWork) := ReadoutFamily.extract env realization budget
  let address := readout.map (·.2) |>.getD realization
  let result ← match readout with
    | some (e, _) => safeCollect env theoremName address e extractionWork
    | none => safeCollect env theoremName address (.sort .zero) extractionWork true
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
