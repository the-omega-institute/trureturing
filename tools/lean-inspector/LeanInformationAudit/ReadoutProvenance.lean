import LeanInformationAudit.ReadoutFamily
import Lean.Meta.Tactic.Cases

/-!
Every admission starts with bounded inference of an occurrence in its original
binder context. The structural fold checks that inferred type. Nominal fields
are occurrences in Lean's dependent case branches, including proof and instance
fields; the walker never reconstructs a declaration or constructor type.
Syntax summaries cross queries, but all type verdicts and contextual inference
caches are query-local. CleanReturnInventory pins the complete parsed programs.
-/

namespace LeanInformationAudit.RegistrationGates
open Lean

-- §10.1 budget record: safety limit outside the capacity domain; owner=governance lane;
-- date=2026-09-13; basis=the existing 4100-link closure-exhaustion fixture;
-- exit condition=the supported closure corpus or pinned Lean version changes,
-- then rerun that fixture and review the safety ceiling before changing it.
def provenanceConstantFuel : Nat := 4096
-- Completed InformationRoot and TemplateShadow profiles, Lean 4.33.0,
-- 2026-09-13: the context-selection query consumed 8,034,836 work units;
-- InformationRoot's largest query consumed 3,247,448.
private def provenanceReferenceQueryWork : Nat := 8034836
-- §10.1 budget record: safety limit outside the capacity domain; owner=governance lane;
-- date=2026-09-13; basis=the measured 8,034,836 work-unit maximum plus 25%
-- safety headroom, rounded upward; exit condition=the pinned Lean version,
-- supported readout corpus, or measurement profile changes, then remeasure.
def provenanceExpressionFuel : Nat := (5 * provenanceReferenceQueryWork + 3) / 4
register_option provenanceExpressionLimit : Nat := {
  defValue := provenanceExpressionFuel
  descr := "Readout work limit, capped by the production expression policy" }

-- §10.1 budget record: safety limit outside the capacity domain; owner=governance lane;
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
  statement mention, direct forbidden dependency, an unclassified form, or
  incomplete work. Callers must handle every constructor. -/
  | allowlisted
  | statementMention
  | forbidden
  | unclassified
  | incomplete
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
  if (← get).summary.incomplete then return none
  let (appHead, firstArg) := match e with
    | .app f arg =>
      let fn := nodes[children[0]!]!
      (if f.isApp then fn.appHead else f,
        if f.isApp then fn.firstArg else some arg)
    | _ => (e, none)
  let node : SyntaxNode := {
    expr := e, context := keyContext, position := pos, children, pContent,
    appHead, firstArg }
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
  inferredOccurrences : Nat := 0
  caseExpansions : Nat := 0
  deriving Inhabited, Repr

-- Ordinary environment extensions are compilation-local and not serialized.
private initialize summaryCache : EnvExtension (Std.HashMap (Name × List Level) Summary) ←
  registerEnvExtension (pure {})
private initialize countersCache : EnvExtension ProvenanceCounters ←
  registerEnvExtension (pure {})

def getProvenanceCounters : CoreM ProvenanceCounters := do
  return countersCache.getState (← getEnv)

private structure WalkState where
  theoremName : Name
  statement : Expr
  decision : Expr
  summaries : Std.HashMap (Name × List Level) Summary := {}
  counters : ProvenanceCounters := {}
  visited : Std.HashSet (Expr × Position × Array Expr) := {}
  walked : NameHashSet := {}
  queued : Std.HashSet (Name × List Level) := {}
  pending : List (Name × List Level) := []
  typeObligations : List (Expr × Array Expr × Name × Name) := []
  comparisons : Std.HashMap (Expr × Expr) Bool := {}
  typeChecks : Std.HashMap (Expr × Array Expr) TypeClassification := {}
  forbidden : Bool := false
  unclassified : Option Unclassified := none
  incomplete : Bool := false
  weights : Std.HashMap Expr Nat := {}
  substitutionWeights : Std.HashMap (Expr × Nat) Nat := {}
  levelWeights : Std.HashMap Level Nat := {}
  applications : Std.HashMap Expr (Expr × Array Expr) := {}
  mentionsCache : Std.HashMap Expr Bool := {}
  cleanTypes : Std.HashSet Expr := {}
  assumedFamilyDepth : Option Nat := none
  inferredTypes : Std.HashMap Expr Expr := {}
  cleanKinds : Std.HashSet Expr := {}
  certifiedNullaryCarriers : Std.HashSet Expr := {}
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

-- Lean 4.33's instantiate_rev_core stops when the binder offset reaches a
-- subterm's loose-variable range (kernel/instantiate.cpp). Count that visited
-- frontier, including stopped roots, before performing the native operation.
private partial def substitutionWeight (e : Expr) (offset : Nat := 0) : WalkM (Option Nat) := do
  unless ← chargeTraversal do return none
  let key := (e, offset)
  if let some size := (← get).substitutionWeights[key]? then return some size
  let children := if offset >= e.looseBVarRange then #[] else match e with
    | .app f a => #[(f, offset), (a, offset)]
    | .lam _ t b _ | .forallE _ t b _ => #[(t, offset), (b, offset + 1)]
    | .letE _ t v b _ => #[(t, offset), (v, offset), (b, offset + 1)]
    | .mdata _ b | .proj _ _ b => #[(b, offset)]
    | _ => #[]
  let mut size := 1
  for (child, childOffset) in children do
    let some childSize ← substitutionWeight child childOffset | return none
    size := min (provenanceExpressionFuel + 1) (size + childSize)
  modify fun s => { s with substitutionWeights := s.substitutionWeights.insert key size }
  return some size

private def substitute (e : Expr) (locals : Array Expr) : WalkM (Option Expr) := do
  if !e.hasLooseBVars then return some e
  let some size ← substitutionWeight e | return none
  unless ← chargeTraversal locals.size do return none
  let mut factor := 1
  for value in locals do
    if value.hasLooseBVars then
      let some valueSize ← expressionWeight value | return none
      factor := factor + valueSize
  -- An open replacement can be lifted at every substituted variable.
  unless ← chargeTraversal (size * factor) do return none
  return some (e.instantiateRev locals)

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

private def queue (name : Name) (levels : List Level) : WalkM Unit := do
  let n := (name, levels)
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
      pure (Except.ok result)) (fun ex => pure (Except.error ex)) : MetaM (Except Exception Bool))
  match result with
  | .ok result =>
    modify fun s => { s with comparisons := s.comparisons.insert (a, b) result }
    return result
  | .error ex =>
    trace[InformationProvenance.check] "comparison_failure lhs={a} rhs={b}: {ex.toMessageData}"
    -- Keep the exception until Lean's native predicate identifies its cause.
    noteUnclassified ⟨(if ex.isMaxHeartbeat then "defeq_budget" else "meta_runtime_exception"),
      `defeq, "unclassified", if ex.isMaxHeartbeat then `heartbeat_exhaustion else `meta_runtime_exception⟩
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
  if (env.find? n).isSome then
    let occurrence := mkConst n levels
    let origin := (← get).theoremName
    modify fun s => { s with typeObligations :=
      (occurrence, #[], n, origin) :: s.typeObligations }
    if inProtected env n then queue n levels
  else modify fun s => { s with incomplete := true }

-- Eligible instance heads still require the same structural fold over their
-- parameters and every constructor field. An unfamiliar class never inherits external-leaf
-- status from its module. In particular proof-carrying user classes are unclassified.
private def listedTypeClasses : Array Name := #[
  ``Decidable, ``OfNat, ``Inhabited, ``Subsingleton, ``Nonempty, ``BEq, ``LawfulBEq,
  `Fintype, `Finite, `NeZero,
  -- Collection and relation interfaces used by the frozen readout corpus.
  ``Membership, ``GetElem, ``GetElem?, ``Setoid, `SetLike, ``Singleton, ``Insert,
  ``Std.Associative, ``Std.Commutative,
  -- Scalar operator interfaces: their actual type parameters are checked too.
  ``Zero, ``One, ``Add, ``HAdd, ``Mul, ``HMul, ``Sub, ``HSub, ``Div, ``HDiv,
  ``Neg, ``Inv, ``Pow, ``HPow, ``Mod, ``HMod, ``LT, ``LE, ``NatPow]

private def boundedMeta (action : MetaM α) (site : Name := `type_classification)
    (operations : Nat := 1) : WalkM (Option α) := do
  unless ← chargeSummaryWork (fun c => { c with canonicalizations := c.canonicalizations + operations }) operations do
    return none
  let budget := min provenanceDefEqHeartbeats (provenanceDefEqLimit.get (← getOptions))
  if budget == 0 then
    noteUnclassified ⟨"defeq_budget", `defeq, "unclassified", `defeq⟩
    return none
  let result ← (tryCatchRuntimeEx (do
    let start ← IO.getNumHeartbeats
    controlAt CoreM fun runInBase => withReader (fun ctx : Core.Context =>
      { ctx with initHeartbeats := start, maxHeartbeats := budget * operations }) do
      let result ← runInBase action
      Core.checkMaxHeartbeats "readout type classification"
      pure (Except.ok result)) (fun ex => pure (Except.error ex)) : MetaM (Except Exception α))
  match result with
  | .ok value => return some value
  | .error ex =>
    trace[InformationProvenance.check] "meta_failure operation={site}: {ex.toMessageData}"
    noteUnclassified ⟨(if ex.isMaxHeartbeat then "defeq_budget" else "meta_runtime_exception"),
      `defeq, "unclassified", if ex.isMaxHeartbeat then `heartbeat_exhaustion else `meta_runtime_exception⟩
    return none

-- These locals are rebuilt from the original typed readout syntax in this
-- query. Their immutable let values are valid even when Lean marks the local
-- nondependent; generic zetaReduce deliberately hides such preexisting values.
private def normalizeIndex (e : Expr) : WalkM (Option Expr) :=
  boundedMeta <| Meta.transform e (usedLetOnly := true) (pre := fun part => do
    let .fvar id := part.getAppFn | return .continue
    let decl ← id.getDecl
    let some value := decl.value? (allowNondep := true) | return .continue
    return .visit (value.beta part.getAppArgs))

-- This is the only source of types used for occurrence admission. Expressions
-- contain their actual levels and stable local identities; no inference cache
-- survives the registered-statement query. Failed inference is never cached.
private def occurrenceType (e : Expr) : WalkM (Option Expr) := do
  unless ← chargeTraversal do return none
  if e.hasLooseBVars || e.hasMVar || e.hasLevelMVar then
    noteUnclassified ⟨"unclassified_occurrence", `occurrence, "unclassified", `occurrence⟩
    return none
  if let some type := (← get).inferredTypes[e]? then return some type
  unless ← chargeExpression e do return none
  let some type ← boundedMeta (Meta.inferType e) `infer_type | return none
  modify fun s => { s with
    inferredTypes := s.inferredTypes.insert e type
    counters.inferredOccurrences := s.counters.inferredOccurrences + 1 }
  return some type

-- Lean's dependent elimination returns actual branch occurrences after solving
-- index equations. Unsupported equations raise an exception; there is no generic
-- telescope fallback. Immutable branch contexts retain all local instances.
private def caseFields (type : Expr) :
    WalkM (Option (Array (LocalContext × LocalInstances × Meta.FVarSubst × Array Expr))) := do
  unless ← chargeTraversal do return none
  unless ← chargeExpression type do return none
  let some (.inductInfo family) := (type.getAppFn.constName?.bind (← getEnv).find?) | return none
  -- Native cases batches every constructor of a proposition even when asked
  -- for one. Reserve one existing Meta allowance per constructor; this is an
  -- explicitly charged batch, while inferType/whnf/defeq remain single queries.
  let mut operations := 0
  for _ in family.ctors do
    unless ← chargeTraversal do return none
    operations := operations + 1
  operations := max 1 operations
  let some fields ← boundedMeta (Meta.withLocalDeclD `readoutValue type fun value => do
    let goal ← Meta.mkFreshExprMVar (mkConst ``True) .syntheticOpaque
    let branches ← goal.mvarId!.cases value.fvarId!
    branches.mapM fun branch => branch.mvarId.withContext do
      let fields ← branch.fields.mapM instantiateMVars
      return (← getLCtx, ← Meta.getLocalInstances, branch.subst, fields)) `case_fields operations | do
    trace[InformationProvenance.check] "failed_cases_type={type} locals={(← getLCtx).numIndices}"
    return none
  unless ← chargeTraversal fields.size do return none
  modify fun s => { s with
    counters.caseExpansions := s.counters.caseExpansions + 1 }
  return some fields

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
    | _ =>
      noteUnclassified ⟨"unclassified_binder_context", `binder, "unclassified", `binder⟩
      return none
  else return some (← k locals)

-- Reuse reconstructed binders only when the original parent context is empty.
-- Restoring both locals and local instances preserves their actual types and
-- stable fvar identities; nested callers retain their existing parent context.
private partial def inBinderContext (context : Array Expr) (k : Array Expr → WalkM α) :
    WalkM (Option α) := do
  if context.isEmpty then return some (← k #[])
  if !(← getLCtx).isEmpty then return ← buildBinderContext context k
  unless ← chargeTraversal (2 * context.size + 1) do return none
  if let some (lctx, instances, locals) := (← get).binderContexts[context]? then
    return some (← Meta.withLCtx lctx instances (k locals))
  unless ← chargeTraversal context.size do return none
  -- Canonicalize the parent first: extending a lexical prefix must retain
  -- its immutable local identities so shared occurrences reuse inference.
  let parent := context.pop
  let result ← inBinderContext parent fun locals =>
    buildBinderContext context (fun locals => do
      let lctx ← getLCtx
      let instances ← Meta.getLocalInstances
      modify fun s => { s with binderContexts := s.binderContexts.insert context (lctx, instances, locals) }
      k locals) parent.size locals
  return result.join

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

-- The least unfinished ancestor used by a recursive cutoff. None means that
-- no enclosing-family assumption was used; this is proof-dependency metadata,
-- never a classification mode.
private def mergeAssumptions (a b : Option Nat) : Option Nat :=
  match a, b with
  | none, x | x, none => x
  | some a, some b => some (min a b)

private def noteFamilyAssumption (depth : Nat) : WalkM Unit := do
  unless ← chargeTraversal do return
  modify fun s => { s with assumedFamilyDepth := mergeAssumptions s.assumedFamilyDepth (some depth) }

mutual
-- One structural fold over inferred types and their type-valued arguments.
-- Every nominal field is inferred in a context returned by dependent cases.
private partial def inputType (env : Environment) (type : Expr)
    (active : Array Expr := #[]) : WalkM (Bool × Bool) := do
  unless ← chargeSummaryWork (fun c => { c with recheckedNodes := c.recheckedNodes + 1 }) do
    return (false, true)
  if type.hasLooseBVars || type.hasMVar || type.hasLevelMVar then return (false, true)
  let key := type
  if (← get).cleanTypes.contains key then return (false, false)
  unless ← chargeTraversal do return (false, true)
  let enclosingAssumptions := (← get).assumedFamilyDepth
  modify fun s => { s with assumedFamilyDepth := none }
  let classify : WalkM (Bool × Bool) := do
    -- Case substitutions can change an enclosing family's arguments. Every
    -- recursive occurrence therefore rechecks its actual arguments below
    -- before using the enclosing-family assumption.
    -- A telescope is already traversed domain by domain by this classifier.
    -- Rescanning each complete suffix with typeMentions would duplicate its
    -- binder reconstruction and comparisons at every level.
    if let .forallE n domain body bi := type then
      let exact ← compareCanonical type (← get).statement
      let decision ← compareCanonical type (← get).decision
      let (dm, du) ← inputType env domain active
      let (bm, bu) ← Meta.withLocalDecl n bi domain fun x => do
        let some body ← substitute body #[x] | return (false, true)
        inputType env body active
      return (exact || decision || dm || bm, du || bu)
    if let .letE _ domain value body _ := type then
      let exact ← compareCanonical type (← get).statement
      let decision ← compareCanonical type (← get).decision
      let (dm, du) ← inputType env domain active
      let vm ← typeMentions env value
      let some body ← substitute body #[value] | return (false, true)
      let (bm, bu) ← inputType env body active
      return (exact || decision || dm || vm || bm, du || bu)
    let mut mentions ← typeMentions env type
    if ← compareCanonical type (← get).decision then mentions := true
    let some reduced ← boundedMeta (Meta.whnf type) `type_whnf | do
      trace[InformationProvenance.check] "failed_type={type}"
      return (mentions, true)
    mentions := (← typeMentions env reduced) || mentions
    match reduced with
    | .forallE n domain body bi =>
      let (dm, du) ← inputType env domain active
      let (bm, bu) ← Meta.withLocalDecl n bi domain fun x =>
        do
          let some body ← substitute body #[x] | return (false, true)
          inputType env body active
      return (mentions || dm || bm, du || bu)
    | .lam n domain body bi =>
      -- Type-valued lambda expressions are generated by dependent recursors
      -- (for example `Fin.casesOn` motives).  Inspect their domains and bodies
      -- through this same classifier instead of treating the lambda head as
      -- an unknown escape.
      let (dm, du) ← inputType env domain active
      let (bm, bu) ← Meta.withLocalDecl n bi domain fun x => do
        let some body ← substitute body #[x] | return (false, true)
        inputType env body active
      return (mentions || dm || bm, du || bu)
    | .letE n domain value body nd =>
      let (dm, du) ← inputType env domain active
      let (vm, vu) ← inputType env value active
      let (bm, bu) ← Meta.withLetDecl n domain value (fun x => do
        let some body ← substitute body #[x] | return (false, true)
        inputType env body active) (nondep := nd)
      return (mentions || dm || vm || bm, du || vu || bu)
    | .mdata _ body =>
      let (bm, bu) ← inputType env body active
      return (mentions || bm, bu)
    | _ =>
      if reduced.isSort then return (mentions, false)
      let some (head, args) ← applicationParts reduced | return (mentions, true)
      let mut unclassified := false
      for arg in args do
        let some argType ← occurrenceType arg | return (mentions, true)
        let (tm, tu) ← inputType env argType active
        mentions := mentions || tm
        unclassified := unclassified || tu
        if let some (am, au) ← typeFamilyArgument env arg argType active then
          mentions := mentions || am
          unclassified := unclassified || au
      -- A local type-family head is allowed only after its inferred type has
      -- itself passed the funnel.  This keeps local neutral syntax from being
      -- an unknown-tolerant escape hatch.
      if head.isFVar then
        let some neutralType ← occurrenceType reduced | return (mentions, true)
        let (fm, fu) ← inputType env neutralType active
        return (mentions || fm, unclassified || fu)
      if let .proj _ _ receiver := head then
        -- Infer both the receiver and projection in the same context. Lean
        -- supplies the receiver's actual parameters, indices and universe.
        let some receiverType ← occurrenceType receiver | return (mentions, true)
        let (rm, ru) ← inputType env receiverType active
        let some projectionType ← occurrenceType head | return (mentions || rm, true)
        let (pm, pu) ← inputType env projectionType active
        return (mentions || rm || pm, ru || pu || unclassified)
      let .const name _ := head | do
        -- Neutral type expressions have no declaration head to inspect.  Their
        -- inferred type is still an obligation: classify it before accepting
        -- the neutral expression, and fail closed if inference is unavailable.
        let some neutralType ← occurrenceType reduced | return (mentions, true)
        let (nm, nu) ← inputType env neutralType active
        return (mentions || nm, unclassified || nu)
      let some declaration := env.find? name | return (mentions, true)
      unless ← chargeTraversal do return (mentions, true)
      if !declaration.hasValue (allowOpaque := true) && !(← get).cleanKinds.contains head then
        -- The actual head occurrence supplies its inferred kind. This closed
        -- kind is independent of the caller's recursive-family assumptions.
        let some kind ← occurrenceType head | return (mentions, true)
        let (km, ku) ← inputType env kind #[]
        mentions := mentions || km
        unclassified := unclassified || ku
        let state ← get
        if !km && !ku && !state.incomplete && !state.forbidden && state.unclassified.isNone then
          unless ← chargeTraversal do return (mentions, true)
          modify fun s => { s with cleanKinds := s.cleanKinds.insert head }
      -- Equality has no independent payload: reflexivity carries only the
      -- operands already checked above. Eliminating an arbitrary equality
      -- would instead ask Lean to solve a theorem (e.g. f x = x).
      if name == ``Eq || name == ``HEq then return (mentions, unclassified)
      -- Nat.le has only natural indices and recursive Nat.le premises. Check
      -- the actual operands above; if S is itself an order statement, reject
      -- conservatively so no recursive order subproof can conceal it. This
      -- avoids enumerating numeric representation bounds (UInt32, Char, ...).
      if name == ``Nat.le then
        let some statement ← boundedMeta (Meta.whnf (← get).statement) `statement_head
          | return (mentions, true)
        return (mentions, unclassified || statement.getAppFn.isConstOf ``Nat.le)
      -- Membership and uniqueness proofs over checked data carriers contain
      -- only recursive Mem/Pairwise and equality/function proof forms. The
      -- positive statement heads below cannot specialize to those forms.
      if (name == ``List.Pairwise || name == ``List.Mem) && args.size == 3 then
        let some kind ← occurrenceType args[0]! | return (mentions, true)
        let some (.sort level) ← boundedMeta (Meta.whnf kind) `carrier_kind
          | return (mentions, true)
        let relation := mkApp (mkConst ``Ne [level]) args[0]!
        let some carrier ← normalizeIndex args[0]! | return (mentions, true)
        let some rigid ← boundedMeta (do
          let carrier ← Meta.whnf carrier
          let .fvar id := carrier | return false
          return (← id.getDecl).value? (allowNondep := true) |>.isNone) `carrier_rigidity
          | return (mentions, true)
        -- A rigid parameter is scoped to this occurrence. Applications and
        -- enclosing case substitutions get freshly inferred field types.
        let mut carrierAllowed := rigid || (← compareCanonical carrier (mkConst ``Nat))
        if !carrierAllowed && level.isNeverZero then
          let some carrier ← boundedMeta (Meta.whnf carrier) `carrier_whnf
            | return (mentions, true)
          if let some (.inductInfo family) := (carrier.getAppFn.constName?.bind env.find?) then
            let nullary := family.numParams == 0 && family.numIndices == 0 &&
              family.ctors.all (fun ctor => match env.find? ctor with
                | some (.ctorInfo info) => info.numFields == 0
                | _ => false)
            if nullary && closed carrier && !carrier.hasLevelMVar then
              unless ← chargeTraversal do return (mentions, true)
              if (← get).certifiedNullaryCarriers.contains carrier then
                carrierAllowed := true
              else
                let some branches ← caseFields carrier | return (mentions, true)
                carrierAllowed := branches.all (fun (_, _, _, fields) => fields.isEmpty)
                if carrierAllowed then
                  unless ← chargeTraversal do return (mentions, true)
                  modify fun s => { s with certifiedNullaryCarriers :=
                    s.certifiedNullaryCarriers.insert carrier }
        if carrierAllowed && (name == ``List.Mem || (← compareCanonical args[1]! relation)) then
          let some statement ← boundedMeta (Meta.whnf (← get).statement) `statement_head
            | return (mentions, true)
          let disjoint ← match statement with
            | .forallE _ domain body _ => do
              let some domain ← boundedMeta (Meta.whnf domain) `statement_domain
                | return (mentions, true)
              pure (domain.getAppFn.isConstOf ``Exists && body.isConstOf ``False)
            | _ => pure (statement.getAppFn.constName?.any (#[``And, ``Or, ``Exists, ``True].contains ·))
          if disjoint then return (mentions, unclassified)
      if Lean.isClass env name && !listedTypeClasses.contains name then
        return (mentions, true)
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
      for depth in [:active.size] do
        let previous := active[depth]!
        let some (previousHead, previousArgs) ← applicationParts previous | return (mentions, true)
        unless ← chargeTraversal do return (mentions, true)
        if hash previousHead != hash head then continue
        unless ← chargeExpression previousHead do return (mentions, true)
        unless ← chargeExpression head do return (mentions, true)
        if previousHead == head then
          let mut sameParameters := true
          for index in [:info.numParams] do
            unless ← chargeTraversal do return (mentions, true)
            let some a := previousArgs[index]? | return (mentions, true)
            let some b := args[index]? | return (mentions, true)
            sameParameters := (← compareCanonical a b) && sameParameters
          let mut coveredIndices := true
          for index in [info.numParams:args.size] do
            unless ← chargeTraversal do return (mentions, true)
            let current := args[index]!
            -- Recursive occurrences with fresh indices share the enclosing
            -- family obligation. Concrete changed indices require fresh cases.
            if current.hasFVar then
              let some normalized ← normalizeIndex current | return (mentions, true)
              if normalized.hasFVar then continue
            let some previous := previousArgs[index]? | return (mentions, true)
            coveredIndices := (← compareCanonical previous current) && coveredIndices
          if sameParameters && coveredIndices then
            noteFamilyAssumption depth
            return (mentions, unclassified)
          -- Different parameters are a fresh obligation, as in nested products.
      let some branches ← caseFields reduced | return (mentions, true)
      unless ← chargeTraversal (active.size + 1) do return (mentions, true)
      let nextActive := active.push reduced
      for (lctx, instances, subst, fields) in branches do
        let mut branchActive := #[]
        for family in nextActive do
          unless ← chargeExpression family do return (mentions, true)
          let some family ← boundedMeta (pure (subst.apply family)) | return (mentions, true)
          branchActive := branchActive.push family
        for field in fields do
          unless ← chargeTraversal do return (mentions, true)
          let (fm, fu) ← Meta.withLCtx lctx instances do
            let some fieldType ← occurrenceType field | return (false, true)
            inputType env fieldType branchActive
          mentions := mentions || fm
          unclassified := unclassified || fu
      return (mentions, unclassified)

  let result ← classify
  -- Constructor scans introduced in this call have now completed; discharge
  -- their recursive assumptions. A dependency on an enclosing unfinished family
  -- still forbids caching. Independent nested checks can be reused immediately.
  unless ← chargeTraversal do return (false, true)
  let unresolved := (← get).assumedFamilyDepth.filter (· < active.size)
  modify fun s => { s with
    assumedFamilyDepth := mergeAssumptions enclosingAssumptions unresolved }
  let state ← get
  if unresolved.isNone && !type.hasLooseBVars && !type.hasMVar && !type.hasLevelMVar &&
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
    let some reduced ← boundedMeta (Meta.whnf type) `family_whnf | return some (false, true)
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

-- The sole admission entry: infer the occurrence in its lexical context, then
-- fold its inferred type. Nested type syntax is handled by the same type fold.
private def classifyOccurrence (env : Environment) (occurrence : Expr)
    (context : Array Expr) : WalkM TypeClassification := do
  let context := if occurrence.hasLooseBVars then context else #[]
  unless ← chargeTraversal (2 * context.size + 1) do return .incomplete
  let key := (occurrence, context)
  if let some cached := (← get).typeChecks[key]? then return cached
  let verdict ← inBinderContext context fun locals => do
    let some occurrence ← substitute occurrence locals | return .incomplete
    let some type ← occurrenceType occurrence | return .incomplete
    let exact ← compareCanonical type (← get).statement
    let decision ← compareCanonical type (← get).decision
    let (mentions, unclassified) ← inputType env type
    if exact || decision then return .forbidden
    if mentions then return .statementMention
    let state ← get
    if state.forbidden then return .forbidden
    if state.unclassified.isSome then return .unclassified
    if state.incomplete then return .incomplete
    if unclassified then return .unclassified
    return .allowlisted
  let verdict := verdict.getD (if (← get).incomplete then .incomplete else .unclassified)
  unless ← chargeTraversal context.size do return .incomplete
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
    | .const n levels =>
      let info := env.find? n
      modify fun s => { s with walked := s.walked.insert n }
      directConstant env n
      if dataPos && n.getRoot == `Classical then
        noteUnclassified (Unclassified.mk "classical_choice" n (namespaceLabel env n) origin)
      if dataPos && !inProtected env n then
        if info.isSome then
          if !Lean.Meta.isInstanceCore env n then
            if let some type ← occurrenceType e then
              if let some h ← resultHead type then
                if decisionFamily.contains h && !listedProducers.contains n then
                  noteUnclassified (Unclassified.mk "unlisted_decision_producer" n (namespaceLabel env n) origin)
      if info.isSome then
        if inProtected env n then queue n levels
      else modify fun s => { s with incomplete := true }
    | .app _ _ =>
      if let .const head _ := node.appHead then
        if head == ``Decidable.isTrue || head == ``Decidable.isFalse then
          if let some arg := node.firstArg then
            if ← compareCanonical arg (← get).statement then
              modify fun s => { s with forbidden := true }
    | .lam .. | .forallE .. | .letE .. =>
      if let some typeIndex := node.children[0]? then checkU summary.nodes[typeIndex]!
    | .proj n _ _ => directProjection env n
    | .mvar _ => modify fun s => { s with incomplete := true }
    | _ => pure ()
    modify fun s => { s with typeObligations :=
      (e, node.context, node.appHead.constName?.getD origin, origin) :: s.typeObligations }
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
      if let some (type, context, first, origin) := (← get).typeObligations.head? then
        modify fun s => { s with typeObligations := s.typeObligations.tail! }
        match ← classifyOccurrence env type context with
        | .forbidden => modify fun s => { s with forbidden := true }
        | .statementMention =>
          noteUnclassified ⟨"statement_mentioning_type", first, namespaceLabel env first, origin⟩
        | .unclassified =>
          noteUnclassified ⟨"unclassified_argument_type", first, namespaceLabel env first, origin⟩
        | .incomplete => modify fun s => { s with incomplete := true }
        | .allowlisted => pure ()
        continue
      break
    modify fun s => { s with pending := s.pending.tail!, walked := s.walked.insert n.1 }
    if (← get).exprFuel == 0 then
      modify fun s => { s with incomplete := true }
      break
    let some info := env.find? n.1 | modify fun s => { s with incomplete := true }; continue
    let summary ← if let some cached := (← get).summaries[n]? then do
        modify fun s => { s with counters.memoHits := s.counters.memoHits + 1 }
        pure cached
      else do
        let some type ← occurrenceType (mkConst n.1 n.2) | continue
        let summary ← if info.hasValue (allowOpaque := true) then do
            let valuePos := match info with | .thmInfo _ => .proofPos | _ => .dataPos
            let value ← Core.instantiateValueLevelParams info n.2 (allowOpaque := true)
            unless ← chargeExpression value do continue
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
  walked : Array String

private def collectReadout (env : Environment) (theoremName address : Name) (readout : Expr) (extractionWork : Nat := 0) (extractionFailed : Bool := false) : CoreM WalkResult := do
  let scope := (moduleScopeCache.getState env).getD (classifyModules env)
  let env := moduleScopeCache.setState env (some scope)
  modifyEnv (moduleScopeCache.setState · (some scope))
  let some theoremInfo := env.find? theoremName | return { forbidden := false, unclassified := none, incomplete := true, walked := #[] }
  let statement ← Meta.MetaM.run' <| Meta.inferType
    (mkConst theoremName (theoremInfo.levelParams.map Level.param))
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
    "theorem={theoremName} P_constants_summarised={counters.summarisedConstants} visits={counters.visits} memo_hits={counters.memoHits} charged_visits={counters.chargedVisits} rechecked_nodes={counters.recheckedNodes} spine_arguments={counters.spineArguments} canonicalizations={counters.canonicalizations} construction_work={counters.constructionWork} traversal_work={counters.traversalWork} dispatch_work={counters.dispatchWork} inferred_occurrences={counters.inferredOccurrences} case_expansions={counters.caseExpansions}"
  let names := state.walked.toArray.map Name.toString |>.qsort (· < ·)
  return (WalkResult.mk state.forbidden state.unclassified state.incomplete names)

private def safeCollect (env : Environment) (theoremName address : Name) (readout : Expr)
    (extractionWork : Nat := 0) (extractionFailed : Bool := false) : CoreM WalkResult :=
  tryCatchRuntimeEx (collectReadout env theoremName address readout extractionWork extractionFailed)
    (fun ex => do
      trace[InformationProvenance.check] "collection_failure: {ex.toMessageData}"
      pure { forbidden := false, unclassified := none, incomplete := true, walked := #[] })

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
