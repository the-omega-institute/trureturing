import Lean


namespace LeanInformationAudit.RegistrationGates.ReadoutFamily
open Lean

-- §10.1 budget record: safety limit outside the capacity domain; owner=governance lane;
-- date=2026-09-13; basis=the realization decoder's 256-step structural-depth
-- ceiling; exit condition=the supported realization encoding or pinned Lean
-- version changes, then rerun decoder depth and malformed-encoding fixtures.
-- Deeper or unrecognized encodings fail closed; shared fuel also bounds width.
private def depthLimit : Nat := 256

private inductive WeightNode where
  | expr (value : Expr)
  | level (value : Level)
  deriving BEq, Hashable, Inhabited

private structure Spine where
  head : Expr
  reversed : List Expr := []
  arity : Nat := 0
  deriving Inhabited

private structure WorkState where
  fuel : Nat
  cap : Nat
  spent : Nat := 0
  weights : Std.HashMap WeightNode Nat := {}
  spines : Std.HashMap Expr Spine := {}

private abbrev DecodeM := OptionT (StateM WorkState)

private def charge (amount : Nat := 1) : DecodeM Unit := do
  let s ← get
  unless amount ≤ s.fuel do failure
  modify fun s => { s with fuel := s.fuel - amount, spent := s.spent + amount }

private def weightChildren : WeightNode → DecodeM (Array WeightNode)
  | .expr e => do
    match e with
    | .app f a | .lam _ f a _ | .forallE _ f a _ => return #[.expr f, .expr a]
    | .letE _ t v b _ => return #[.expr t, .expr v, .expr b]
    | .mdata _ b | .proj _ _ b => return #[.expr b]
    | .sort l => return #[.level l]
    | .const _ levels =>
      let mut children := #[]
      for level in levels do
        charge
        children := children.push (.level level)
      return children
    | _ => return #[]
  | .level l => return match l with
    | .succ a => #[.level a]
    | .max a b | .imax a b => #[.level a, .level b]
    | _ => #[]

-- Iterative postorder avoids using the native stack for untrusted tree depth.
-- The capped tree weight is reused, while calculating it also consumes fuel.
private def weight (e : Expr) : DecodeM Nat := do
  let root := WeightNode.expr e
  let mut pending : List (WeightNode × Bool) := [(root, false)]
  while !pending.isEmpty do
    charge
    let (node, ready) := pending.head!
    pending := pending.tail!
    if (← get).weights.contains node then continue
    let children ← weightChildren node
    if ready then
      let mut size := 1
      for child in children do
        charge
        let some childSize := (← get).weights[child]? | failure
        size := min (← get).cap (size + childSize)
      modify fun s => { s with weights := s.weights.insert node size }
    else
      pending := (node, true) :: pending
      for child in children do
        charge
        pending := (child, false) :: pending
  let some size := (← get).weights[root]? | failure
  return size

-- Prefixes share a reversed argument list. Walking every family subexpression
-- therefore does not rescan the entire application spine at each prefix.
private def spine (e : Expr) : DecodeM Spine := do
  let mut current := e
  let mut pending : List (Expr × Expr) := []
  let mut result : Spine := { head := e }
  while true do
    charge
    if let some cached := (← get).spines[current]? then
      result := cached
      break
    match current with
    | .app f arg =>
      pending := (current, arg) :: pending
      current := f
    | _ =>
      result := { head := current }
      modify fun s => { s with spines := s.spines.insert current result }
      break
  for (application, arg) in pending do
    charge
    result := { result with reversed := arg :: result.reversed, arity := result.arity + 1 }
    modify fun s => { s with spines := s.spines.insert application result }
  return result

private def argument (s : Spine) (index : Nat) : DecodeM Expr := do
  unless index < s.arity do failure
  let offset := s.arity - 1 - index
  charge (offset + 1)
  let some arg := s.reversed[offset]? | failure
  return arg

private def applySpine (head : Expr) (s : Spine) : DecodeM Expr := do
  charge s.arity
  let mut result := head
  for arg in s.reversed.reverse do
    charge
    result := mkApp result arg
  return result

private def instantiate (body arg : Expr) : DecodeM Expr := do
  charge
  if !body.hasLooseBVars then return body
  let bodyWeight ← weight body
  let argWeight ← if arg.hasLooseBVars then weight arg else pure 0
  -- An open replacement can require lifting at every substituted occurrence.
  charge (bodyWeight * (argWeight + 1))
  return body.instantiate1 arg

private def instantiateLevels (body : Expr) (params : List Name) (levels : List Level) :
    DecodeM Expr := do
  charge
  if !body.hasLevelParam then return body
  let size ← weight body
  let mut factor := 1
  for _ in params do
    charge
    factor := factor + 1
  -- Each parameter occurrence may inspect the complete parameter substitution.
  charge (size * factor)
  return body.instantiateLevelParams params levels

private def beta (s : Spine) : DecodeM Expr := do
  let size ← weight s.head
  let mut factor := 1
  for arg in s.reversed do
    charge
    if arg.hasLooseBVars then factor := factor + (← weight arg)
  -- Reserve lambda/metadata scanning, substitution, and residual applications.
  charge (size + size * factor + s.arity)
  charge s.arity
  return s.head.betaRev s.reversed.toArray

private def recordHead (env : Environment) : Nat → Expr → DecodeM Expr
  | 0, _ => failure
  | depth + 1, e => do
    charge
    let s ← spine e
    match s.head with
    | .mdata _ body => recordHead env depth (← applySpine body s)
    | .letE _ _ value body _ =>
      recordHead env depth (← applySpine (← instantiate body value) s)
    | .lam .. =>
      if s.arity == 0 then return e
      recordHead env depth (← beta s)
    | .const name levels =>
      match env.find? name with
      | some (.defnInfo info) =>
        recordHead env depth (← applySpine (← instantiateLevels info.value info.levelParams levels) s)
      | some _ => return e
      | none => failure
    | .proj _ index value =>
      let value ← recordHead env depth value
      let constructor ← spine value
      let .const name _ := constructor.head | return e
      let some (.ctorInfo info) := env.find? name | return e
      let field ← argument constructor (info.numParams + index)
      recordHead env depth (← applySpine field s)
    | _ => return e

def carrierHeads : Array Name := #[
  `D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index,
  `D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Output,
  `D5.S3.ConceptDynamics.InformationEscape.Arena.State,
  `LeanInformationAudit.StructuralPrimitiveSignature.Index,
  `LeanInformationAudit.StructuralPrimitiveSignature.Output,
  `LeanInformationAudit.StructuralArena.State,
  `D5.S3.ConceptDynamics.InformationEscape.StructuralArena.State,
  `D5.S3.ConceptDynamics.InformationEscape.StructuralPrimitiveSignature.Index,
  `D5.S3.ConceptDynamics.InformationEscape.StructuralPrimitiveSignature.Output]

private def decode (env : Environment) (realization : Name) : DecodeM Expr := do
  charge
  let some info := env.find? realization | failure
  let root ← match info with
    | .thmInfo info => do
      let type ← recordHead env depthLimit info.type
      let s ← spine type
      unless s.arity == 3 && s.head.constName? ==
          some `D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization do failure
      argument s 2
    | .defnInfo _ => pure (mkConst realization)
    | _ => failure
  let value ← recordHead env depthLimit root
  let s ← spine value
  unless s.head.constName? == some `D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.mk ||
      s.head.constName? == some `LeanInformationAudit.StructuralPrimitiveRealization.mk do failure
  argument s 2

/-- Decode a readout and return the work already debited from the supplied fuel.
The caller transfers this debit even when decoding fails; caches are query-local. -/
def extract (env : Environment) (realization : Name) (fuel : Nat) : Option (Expr × Name) × Nat :=
  let action : DecodeM (Expr × Name) := do
    let value ← decode env realization
    let view ← spine value
    return (value, view.head.constName?.getD realization)
  let (result, state) := action.run.run { fuel, cap := fuel + 1 }
  (result, state.spent)

-- Only the declared carrier selectors may enter the record decoder from type
-- classification. Arbitrary data expressions have no such reduction boundary.
def carrier (env : Environment) (e : Expr) (fuel : Nat) : Option Expr × Nat :=
  let action : DecodeM Expr := recordHead env depthLimit e
  let (result, state) := action.run.run { fuel, cap := fuel + 1 }
  (result, state.spent)

end LeanInformationAudit.RegistrationGates.ReadoutFamily

/-!
Occurrences are inferred in their original binder context at the existing native
work limit. An allowlist checks structural type families, specialized constructor
fields and explicit carrier projections. Independent proofs stop at the inferred
Prop boundary. Their implementations never enter executable provenance. Unknown
forms fail closed; exhausted work returns an incomplete closure. Reusable caches
contain declaration syntax only, while inferred types and verdicts are query-local.
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
-- date=2026-09-13; basis=bounded raw Lean allocation per native inference operation;
-- exit condition=the supported readout corpus or pinned Lean version changes,
-- then rerun real heartbeat-exhaustion and boundary fixtures. This is exempt
-- from capacity derivation because it is a correctness fail-closed limit.
def provenanceDefEqHeartbeats : Nat := 20000

register_option provenanceDefEqLimit : Nat := {
  defValue := provenanceDefEqHeartbeats
  descr := "Maximum raw heartbeats for native occurrence inference; legacy option name; zero is incomplete" }

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

-- A cached declaration contains only its typed roots. Children are requested
-- lazily after the occurrence boundary; no proof implementation is summarized.
private structure SyntaxNode where
  expr : Expr
  position : Position
  deriving Inhabited

private structure Summary where
  nodes : Array SyntaxNode := #[]
  roots : Array Nat := #[]
  visits : Nat := 0
  constructionWork : Nat := 0
  incomplete : Bool := false
  deriving Inhabited

private def summarise (_env : Environment) (inputs : Array (Position × Expr)) (fuel : Nat) :
    CoreM Summary := do
  if inputs.size > fuel then return { incomplete := true }
  let nodes := inputs.map fun (position, expr) => ({ expr, position } : SyntaxNode)
  return { nodes, roots := (List.range nodes.size).toArray, visits := nodes.size, constructionWork := nodes.size }

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
  familyMemoHits : Nat := 0
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
  currentFirst : Name := .anonymous
  currentOrigin : Name := .anonymous
  statement : Expr
  statementForms : Array Expr := #[]
  decision : Expr
  summaries : Std.HashMap (Name × List Level) Summary := {}
  counters : ProvenanceCounters := {}
  visited : Std.HashSet (Expr × Position × Array Expr) := {}
  walked : NameHashSet := {}
  queued : Std.HashSet (Name × List Level) := {}
  pending : List (Name × List Level) := []
  typeChecks : Std.HashMap (Expr × Array Expr) TypeClassification := {}
  forbidden : Bool := false
  unclassified : Option Unclassified := none
  incomplete : Bool := false
  weights : Std.HashMap (Expr × Bool) Nat := {}
  substitutionWeights : Std.HashMap (Expr × Nat) Nat := {}
  levelWeights : Std.HashMap Level Nat := {}
  applications : Std.HashMap Expr (Expr × Array Expr) := {}
  cleanTypes : Std.HashSet Expr := {}
  assumedFamilyDepth : Option Nat := none
  inferredTypes : Std.HashMap Expr Expr := {}
  cleanKinds : Std.HashSet Expr := {}
  certifiedNullaryCarriers : Std.HashSet Expr := {}
  dataFunctionTypes : Std.HashSet Expr := {}
  cleanFamilies : Std.HashSet (Expr × Expr) := {}
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
    trace[InformationProvenance.check] "incomplete cause=expression_budget operation=work_reservation first={(← get).currentFirst} site={(← get).currentOrigin}"
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
private partial def expressionWeight (e : Expr) (freeOnly : Bool := false) : WalkM (Option Nat) := do
  unless ← chargeTraversal do return none
  if let some n := (← get).weights[(e, freeOnly)]? then return some n
  let children := if freeOnly && !e.hasFVar then #[] else match e with
    | .app f a => #[f, a]
    | .lam _ t b _ | .forallE _ t b _ => #[t, b]
    | .letE _ t v b _ => #[t, v, b]
    | .mdata _ b | .proj _ _ b => #[b]
    | _ => #[]
  let mut weight := 1
  for child in children do
    let some n ← expressionWeight child freeOnly | return none
    weight := min (provenanceExpressionFuel + 1) (weight + n)
  let levels := if freeOnly then [] else match e with | .const _ ls => ls | .sort l => [l] | _ => []
  for level in levels do
    let some n ← levelWeight level | return none
    weight := min (provenanceExpressionFuel + 1) (weight + n)
  modify fun s => { s with weights := s.weights.insert (e, freeOnly) weight }
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
-- for their loose bound variables. Alias spellings only supply rejection witnesses.
-- Syntactic identity is only a rejection witness. A mismatch supplies no
-- admission: every candidate still passes the structural type-family rules.
private def compareCanonical (a b : Expr) : WalkM Bool := do
  unless ← chargeTraversal do return false
  -- Hash mismatch is a constant-time negative prefilter. Hash agreement is
  -- conservatively treated as a possible mention, never as proof of equality.
  return hash a == hash b ||
    (hash b == hash (← get).statement && (← get).statementForms.any (fun form => hash form == hash a))

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

-- Eligible instance heads still require the same structural fold over their
-- parameters and every constructor field. An unfamiliar class never inherits external-leaf
-- status from its module. In particular proof-carrying user classes are unclassified.
private def listedTypeClasses : Array Name := #[
  ``Decidable, ``OfNat, ``Inhabited, ``Subsingleton, ``Nonempty, ``BEq, ``LawfulBEq,
  `Fintype, `Finite, `NeZero, `Nat.AtLeastTwo,
  -- Collection and relation interfaces used by the frozen readout corpus.
  ``Membership, ``GetElem, ``GetElem?, ``Setoid, `SetLike, ``Singleton, ``Insert,
  `Append, `HAppend, `Union, `DFunLike, `EquivLike,
  ``Std.Associative, ``Std.Commutative,
  -- Scalar operator interfaces: their actual type parameters are checked too.
  ``Zero, ``One, ``Add, ``HAdd, ``Mul, ``HMul, ``Sub, ``HSub, ``Div, ``HDiv,
  ``Neg, ``Inv, ``Pow, ``HPow, ``Mod, ``HMod, ``LT, ``LE, ``NatPow,
  `Dvd, `NatCast, `IntCast, `AddSemigroup, `AddCommSemigroup, `AddMonoid,
  `AddCommMonoid, `AddMonoidWithOne, `AddGroup, `AddCommGroup, `AddGroupWithOne,
  `Semigroup, `CommSemigroup, `Monoid, `CommMonoid, `Group, `CommGroup,
  `MulZeroClass, `MulOneClass, `AddZeroClass, `Distrib, `LeftDistribClass,
  `RightDistribClass, `NonUnitalNonAssocSemiring, `NonUnitalSemiring,
  `NonAssocSemiring, `Semiring, `CommSemiring, `Ring, `CommRing,
  `NonUnitalNonAssocRing, `NonUnitalRing, `NonAssocRing,
  `CommMagma, `NonUnitalNonAssocCommSemiring, `NonUnitalCommSemiring,
  `NonAssocCommSemiring, `NonUnitalNonAssocCommRing, `NonUnitalCommRing, `NonAssocCommRing,
  `AddZero, `MulOne, `NSMul, `NPow, `ZSMul, `ZPow, `SMul, `VAdd,
  `SemigroupWithZero, `MonoidWithZero, `MulZeroOneClass, `AddCommMonoidWithOne,
  `AddCommGroupWithOne, `DivInvMonoid, `SubNegMonoid, `NegZeroClass, `InvOneClass,
  `Std.Symm, `Std.Irrefl, `ReflBEq, `Inter,
  `Preorder, `PartialOrder, `LinearOrder, `Ord, `Min, `Max,
  -- Division/cast interfaces retain checked scalar parameters and proof fields.
  `DivisionSemiring, `DivisionRing, `Semifield, `Field, `NNRatCast, `RatCast,
  `GroupWithZero, `CommGroupWithZero, `CommMonoidWithZero, `Nontrivial,
  `Fact, `CharP]

private def boundedMeta (action : MetaM α) (site : Name := `type_classification)
    (operations : Nat := 1) : WalkM (Option α) := do
  unless ← chargeSummaryWork (fun c => { c with canonicalizations := c.canonicalizations + operations }) operations do
    return none
  let budget := min provenanceDefEqHeartbeats (provenanceDefEqLimit.get (← getOptions))
  if budget == 0 then
    modify fun s => { s with incomplete := true }
    trace[InformationProvenance.check] "incomplete cause=heartbeat_exhaustion operation={site} first={(← get).currentFirst} site={(← get).currentOrigin}"
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
    modify fun s => { s with incomplete := true }
    trace[InformationProvenance.check] "incomplete cause={if ex.isMaxHeartbeat then "heartbeat_exhaustion" else "meta_runtime_exception"} operation={site} first={(← get).currentFirst} site={(← get).currentOrigin}"
    return none

-- This is the only source of types used for occurrence admission. Expressions
-- contain their actual levels and stable local identities; no inference cache
-- survives the registered-statement query. Failed inference is never cached.
private def occurrenceType (e : Expr) : WalkM (Option Expr) := do
  unless ← chargeTraversal do return none
  if e.hasLooseBVars || e.hasMVar || e.hasLevelMVar then
    noteUnclassified ⟨"unclassified_occurrence", `occurrence, "unclassified", `occurrence⟩
    return none
  if let some type := (← get).inferredTypes[e]? then return some type
  let some type ← boundedMeta (Meta.inferType e) `infer_type | return none
  modify fun s => { s with
    inferredTypes := s.inferredTypes.insert e type
    counters.inferredOccurrences := s.counters.inferredOccurrences + 1 }
  return some type

-- The frontend Nat literal is an audited representation, including its exact
-- native OfNat dictionary. A user-supplied dictionary is not a literal boundary.
private def naturalLiteral (e : Expr) : Option Nat := do
  if let some n := e.rawNatLit? then return n
  unless e.isAppOfArity ``OfNat.ofNat 3 do none
  let args := e.getAppArgs
  unless args[0]!.isConstOf ``Nat do none
  let n ← args[1]!.rawNatLit?
  unless args[2]! == mkInstOfNatNat (mkRawNatLit n) do none
  return n

-- A possible hash match is an unsupported mention, not evidence of a forbidden
-- dependency. Only these fixed scalar statement shapes establish an exact
-- proof boundary without comparing arbitrary expression trees.
private def scalarStatement (e : Expr) : Option (Name × Nat × Nat) := do
  if e.isConstOf ``True then return (``True, 0, 0)
  if e.isConstOf ``False then return (``False, 0, 0)
  unless e.isAppOfArity ``Eq 3 && e.getAppArgs[0]!.isConstOf ``Nat do none
  return (``Eq, ← naturalLiteral e.getAppArgs[1]!, ← naturalLiteral e.getAppArgs[2]!)

private def exactScalarStatement (e : Expr) : WalkM Bool := do
  unless ← chargeTraversal do return false
  let some shape := scalarStatement e | return false
  return (← get).statementForms.any (fun form => scalarStatement form == some shape)

-- Constructor telescopes are inferred from native occurrences. Only literal
-- constructor-index patterns are supported; no metavariables, equation solver,
-- dependent elimination, or semantic index normalization is used.
private partial def bindIndex (pattern actual : Expr)
    (bindings : Std.HashMap FVarId Expr) : WalkM (Option (Std.HashMap FVarId Expr)) := do
  unless ← chargeTraversal do return none
  match pattern with
  | .fvar id =>
    if let some previous := bindings[id]? then
      if previous != actual then return none
    return some (bindings.insert id actual)
  | _ =>
    if pattern == actual then return some bindings
    let some (ph, pa) ← applicationParts pattern | return none
    if ph.isConstOf ``id && pa.size == 2 then
      return ← bindIndex pa[1]! actual bindings
    if ph.isConstOf ``Nat.succ && pa.size == 1 then
      let literal := naturalLiteral actual
      if let some n := literal then
        if n == 0 then return none
        return ← bindIndex pa[0]! (mkNatLit (n - 1)) bindings
    let some (ah, aa) ← applicationParts actual | return none
    if ph != ah || pa.size != aa.size then return none
    let mut result := bindings
    for i in [:pa.size] do
      let some next ← bindIndex pa[i]! aa[i]! result | return none
      result := next
    return some result

private partial def constructorFields (ctor : Expr) (args : Array Expr)
    (parameters : Nat) (k : Array Expr → Expr → WalkM α)
    (fields : Array Expr := #[]) : WalkM (Option α) := do
  let some type ← occurrenceType ctor | return none
  match type with
  | .forallE n domain _ bi =>
    if parameters > 0 then
      let some arg := args[0]? | return none
      constructorFields (mkApp ctor arg) (args.extract 1 args.size) (parameters - 1) k fields
    else
      Meta.withLocalDecl n bi domain fun field =>
        constructorFields (mkApp ctor field) args 0 k (fields.push field)
  | _ => return some (← k fields type)

private def caseFields (type : Expr) :
    WalkM (Option (Array (LocalContext × LocalInstances × Array Expr))) := do
  let some (head, args) ← applicationParts type | return none
  let .const name levels := head | return none
  let some (.inductInfo family) := (← getEnv).find? name | return none
  let mut branches := #[]
  for ctor in family.ctors do
    unless ← chargeTraversal do return none
    let result ← constructorFields (mkConst ctor levels) args family.numParams fun fields result => do
      if fields.isEmpty then return some (← getLCtx, ← Meta.getLocalInstances, #[])
      let some (_, indices) ← applicationParts result | return none
      let mut bindings : Std.HashMap FVarId Expr := {}
      for i in [family.numParams:args.size] do
        let some pattern := indices[i]? | return none
        let some next ← bindIndex pattern args[i]! bindings | return none
        bindings := next
      -- Only substitute already fixed index binders, never solve new equations.
      let mut actualFields := #[]
      let mut lctx ← getLCtx
      for field in fields do
        let some fieldType ← occurrenceType field | return none
        unless ← chargeExpression fieldType do return none
        let fieldType := fieldType.replace fun e => match e with
          | .fvar id => bindings[id]?
          | _ => none
        let id ← mkFreshFVarId
        lctx := lctx.mkLocalDecl id `field fieldType
        actualFields := actualFields.push (mkFVar id)
      return some (lctx, ← Meta.getLocalInstances, actualFields)
    let some result := result | return none
    -- A constructor with a distinct literal index has no fields at this index.
    if let some branch := result then branches := branches.push branch
    else if family.numIndices > 0 then
      -- Unknown index patterns do not justify a clean nominal boundary.
      return none
  modify fun s => { s with counters.caseExpansions := s.counters.caseExpansions + 1 }
  return some branches

-- A recognized representation alias forwards its actual arguments through its
-- explicit lambda telescope. It does not evaluate a computed data expression.
private partial def aliasBody (value : Expr) (args : Array Expr) : WalkM (Option Expr) := do
  unless ← chargeTraversal do return none
  if args.isEmpty then return some value
  match value with
  | .lam _ _ body _ =>
    let some body ← substitute body #[args[0]!] | return none
    aliasBody body (args.extract 1 args.size)
  | .mdata _ body => aliasBody body args
  | _ =>
    unless ← chargeTraversal args.size do return none
    return some (mkAppN value args)

private partial def representationType (type : Expr) : WalkM (Option Expr) := do
  unless ← chargeTraversal do return none
  match type with
  | .mdata _ body => representationType body
  | .fvar id =>
    let some value := (← id.getDecl).value? (allowNondep := true) | return some type
    representationType value
  | _ => return some type

-- Decode only an explicit record projection. The receiver must expose a
-- constructor of the projection's own structure; computed recursors stay opaque.
private def statementStep (env : Environment) (current : Expr) : WalkM (Option Expr) := do
  let some (head, args) ← applicationParts current | return none
  match head with
  | .const n levels =>
    let some (.defnInfo info) := env.find? n | return none
    let value ← Core.instantiateValueLevelParams (.defnInfo info) levels
    aliasBody value args
  | .lam .. =>
    if args.isEmpty then return none
    aliasBody head args
  | .mdata _ body => return some (mkAppN body args)
  | .letE _ _ value body _ =>
    let some body ← substitute body #[value] | return none
    aliasBody body args
  | .proj structureName index receiver =>
    let (record, work) := ReadoutFamily.carrier env receiver (← get).exprFuel
    unless ← chargeTraversal work do return none
    let some record := record | return none
    let some (ctor, fields) ← applicationParts record | return none
    let some (.ctorInfo info) := ctor.constName?.bind env.find? | return none
    unless info.induct == structureName do return none
    let some field := fields[info.numParams + index]? | return none
    aliasBody field args
  | _ => return none

private partial def statementOuter (env : Environment) (type : Expr) : WalkM (Option Expr) := do
  unless ← chargeTraversal do return none
  if type.getAppFn.isConstOf `Multiset.Mem then return some type
  let some next ← statementStep env type | return some type
  if next == type then return none
  statementOuter env next

-- Equality-only List metadata has recursive List premises and disequalities
-- ending in False. These explicit positive conclusions, or negations of known
-- non-equality heads, cannot be those premises. Unknown predicate heads stop.
private partial def listStatementBoundary (env : Environment) (type : Expr)
    (binders : Nat := 0) : WalkM Bool := do
  let some type ← statementOuter env type | return false
  match type with
  | .forallE n domain body bi =>
    if binders == 0 then
      let some firstProof ← boundedMeta (Meta.isProp domain) `list_statement_domain | return false
      if !firstProof then
        let twoDataBinders ← Meta.withLocalDecl n bi domain fun x => do
          let some body ← substitute body #[x] | return false
          let some body ← statementOuter env body | return false
          let .forallE _ secondDomain _ _ := body | return false
          let some secondProof ← boundedMeta (Meta.isProp secondDomain) `list_statement_domain
            | return false
          return !secondProof
        if twoDataBinders then return true
    if body.isConstOf ``False then
      let some domain ← statementOuter env domain | return false
      return domain.isForall || domain.getAppFn.constName?.any
        (#[``Exists, ``And, ``Or, ``List.Mem, `Multiset.Mem].contains ·)
    Meta.withLocalDecl n bi domain fun x => do
      let some body ← substitute body #[x] | return false
      listStatementBoundary env body (binders + 1)
  | _ =>
    let name := type.getAppFn.constName?.getD .anonymous
    return #[``And, ``Or, ``Exists, ``True, ``Eq, ``HEq, ``Nat.le].contains name ||
      (binders > 0 && #[``List.Mem, `Multiset.Mem].contains name)

-- Pure data carriers for equality-only collection metadata. The surrounding
-- type fold has already checked actual parameters and statement-bearing fields.
-- Nominal carriers with proof/type-valued fields are excluded here; intrinsic
-- scalar bounds and quotient containers have explicit representation boundaries.
private partial def dataCarrier (env : Environment) (type : Expr)
    (active : Array Expr := #[]) : WalkM Bool := do
  unless ← chargeTraversal do return false
  let some type ← representationType type | return false
  let some kind ← occurrenceType type | return false
  let .sort level := kind | return false
  unless level.isNeverZero do return false
  match type with
  | .sort _ => return false
  | .fvar id => return (← id.getDecl).value? (allowNondep := true) |>.isNone
  | .forallE n domain body bi =>
    unless ← dataCarrier env domain active do return false
    Meta.withLocalDecl n bi domain fun x => do
      let some body ← substitute body #[x] | return false
      dataCarrier env body active
  | _ =>
    let some (head, args) ← applicationParts type | return false
    let .const name levels := head | return false
    if #[``Nat, ``Int, `Rat, ``Fin, `ZMod].contains name then return true
    if #[``List, `Multiset, `Finset].contains name && args.size == 1 then
      return ← dataCarrier env args[0]! active
    if name == ``Subtype && args.size == 2 then
      return ← dataCarrier env args[0]! active
    if active.contains type then return false
    if let some (.defnInfo info) := env.find? name then
      let value ← Core.instantiateValueLevelParams (.defnInfo info) levels
      let some body ← aliasBody value args | return false
      return ← dataCarrier env body (active.push type)
    let some branches ← caseFields type | return false
    for (lctx, instances, fields) in branches do
      for field in fields do
        let clean ← Meta.withLCtx lctx instances do
          let some fieldType ← occurrenceType field | return false
          dataCarrier env fieldType (active.push type)
        unless clean do return false
    return true

-- Record explicit proposition-alias spellings only as rejection witnesses.
-- These hashes never certify non-mention and never normalize data operands.
private def statementAliases (env : Environment) : WalkM Unit := do
  let mut current := (← get).statement
  let mut seen : Std.HashSet UInt64 := {}
  repeat
    unless ← chargeTraversal do return
    if seen.contains (hash current) then
      modify fun s => { s with incomplete := true }
      return
    seen := seen.insert (hash current)
    modify fun s => { s with statementForms := s.statementForms.push current }
    let some body ← statementStep env current | return
    current := body

-- The final supported outer spelling is used for structural family fences.
-- Computed operands remain untouched and cannot establish non-mention.
private def statementBoundary : WalkM Expr := do
  let state ← get
  return state.statementForms.back?.getD state.statement

-- A carrier alias is supported only when its explicit body is another named
-- type application. This recognizes Unit/PUnit without evaluating data or
-- admitting arbitrary computed carriers. The ordinary type fold still checks
-- every parameter and nominal field before this narrower List boundary is used.
private partial def namedCarrier (env : Environment) (type : Expr) : WalkM (Option Expr) := do
  unless ← chargeTraversal do return none
  let some type ← representationType type | return none
  let .const name levels := type.getAppFn | return some type
  let some (.defnInfo info) := env.find? name | return some type
  let value ← Core.instantiateValueLevelParams (.defnInfo info) levels
  let some body ← aliasBody value type.getAppArgs | return none
  unless body.getAppFn.isConst do return some type
  if body == type then return none
  namedCarrier env body

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
      Meta.withLetDecl n t v (fun _ => next (locals.push v)) (nondep := nd)
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
private def typeMentions (env : Environment) (e : Expr) : WalkM Bool := do
  unless ← chargeSummaryWork (fun c => { c with recheckedNodes := c.recheckedNodes + 1 }) do return false
  if let .const n _ := e.getAppFn then directConstant env n
  if let .proj n _ _ := e.getAppFn then directProjection env n
  return ← compareCanonical e (← get).statement

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
-- Nominal fields are native occurrences specialized by constructor-index patterns.
private partial def inputType (env : Environment) (type : Expr)
    (active : Array Expr := #[]) : WalkM (Bool × Bool) := do
  unless ← chargeSummaryWork (fun c => { c with recheckedNodes := c.recheckedNodes + 1 }) do
    return (false, true)
  if type.hasLooseBVars || type.hasMVar || type.hasLevelMVar then return (false, true)
  if ReadoutFamily.carrierHeads.contains (type.getAppFn.constName?.getD .anonymous) then
    let (decoded, work) := ReadoutFamily.carrier env type (← get).exprFuel
    unless ← chargeTraversal work do return (false, true)
    let some decoded := decoded | return (false, true)
    if decoded == type then return (false, true)
    return ← inputType env decoded active
  let key := type
  if (← get).cleanTypes.contains key then return (false, false)
  unless ← chargeTraversal do return (false, true)
  let enclosingAssumptions := (← get).assumedFamilyDepth
  modify fun s => { s with assumedFamilyDepth := none }
  let classify : WalkM (Bool × Bool) := do
    -- Recursive occurrences recheck their actual arguments before using an
    -- enclosing-family assumption.
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
    let some reduced ← representationType type | do
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
      if let .lam .. := head then
        let some body ← aliasBody head args | return (mentions, true)
        let (bm, bu) ← inputType env body active
        return (mentions || bm, bu)
      let mut unclassified := false
      for arg in args do
        if let .const n _ := arg.getAppFn then directConstant env n
        if let .proj n _ _ := arg.getAppFn then directProjection env n
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
      directProjection env name
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
      let statement ← statementBoundary
      let natOrder := fun e =>
        let h := e.getAppFn
        h.isConstOf ``Nat.le || h.isConstOf ``Nat.lt ||
          ((h.isConstOf ``LE.le || h.isConstOf ``LT.lt) &&
            e.getAppArgs[0]?.any (·.isConstOf ``Nat))
      if natOrder reduced && natOrder statement then return (mentions, true)
      -- Membership of propositions is not a data-carrier boundary. Inspect
      -- the actual receiver carrier even when the interface projection is stuck.
      if name == ``Membership.mem && args.size >= 2 then
        let element := args[0]!
        if element == .sort .zero then return (mentions, true)
      -- Equality has no independent payload: reflexivity carries only the
      -- operands already checked above. Eliminating an arbitrary equality
      -- would instead ask Lean to solve a theorem (e.g. f x = x).
      if name == ``Eq || name == ``HEq then
        -- Closed computed operands on either side are outside the equality boundary when the
        -- registered statement is an equality. A raw spelling mismatch cannot
        -- certify that a numeric/record alias differs from that statement.
        let inductiveHead := fun e => e.getAppFn.constName?.filter fun n =>
          (env.find? n).any (fun info => match info with | .inductInfo _ => true | _ => false)
        let distinctCarriers := if args.size == 3 && statement.isAppOfArity ``Eq 3 then
          let a := args[0]!
          let b := statement.getAppArgs[0]!
          match inductiveHead a, inductiveHead b with
          | some a, some b => a != b
          | none, some _ => a.isForall || a.isSort
          | some _, none => b.isForall || b.isSort
          | _, _ => false
        else false
        if name == ``Eq && args.size == 3 && statement.isAppOfArity ``Eq 3 && !distinctCarriers then
          for operand in args.extract 1 3 ++ statement.getAppArgs.extract 1 3 do
            let literal := (naturalLiteral operand).isSome
            let nullary := match operand with
              | .const n _ => (env.find? n).any fun info => match info with
                | .ctorInfo ctor => ctor.numFields == 0 && ctor.numParams == 0
                | _ => false
              | _ => false
            if closed operand && !literal && !nullary then
              trace[InformationProvenance.check] "unsupported_equality_operand={repr operand} type={reduced}"
              unclassified := true
        return (mentions, unclassified)
      -- Nat.le has only natural indices and recursive Nat.le premises. Check
      -- the actual operands above; if S is itself an order statement, reject
      -- conservatively so no recursive order subproof can conceal it. This
      -- avoids enumerating numeric representation bounds (UInt32, Char, ...).
      if name == ``Nat.le then
        let some statement ← representationType (← statementBoundary)
          | return (mentions, true)
        let head := statement.getAppFn
        let order := head.isConstOf ``Nat.le || head.isConstOf ``Nat.lt ||
          ((head.isConstOf ``LE.le || head.isConstOf ``LT.lt) &&
            statement.getAppArgs[0]?.any (·.isConstOf ``Nat))
        return (mentions, unclassified || order)
      -- Membership and uniqueness proofs over checked data carriers contain
      -- only recursive Mem/Pairwise and equality/function proof forms. The
      -- positive statement heads below cannot specialize to those forms.
      if (name == ``List.Pairwise || name == ``List.Mem) && args.size == 3 then
        let some kind ← occurrenceType args[0]! | return (mentions, true)
        let some (.sort level) ← representationType kind
          | return (mentions, true)
        let relation := mkApp (mkConst ``Ne [level]) args[0]!
        let some carrier ← namedCarrier env args[0]! | return (mentions, true)
        let some rigid ← boundedMeta (do
          let carrier ← pure carrier
          let .fvar id := carrier | return false
          return (← id.getDecl).value? (allowNondep := true) |>.isNone) `carrier_rigidity
          | return (mentions, true)
        -- A rigid parameter is scoped to this occurrence. Applications and
        -- enclosing case substitutions get freshly inferred field types.
        let mut carrierAllowed := rigid || (carrier.isConstOf ``Nat) || (← dataCarrier env args[0]!)
        if !carrierAllowed && level.isNeverZero then
          let some carrier ← representationType carrier
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
                carrierAllowed := branches.all (fun (_, _, fields) => fields.isEmpty)
                if carrierAllowed then
                  unless ← chargeTraversal do return (mentions, true)
                  modify fun s => { s with certifiedNullaryCarriers :=
                    s.certifiedNullaryCarriers.insert carrier }
        let relationAllowed := args[1]! == relation || match args[1]! with
          | .lam _ _ (.lam _ _ body _) _ =>
            body.isAppOfArity ``Ne 3 && body.getAppArgs[1]! == .bvar 1 &&
              body.getAppArgs[2]! == .bvar 0
          | _ => false
        if carrierAllowed && (name == ``List.Mem || relationAllowed) then
          let some statement ← representationType (← statementBoundary)
            | return (mentions, true)
          let disjoint ← listStatementBoundary env statement
          if disjoint then return (mentions, unclassified)
        trace[InformationProvenance.check] "unsupported_list_boundary type={reduced} carrier={carrier} allowed={carrierAllowed} relation={relationAllowed}"
        return (mentions, true)
      if Lean.isClass env name && !listedTypeClasses.contains name then
        trace[InformationProvenance.check] "unsupported_class={name} type={type}"
        return (mentions, true)
      -- Quotient carriers and lifted type families expose their relation or
      -- predicate to the same argument classifier; no predicate is a leaf.
      if let some (.quotInfo info) := env.find? name then
        if match info.kind with | .type | .lift => true | _ => false then
          return (mentions, unclassified)
      if let some (.recInfo _) := env.find? name then return (mentions, unclassified)
      if let some (.defnInfo _) := env.find? name then
        -- An explicit type alias forwards its actual parameters. Its raw body
        -- must pass the same structural families; computed data is not evaluated.
        let value ← Core.instantiateValueLevelParams declaration head.constLevels! (allowOpaque := false)
        let some unfolded ← aliasBody value args | return (mentions, true)
        if unfolded == reduced then return (mentions, true)
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
            sameParameters := (a == b) && sameParameters
          let mut coveredIndices := true
          for index in [info.numParams:args.size] do
            unless ← chargeTraversal do return (mentions, true)
            let current := args[index]!
            -- Recursive occurrences with fresh indices share the enclosing
            -- family obligation. Concrete changed indices require fresh cases.
            if current.hasFVar then
              let some normalized ← representationType current | return (mentions, true)
              if normalized.hasFVar then continue
            let some previous := previousArgs[index]? | return (mentions, true)
            coveredIndices := (previous == current) && coveredIndices
          if sameParameters && coveredIndices then
            noteFamilyAssumption depth
            return (mentions, unclassified)
          -- Different parameters are a fresh obligation, as in nested products.
      let some branches ← caseFields reduced | do
        trace[InformationProvenance.check] "unsupported_nominal_fields type={reduced}"
        return (mentions, true)
      unless ← chargeTraversal (active.size + 1) do return (mentions, true)
      let nextActive := active.push reduced
      for (lctx, instances, fields) in branches do
        unless ← chargeTraversal do return (mentions, true)
        for field in fields do
          unless ← chargeTraversal do return (mentions, true)
          let (fm, fu) ← Meta.withLCtx lctx instances do
            let some fieldType ← occurrenceType field | return (false, true)
            inputType env fieldType nextActive
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
  let canCache := #[value, type].all fun e =>
    !e.hasLooseBVars && !e.hasMVar && !e.hasLevelMVar
  if canCache && (← get).cleanFamilies.contains (value, type) then
    modify fun s => { s with counters.familyMemoHits := s.counters.familyMemoHits + 1 }
    return some (false, false)
  let enclosing := (← get).assumedFamilyDepth
  modify fun s => { s with assumedFamilyDepth := none }
  let inspect : WalkM (Option (Bool × Bool)) := do
    let some reduced ← representationType type | return some (false, true)
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
  let state ← get
  modify fun s => { s with assumedFamilyDepth := mergeAssumptions enclosing state.assumedFamilyDepth }
  -- This fold opens no family frame: every surviving assumption is external.
  if canCache && result == some (false, false) && state.assumedFamilyDepth.isNone &&
      !state.incomplete && !state.forbidden && state.unclassified.isNone then
    unless ← chargeTraversal do return some (false, true)
    modify fun s => { s with cleanFamilies := s.cleanFamilies.insert (value, type) }
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
    let exact ← exactScalarStatement type
    let decision ← if type.isAppOfArity ``Decidable 1 then
        exactScalarStatement type.getAppArgs[0]! else pure false
    let (mentions, unclassified) ← inputType env type
    if exact || decision then return .forbidden
    if mentions then return .statementMention
    let state ← get
    if state.forbidden then return .forbidden
    if state.incomplete then return .incomplete
    if state.unclassified.isSome then return .unclassified
    if unclassified then return .unclassified
    return .allowlisted
  let verdict := verdict.getD (if (← get).incomplete then .incomplete else .unclassified)
  unless ← chargeTraversal context.size do return .incomplete
  modify fun s => { s with typeChecks := s.typeChecks.insert key verdict }
  return verdict

-- Check a node before requesting its children. Independent Prop proofs are
-- leaves after identity and inferred-type checks; their bodies are never cached
-- or traversed. Type-valued decision dictionaries remain executable nodes.
private partial def visitOccurrence (env : Environment) (pos : Position)
    (origin : Name) (e : Expr) (context : Array Expr := #[]) : WalkM Unit := do
  unless ← chargeSummaryWork (fun c => { c with dispatchWork := c.dispatchWork + 1 }) do return
  let first := e.getAppFn.constName?.getD origin
  modify fun s => { s with currentFirst := first, currentOrigin := origin }
  if let .const n _ := e.getAppFn then directConstant env n
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
    if decoded == some true then return
  let key := (e, pos, context)
  if (← get).visited.contains key then return
  modify fun s => { s with visited := s.visited.insert key }
  let verdict ← classifyOccurrence env e context
  match verdict with
  | .forbidden => modify fun s => { s with forbidden := true }; return
  | .statementMention => noteUnclassified ⟨"statement_mentioning_type", first, namespaceLabel env first, origin⟩
  | .unclassified => noteUnclassified ⟨"unclassified_argument_type", first, namespaceLabel env first, origin⟩
  | .incomplete => modify fun s => { s with incomplete := true }; return
  | .allowlisted => pure ()
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
      let (mentions, unknown) ← inputType env actual
      if mentions then
        noteUnclassified ⟨"statement_mentioning_type", first, namespaceLabel env first, origin⟩
      if unknown then
        noteUnclassified ⟨"unclassified_argument_type", first, namespaceLabel env first, origin⟩
      return true
    let some proof ← boundedMeta (Meta.isProp type) `proof_boundary | return false
    return proof
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
    if (env.find? n).isNone then modify fun s => { s with incomplete := true }
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
  | .mvar _ => modify fun s => { s with incomplete := true }
  | _ => pure ()

private def visitSummary (env : Environment) (origin : Name) (summary : Summary) : WalkM Unit := do
  if summary.incomplete then modify fun s => { s with incomplete := true }
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
      modify fun s => { s with incomplete := true }
      break
    let some info := env.find? n.1 | modify fun s => { s with incomplete := true }; continue
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
    statementAliases env
    visit env .dataPos address readout
    process env
  let budget := min provenanceExpressionFuel (provenanceExpressionLimit.get (← getOptions))
  let (_, state) ← Meta.MetaM.run' <| computation.run {
    theoremName, statement, decision, summaries := summaryCache.getState env, exprFuel := budget }
  let counters := { state.counters with chargedVisits := budget - state.exprFuel }
  modifyEnv (summaryCache.setState · state.summaries)
  modifyEnv (countersCache.setState · counters)
  trace[InformationProvenance.check]
    "theorem={theoremName} P_constants_summarised={counters.summarisedConstants} visits={counters.visits} memo_hits={counters.memoHits} charged_visits={counters.chargedVisits} rechecked_nodes={counters.recheckedNodes} spine_arguments={counters.spineArguments} canonicalizations={counters.canonicalizations} construction_work={counters.constructionWork} traversal_work={counters.traversalWork} dispatch_work={counters.dispatchWork} inferred_occurrences={counters.inferredOccurrences} case_expansions={counters.caseExpansions} family_memo_hits={counters.familyMemoHits}"
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
  if r.incomplete then return (false, none)
  if r.forbidden || r.unclassified.isSome then return (true, some r.walked)
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
  let reason := if result.incomplete then "incomplete_closure"
    else if result.forbidden then "forbidden_dependency" else "unclassified_form"
  let payload := if result.incomplete then Json.null
    else if result.forbidden then Json.arr (result.walked.map Json.str)
    else if let some u := result.unclassified then unclassifiedJson u result.walked
    else Json.null
  return some s!"IE-C050 ClosedTruthReadout key={root}/{catalog}/{theoremName} readout={address} reason={reason} provenance={payload.compress}"

def provenanceError (env : Environment) (root catalog theoremName realization : Name) : CoreM (Option String) :=
  withEnv env (provenanceErrorCurrent root catalog theoremName realization)

end LeanInformationAudit.RegistrationGates
