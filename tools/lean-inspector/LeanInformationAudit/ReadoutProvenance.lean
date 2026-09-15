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
  `D5.S3.ConceptDynamics.CIRPT.PrimitiveBundle.Index,
  `D5.S3.ConceptDynamics.InformationEscape.Catalog.Index,
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
  `LeanInformationAudit.TemplateAudit.selectedPlan,
  `LeanInformationAudit.TemplateAudit.observeSelectedPlan,
  `LeanInformationAudit.TemplateAudit.importedSummaryBytes,
  `LeanInformationAudit.TemplateBinding.inventory,
  `LeanInformationAudit.TemplateBinding.records,
  `LeanInformationAudit.TemplateBinding.cachedJoinedRecords,
  `LeanInformationAudit.TemplateBinding.assessJoined,
  `LeanInformationAudit.TemplateBinding.exportSnapshot,
  `LeanInformationAudit.TemplateBinding.observedAssessments,
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
      `LeanInformationAudit.TemplateAudit.TemplatePlanData,
      `LeanInformationAudit.TemplateAudit.TemplatePlanFrame,
      `LeanInformationAudit.TemplateAudit.TemplateIndex,
      `LeanInformationAudit.TemplateAudit.DependencyIdentity,
      `LeanInformationAudit.TemplateOccurrenceKey, `LeanInformationAudit.TemplateOccurrenceEvent,
      `LeanInformationAudit.TemplateBindingCertificate, `LeanInformationAudit.TemplateBindingResult,
      `LeanInformationAudit.BindingRecord, `LeanInformationAudit.TemplateBindingClaim,
      `LeanInformationAudit.TemplateBinding.JoinedRecords,
      `LeanInformationAudit.AutoDerivedSemanticCertificate,
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

/-- Raw judge identities are rejection witnesses shared by enrollment and
occurrence auditing. A negative answer grants no grammar admission. -/
def isJudgeIdentity (env : Environment) (name : Name) : Bool :=
  provenanceJudgeAPIs.contains name || generatedAddress name || judgePayloadType name ||
    (env.find? name).any judgePayload ||
    ((env.getProjectionFnInfo? name).bind (fun p => env.find? p.ctorName)).any judgePayload

/-- A raw projection names its structure, rather than its projection function. -/
def isJudgeProjection (name : Name) : Bool :=
  provenanceJudgeAPIs.contains name || generatedAddress name || judgePayloadType name

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

-- These producers expose their implementations or have kernel-controlled
-- computation rules. Arbitrary external definitions have no such permission.
private def carrierProducerAllowed (env : Environment) (name : Name) : Bool :=
  inProtected env name || isCtorOrInductive env name || name == ``Nat.brecOn

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

/-- Every successful type decision identifies a reviewed rule and its actual
head/type. There is deliberately no default/unknown admission constructor. -/
inductive ProvenanceAllowRule where
  | statementInductive | statementForall | statementMembership
  | telescope | letType | lambdaType | metadataType | sortKind | betaType
  | scopedParameter | auditedProjection | equality | naturalOrder | listMetadata
  | quotientType | recursorType | enumRecursorType | aliasType | recursiveFamily | nominalFields
  | ordinaryData | typeFamily | scalarCarrier | rigidCarrier | functionCarrier
  | containerCarrier | subtypeCarrier | nullaryCarrier | nominalCarrier
  | fieldProposition | fieldConcrete | fieldParameter | fieldFunction | fieldAlias | fieldAudited
  | statementHeadApart | statementLiteralApart | statementDomainApart
  | statementBodyApart | statementArgumentApart | statementRigidApart | statementMetadataApart
  | proofBoundary | propositionBoundary | externalLeaf | syntaxLeaf
  | listForall | listNegated | listPositive | carrierAlias | carrierProjection
  deriving BEq, Repr

structure ProvenanceAdmissionWitness where
  rule : ProvenanceAllowRule
  matchedHead : Expr
  matchedType : Expr
  sourceDependency : Option Name := none

private inductive TypeClassification where
  | allowlisted (witness : ProvenanceAdmissionWitness)
  | statementMention
  | forbidden
  | unclassified (site : Unclassified)
  | incomplete

private instance : Inhabited TypeClassification := ⟨.incomplete⟩

private def TypeClassification.flags : TypeClassification → Bool × Bool
  -- admission-exit: TypeClassification.flags.forward.1 rule=retained-witness.rule
  | .allowlisted _ => (false, false)
  | .statementMention | .forbidden => (true, false)
  | .unclassified _ | .incomplete => (false, true)

private def TypeClassification.witness? : TypeClassification → Option ProvenanceAdmissionWitness
  -- admission-exit: TypeClassification.witness?.forward.1 rule=retained-witness.rule
  | .allowlisted witness => some witness
  | _ => none

private inductive FamilyClassification where
  | data (witness : ProvenanceAdmissionWitness)
  | family (verdict : TypeClassification)

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
  recognizedStatement : Option ProvenanceAdmissionWitness := none
  decision : Expr
  summaries : Std.HashMap (Name × List Level) Summary := {}
  counters : ProvenanceCounters := {}
  visited : Std.HashSet (Expr × Position × Array Expr) := {}
  walked : NameHashSet := {}
  /-- Raw constant occurrences, including independent proof heads. Retaining
  their identity does not queue or inspect a proof implementation. -/
  retainedInputs : NameHashSet := {}
  queued : Std.HashSet (Name × List Level) := {}
  pending : List (Name × List Level) := []
  typeChecks : Std.HashMap (Expr × Array Expr × Name) TypeClassification := {}
  forbidden : Bool := false
  unclassified : Option Unclassified := none
  incomplete : Bool := false
  weights : Std.HashMap (Expr × Bool) Nat := {}
  substitutionWeights : Std.HashMap (Expr × Nat) Nat := {}
  levelWeights : Std.HashMap Level Nat := {}
  applications : Std.HashMap Expr (Expr × Array Expr) := {}
  cleanTypes : Std.HashMap (Expr × Option Name) ProvenanceAdmissionWitness := {}
  apartPropositions : Std.HashMap Expr ProvenanceAdmissionWitness := {}
  identityFailureTraced : Bool := false
  identityUnknown : Option Unclassified := none
  assumedFamilyDepth : Option Nat := none
  assumedProducer : Option Name := none
  inferredTypes : Std.HashMap Expr Expr := {}
  cleanKinds : Std.HashMap (Expr × Option Name) ProvenanceAdmissionWitness := {}
  certifiedNullaryCarriers : Std.HashMap Expr ProvenanceAdmissionWitness := {}
  dataFunctionTypes : Std.HashMap (Expr × Option Name) ProvenanceAdmissionWitness := {}
  cleanFamilies : Std.HashMap (Expr × Expr × Option Name) ProvenanceAdmissionWitness := {}
  binderContexts : Std.HashMap (Array Expr) (LocalContext × LocalInstances × Array Expr) := {}
  exprFuel : Nat := provenanceExpressionFuel
  constFuel : Nat := provenanceConstantFuel

private abbrev WalkM := StateRefT WalkState MetaM

private def noteIncomplete (cause operation : Name) : WalkM Unit := do
  modify fun s => { s with incomplete := true }
  trace[InformationProvenance.check]
    "incomplete cause={cause} operation={operation} first={(← get).currentFirst} site={(← get).currentOrigin}"

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

private def witness (rule : ProvenanceAllowRule) (type : Expr) : ProvenanceAdmissionWitness :=
  ⟨rule, type.getAppFn, type, none⟩

-- Cache only the exact dependency that justified a producer-sensitive rule.
-- Most types have no such dependency and remain reusable at every occurrence.
-- A source name is occurrence data, never a caller-selectable classification mode.
private def reuseWitness (cache : Std.HashMap (Expr × Option Name) ProvenanceAdmissionWitness)
    (type : Expr) : WalkM (Option ProvenanceAdmissionWitness) := do
  let source := (← get).currentFirst
  let found := cache[(type, (none : Option Name))]?.orElse fun _ => cache[(type, some source)]?
  let found := found.filter fun evidence => evidence.sourceDependency.all (· == source)
  if let some evidence := found then
    modify fun s => { s with assumedProducer := s.assumedProducer.or evidence.sourceDependency }
  -- admission-exit: reuseWitness.1 rule=retained-witness.rule
  return found

private def bindWitnessSource (verdict : TypeClassification) (source : Option Name) :
    TypeClassification := match verdict with
  -- admission-exit: bindWitnessSource.forward.1 rule=retained-witness.rule
  | .allowlisted evidence => .allowlisted { evidence with sourceDependency := source }
  | other => other

private def unknownType (type : Expr) (className : String := "unclassified_argument_type") :
    WalkM TypeClassification := do
  let state ← get
  let first := if state.currentFirst.isAnonymous then
    type.getAppFn.constName?.getD state.theoremName else state.currentFirst
  return .unclassified ⟨className, first, namespaceLabel (← getEnv) first, state.currentOrigin⟩

-- A rule discharges a structural obligation only when every child was
-- classified. Rejection flags are projections of typed child verdicts; a
-- failed branch can never supply the witness accepted by the caller or memo.
private def checkedType (rule : ProvenanceAllowRule) (type : Expr)
    (mentions unknown : Bool) : WalkM TypeClassification := do
  if mentions then return .statementMention
  if unknown then return ← unknownType type
  -- admission-exit: checkedType.1 rule=retained-witness.rule
  return .allowlisted (witness rule type)

private def queue (name : Name) (levels : List Level) : WalkM Unit := do
  let n := (name, levels)
  let s ← get
  if s.queued.contains n then return
  if s.constFuel == 0 then
    trace[InformationProvenance.check] "incomplete cause=constant_budget operation=constant_enqueue first={name} site={s.currentOrigin}"
    modify fun s => { s with incomplete := true }
  else
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
  if n == (← get).theoremName || isJudgeIdentity env n then
    modify fun s => { s with forbidden := true, walked := s.walked.insert n }

private def directProjection (env : Environment) (n : Name) : WalkM Unit := do
  if isJudgeProjection n then
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
  let some recognized := (← get).recognizedStatement | return false
  return scalarStatement recognized.matchedType == some shape

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

-- A field role needs a positive spelling: kind alone cannot distinguish a
-- carrier slot from an ordinary value. Explicit aliases are followed before
-- deciding the role; no recursor or opaque carrier is evaluated. These witnesses
-- discharge only the role check. observedType still checks all parameters,
-- proof identities and nominal fields of the recognized value type.
private partial def nominalFieldShape (env : Environment) (type : Expr)
    (parameters : Array Expr) : WalkM (Option ProvenanceAdmissionWitness) := do
  let some concrete ← representationType type | return none
  let some kind ← occurrenceType concrete | return none
  if kind == .sort .zero then
    -- admission-exit: nominalFieldShape.1 rule=fieldProposition
    return some (witness .fieldProposition concrete)
  match concrete with
  | .sort _ => return none
  | .forallE n domain body bi =>
    let result ← Meta.withLocalDecl n bi domain fun x => do
      let some body ← substitute body #[x] | return none
      -- admission-exit: nominalFieldShape.forward.1 rule=retained-witness.rule
      nominalFieldShape env body parameters
    if result.isNone then return none
    -- admission-exit: nominalFieldShape.2 rule=fieldFunction
    return some (witness .fieldFunction concrete)
  | .letE _ _ value body _ =>
    let some body ← substitute body #[value] | return none
    let some _ ← nominalFieldShape env body parameters | return none
    -- admission-exit: nominalFieldShape.3 rule=fieldAlias
    return some (witness .fieldAlias concrete)
  | _ =>
    let some (head, args) ← applicationParts concrete | return none
    unless ← chargeTraversal parameters.size do return none
    -- Supplied parameters can be projections or instantiated types, not only
    -- local variable heads. This witnesses their role; observedType still
    -- checks the entire instantiated parameter for statement-bearing inputs.
    if parameters.contains concrete || (head.isFVar && parameters.contains head) then
      -- admission-exit: nominalFieldShape.4 rule=fieldParameter
      return some (witness .fieldParameter concrete)
    if let .lam .. := head then
      let some body ← aliasBody head args | return none
      let some _ ← nominalFieldShape env body parameters | return none
      -- admission-exit: nominalFieldShape.5 rule=fieldAlias
      return some (witness .fieldAlias concrete)
    let .const name levels := head | return none
    let some declaration := env.find? name | return none
    match declaration with
    | .inductInfo _ | .quotInfo _ =>
      -- admission-exit: nominalFieldShape.6 rule=fieldConcrete
      return some (witness .fieldConcrete concrete)
    | .defnInfo _ =>
      let value ← Core.instantiateValueLevelParams declaration levels (allowOpaque := false)
      let some body ← aliasBody value args | return none
      if body == concrete then return none
      let some _ ← nominalFieldShape env body parameters | return none
      -- admission-exit: nominalFieldShape.7 rule=fieldAlias
      return some (witness .fieldAlias concrete)
    | _ => return none

-- Decode only an explicit record projection. The receiver must expose a
-- constructor of the projection's own structure; computed recursors stay opaque.
private inductive StatementStep where
  | next (expression : Expr)
  | recognized (evidence : ProvenanceAdmissionWitness)
  | unclassified (site : Unclassified)
  | incomplete

private def statementUnknown (head : Expr) : WalkM StatementStep := do
  let name := head.constName?.getD (match head with
    | .proj structureName _ _ => structureName
    | .fvar _ => `fvar
    | .bvar _ => `bvar
    | .lam .. => `lambda
    | _ => `unrecognized_head)
  return .unclassified ⟨"unclassified_statement_head", name,
    namespaceLabel (← getEnv) name, (← get).theoremName⟩

private def statementStep (env : Environment) (current : Expr) : WalkM StatementStep := do
  let some (head, args) ← applicationParts current | return .incomplete
  match head with
  -- admission-exit: statementStep.1 rule=statementForall
  | .forallE .. => return .recognized (witness .statementForall current)
  | .const n levels =>
    match env.find? n with
    -- admission-exit: statementStep.2 rule=statementInductive
    | some (.inductInfo _) => return .recognized (witness .statementInductive current)
    | some (.defnInfo info) =>
      let value ← Core.instantiateValueLevelParams (.defnInfo info) levels
      let some body ← aliasBody value args | return .incomplete
      return .next body
    | _ => return ← statementUnknown head
  | .lam .. =>
    if args.isEmpty then return ← statementUnknown head
    let some body ← aliasBody head args | return .incomplete
    return .next body
  | .mdata _ body => return .next (mkAppN body args)
  | .letE _ _ value body _ =>
    let some body ← substitute body #[value] | return .incomplete
    let some body ← aliasBody body args | return .incomplete
    return .next body
  | .proj structureName index receiver =>
    let (record, work) := ReadoutFamily.carrier env receiver (← get).exprFuel
    unless ← chargeTraversal work do return .incomplete
    let some record := record | return ← statementUnknown head
    let some (ctor, fields) ← applicationParts record | return .incomplete
    let some (.ctorInfo info) := ctor.constName?.bind env.find?
      | return ← statementUnknown head
    unless info.induct == structureName do return ← statementUnknown head
    let some field := fields[info.numParams + index]? | return ← statementUnknown head
    let some body ← aliasBody field args | return .incomplete
    return .next body
  | _ => return ← statementUnknown head

private partial def statementOuter (env : Environment) (type : Expr) :
    WalkM (Option ProvenanceAdmissionWitness) := do
  unless ← chargeTraversal do return none
  if type.getAppFn.isConstOf `Multiset.Mem then
    -- admission-exit: statementOuter.1 rule=statementMembership
    return some (witness .statementMembership type)
  match ← statementStep env type with
  -- admission-exit: statementOuter.2 rule=retained-witness.rule
  | .recognized evidence => return some evidence
  | .unclassified _ => return none
  | .incomplete => noteIncomplete `incomplete_classification `type_classification; return none
  | .next next =>
    if next == type then return none
    -- admission-exit: statementOuter.forward.1 rule=retained-witness.rule
    statementOuter env next

-- Equality-only List metadata has recursive List premises and disequalities
-- ending in False. These explicit positive conclusions, or negations of known
-- non-equality heads, cannot be those premises. Unknown predicate heads stop.
private partial def listStatementBoundary (env : Environment) (type : Expr)
    (binders : Nat := 0) : WalkM (Option ProvenanceAdmissionWitness) := do
  let some evidence ← statementOuter env type | return none
  let type := evidence.matchedType
  match type with
  | .forallE n domain body bi =>
    if binders == 0 then
      let some firstProof ← boundedMeta (Meta.isProp domain) `list_statement_domain | return none
      if !firstProof then
        let twoDataBinders ← Meta.withLocalDecl n bi domain fun x => do
          let some body ← substitute body #[x] | return false
          let some evidence ← statementOuter env body | return false
          let body := evidence.matchedType
          let .forallE _ secondDomain _ _ := body | return false
          let some secondProof ← boundedMeta (Meta.isProp secondDomain) `list_statement_domain
            | return false
          return !secondProof
        -- admission-exit: listStatementBoundary.1 rule=listForall
        if twoDataBinders then return some (witness .listForall type)
    if body.isConstOf ``False then
      let some evidence ← statementOuter env domain | return none
      let domain := evidence.matchedType
      if domain.isForall || domain.getAppFn.constName?.any
          (#[``Exists, ``And, ``Or, ``List.Mem, `Multiset.Mem].contains ·) then
        -- admission-exit: listStatementBoundary.2 rule=listNegated
        return some (witness .listNegated type)
      return none
    Meta.withLocalDecl n bi domain fun x => do
      let some body ← substitute body #[x] | return none
      -- admission-exit: listStatementBoundary.forward.1 rule=retained-witness.rule
      listStatementBoundary env body (binders + 1)
  | _ =>
    let name := type.getAppFn.constName?.getD .anonymous
    if #[``And, ``Or, ``Exists, ``True, ``Eq, ``HEq, ``Nat.le].contains name ||
        (binders > 0 && #[``List.Mem, `Multiset.Mem].contains name) then
      -- admission-exit: listStatementBoundary.3 rule=listPositive
      return some (witness .listPositive type)
    return none

-- Pure data carriers for equality-only collection metadata. The surrounding
-- type fold has already checked actual parameters and statement-bearing fields.
-- Nominal carriers with proof/type-valued fields are excluded here; intrinsic
-- scalar bounds and quotient containers have explicit representation boundaries.
private partial def dataCarrier (env : Environment) (type : Expr)
    (active : Array Expr := #[]) : WalkM (Option ProvenanceAdmissionWitness) := do
  unless ← chargeTraversal do return none
  let some type ← representationType type | return none
  let some kind ← occurrenceType type | return none
  let .sort level := kind | return none
  unless level.isNeverZero do return none
  match type with
  | .sort _ => return none
  | .fvar id =>
    if (← id.getDecl).value? (allowNondep := true) |>.isNone then
      -- admission-exit: dataCarrier.1 rule=rigidCarrier
      return some (witness .rigidCarrier type)
    return none
  | .proj structureName index receiver =>
    -- Only registered arena/signature carrier selectors inherit the rigid
    -- local parameter boundary. Concrete receivers expose their actual field,
    -- which must pass the same carrier test (including Prop/payload fences).
    let audited := ReadoutFamily.carrierHeads.any fun selector =>
      match env.getProjectionFnInfo? selector with
      | some projection => projection.i == index &&
        (env.find? projection.ctorName).any fun info =>
          match info with
          | .ctorInfo info => info.induct == structureName
          | _ => false
      | none => false
    unless audited do return none
    let some receiver ← representationType receiver | return none
    if let .fvar id := receiver then
      if (← id.getDecl).value? (allowNondep := true) |>.isNone then
        -- admission-exit: dataCarrier.2 rule=carrierProjection
        return some (witness .carrierProjection type)
    let .next field ← statementStep env (.proj structureName index receiver) | return none
    if field == type then return none
    -- admission-exit: dataCarrier.forward.1 rule=retained-witness.rule
    dataCarrier env field active
  | .forallE n domain body bi =>
    unless (← dataCarrier env domain active).isSome do return none
    Meta.withLocalDecl n bi domain fun x => do
      let some body ← substitute body #[x] | return none
      -- admission-exit: dataCarrier.forward.2 rule=retained-witness.rule
      dataCarrier env body active
  | _ =>
    let some (head, args) ← applicationParts type | return none
    let .const name levels := head | return none
    if #[``Nat, ``Int, `Rat, ``Fin, `ZMod].contains name then
      -- admission-exit: dataCarrier.3 rule=scalarCarrier
      return some (witness .scalarCarrier type)
    if #[``List, `Multiset, `Finset].contains name && args.size == 1 then
      -- admission-exit: dataCarrier.4 rule=retained-witness.rule
      return ← dataCarrier env args[0]! active
    if name == ``Subtype && args.size == 2 then
      -- admission-exit: dataCarrier.5 rule=retained-witness.rule
      return ← dataCarrier env args[0]! active
    if active.contains type then return none
    if let some (.defnInfo info) := env.find? name then
      let value ← Core.instantiateValueLevelParams (.defnInfo info) levels
      let some body ← aliasBody value args | return none
      -- admission-exit: dataCarrier.6 rule=retained-witness.rule
      return ← dataCarrier env body (active.push type)
    let some branches ← caseFields type | return none
    for (lctx, instances, fields) in branches do
      for field in fields do
        let clean ← Meta.withLCtx lctx instances do
          let some fieldType ← occurrenceType field | return none
          -- admission-exit: dataCarrier.forward.3 rule=retained-witness.rule
          dataCarrier env fieldType (active.push type)
        unless clean.isSome do return none
    -- admission-exit: dataCarrier.7 rule=nominalCarrier
    return some (witness .nominalCarrier type)

-- Record explicit proposition-alias spellings only as rejection witnesses.
-- These hashes never certify non-mention and never normalize data operands.
private def statementAliases (env : Environment) : WalkM Unit := do
  let mut current := (← get).statement
  let mut seen : Std.HashSet UInt64 := {}
  repeat
    unless ← chargeTraversal do return
    if seen.contains (hash current) then
      noteIncomplete `alias_cycle `statement_aliases
      return
    seen := seen.insert (hash current)
    modify fun s => { s with statementForms := s.statementForms.push current }
    match ← statementStep env current with
    | .next body => current := body
    | .recognized evidence =>
      modify fun s => { s with recognizedStatement := some evidence }
      return
    | .unclassified site => noteUnclassified site; return
    | .incomplete => noteIncomplete `incomplete_classification `type_classification; return

-- The final supported outer spelling is used for structural family fences.
-- Computed operands remain untouched and cannot establish non-mention.
private def statementBoundary : WalkM (Option ProvenanceAdmissionWitness) := do
  -- admission-exit: statementBoundary.1 rule=retained-witness.rule
  return (← get).recognizedStatement

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

-- A hash mismatch never proves that two propositions have different statement
-- identities. This bounded recognizer establishes an actual rigid distinction:
-- different kernel heads, literals, domains, or a distinguishing live argument.
-- Unknown/computed heads stop. It never evaluates a recursor or proof term.
private partial def rigidStatementLocal (expression : Expr) : WalkM Bool := do
  unless ← chargeTraversal do return false
  match expression with
  | .fvar id => return ((← id.getDecl).value? (allowNondep := true)).isNone
  | .proj _ _ receiver => rigidStatementLocal receiver
  | .app function _ => rigidStatementLocal function
  | _ => return false

private partial def statementIdentityForm (env : Environment) (expression : Expr) :
    WalkM (Option Expr) := do
  unless ← chargeTraversal do return none
  let some expression ← representationType expression | return none
  let some (head, args) ← applicationParts expression | return none
  if let .fvar id := head then
    if let some value := (← id.getDecl).value? (allowNondep := true) then
      let some body ← aliasBody value args | return none
      return ← statementIdentityForm env body
    return some expression
  if let .proj structureName index receiver := head then
    -- A projection chain from an unassigned local record is rigid. A concrete
    -- receiver still follows the audited constructor-field decoder below.
    if let some localReceiver ← statementIdentityForm env receiver then
      if ← rigidStatementLocal localReceiver then
        return some (mkAppN (.proj structureName index localReceiver) args)
  match expression with
  | .sort _ | .lit _ | .lam .. => return some expression
  | _ => pure ()
  -- These quotient predicates have fixed proposition families after every
  -- possible reduction: List.Pairwise and List.Mem respectively. They do not
  -- expose an arbitrary proposition chosen by a carrier or callback.
  if #[`Multiset.Nodup, `Multiset.Mem].contains (head.constName?.getD Name.anonymous) then
    return some expression
  if (naturalLiteral expression).isSome ||
      expression.isConstOf ``Bool.true || expression.isConstOf ``Bool.false then
    return some expression
  if let .const name _ := head then
    if (env.find? name).any (fun info => match info with
        | .ctorInfo c => c.induct == ``Nat
        | _ => false) then return some expression
  match ← statementStep env expression with
  | .recognized evidence => return some evidence.matchedType
  | .next next => statementIdentityForm env next
  | .unclassified site =>
    if (← get).identityUnknown.isNone then modify fun s => { s with identityUnknown := some site }
    return none
  | .incomplete => noteIncomplete `incomplete_classification `statement_identity; return none

private partial def statementApart (env : Environment) (left right : Expr) :
    WalkM (Option ProvenanceAdmissionWitness) := do
  unless ← chargeTraversal do return none
  -- Equal fingerprints include possible collisions, so they never admit.
  if hash left == hash right then return none
  let some a ← statementIdentityForm env left | return none
  let some b ← statementIdentityForm env right | return none
  if hash a == hash b then return none
  if let some x := naturalLiteral a then
    if let some y := naturalLiteral b then
      if x != y then
        -- admission-exit: statementApart.1 rule=statementLiteralApart
        return some (witness .statementLiteralApart a)
  if (a.isConstOf ``Bool.true && b.isConstOf ``Bool.false) ||
      (a.isConstOf ``Bool.false && b.isConstOf ``Bool.true) then
    -- admission-exit: statementApart.2 rule=statementLiteralApart
    return some (witness .statementLiteralApart a)
  if let .lit x := a then
    if let .lit y := b then
      -- admission-exit: statementApart.3 rule=statementLiteralApart
      if x != y then return some (witness .statementLiteralApart a)
  let kernelHead := fun expression => expression.getAppFn.constName?.filter fun name =>
    (env.find? name).any fun info => match info with
      | .inductInfo _ => true
      | .ctorInfo c => c.induct == ``Nat
      | _ => false
  let metadataFamily := fun e =>
    if e.getAppFn.isConstOf `Multiset.Nodup then some ``List.Pairwise
    else if e.getAppFn.isConstOf `Multiset.Mem then some ``List.Mem else none
  let am := metadataFamily a
  let bm := metadataFamily b
  let ah := am.orElse fun _ => kernelHead a
  let bh := bm.orElse fun _ => kernelHead b
  if let some an := ah then
    if let some bn := bh then
      if an != bn then
        -- admission-exit: statementApart.4 rule=statementMetadataApart
        if am.isSome || bm.isSome then return some (witness .statementMetadataApart a)
        -- admission-exit: statementApart.5 rule=statementHeadApart
        return some (witness .statementHeadApart a)
      -- A shared metadata family is not evidence of identity or disjointness;
      -- its quotient representation is deliberately left unresolved.
      if am.isSome || bm.isSome then return none
      let aa := a.getAppArgs
      let ba := b.getAppArgs
      unless aa.size == ba.size do return none
      unless ← chargeTraversal aa.size do return none
      for i in [:aa.size] do
        if (← statementApart env aa[i]! ba[i]!).isSome then
          -- admission-exit: statementApart.6 rule=statementArgumentApart
          return some (witness .statementArgumentApart a)
      return none
  -- A rigid type parameter cannot reduce to a kernel inductive type head.
  -- No distinct-proof-variable or proof-constructor comparison is permitted.
  let rigidValue := fun e h => h.isSome || e.isForall || e.isSort ||
    (naturalLiteral e).isSome || e.isConstOf ``Bool.true || e.isConstOf ``Bool.false
  let an ← rigidStatementLocal a.getAppFn
  let bn ← rigidStatementLocal b.getAppFn
  if (an && rigidValue b bh) || (bn && rigidValue a ah) then
    -- admission-exit: statementApart.7 rule=statementRigidApart
    return some (witness .statementRigidApart a)
  match a, b with
  | .forallE n da ab bi, .forallE _ db bb _
  | .lam n da ab bi, .lam _ db bb _ =>
    if (← statementApart env da db).isSome then
      -- admission-exit: statementApart.8 rule=statementDomainApart
      return some (witness .statementDomainApart a)
    -- Congruence is conditional on equal domains. In that case one shared
    -- binder gives both well-typed bodies; unequal domains already distinguish
    -- the binders. This does not decide domain equality or normalize a carrier.
    Meta.withLocalDecl n bi da fun x => do
      let some ab ← substitute ab #[x] | return none
      let some bb ← substitute bb #[x] | return none
      if (← statementApart env ab bb).isSome then
        -- admission-exit: statementApart.9 rule=statementBodyApart
        return some (witness .statementBodyApart a)
      return none
  | .forallE .., _ =>
    -- admission-exit: statementApart.10 rule=statementMetadataApart
    if bm.isSome then return some (witness .statementMetadataApart a)
    -- admission-exit: statementApart.11 rule=statementHeadApart
    if bh.isSome || b.isSort then return some (witness .statementHeadApart a)
    return none
  | _, .forallE .. =>
    -- admission-exit: statementApart.12 rule=statementMetadataApart
    if am.isSome then return some (witness .statementMetadataApart a)
    -- admission-exit: statementApart.13 rule=statementHeadApart
    if ah.isSome || a.isSort then return some (witness .statementHeadApart a)
    return none
  | .sort .zero, .sort (.succ _) | .sort (.succ _), .sort .zero =>
    -- admission-exit: statementApart.14 rule=statementHeadApart
    return some (witness .statementHeadApart a)
  | .sort _, _ =>
    -- admission-exit: statementApart.15 rule=statementHeadApart
    if bh.isSome || b.isFVar then return some (witness .statementHeadApart a)
    return none
  | _, .sort _ =>
    -- admission-exit: statementApart.16 rule=statementHeadApart
    if ah.isSome || a.isFVar then return some (witness .statementHeadApart a)
    return none
  | _, _ => return none

private def checkedStatementType (env : Environment) (type : Expr) :
    WalkM (Option ProvenanceAdmissionWitness) := do
  unless ← chargeTraversal do return none
  -- admission-exit: checkedStatementType.1 rule=retained-witness.rule
  if let some evidence := (← get).apartPropositions[type]? then return some evidence
  modify fun s => { s with identityUnknown := none }
  let evidence ← statementApart env type (← get).statement
  if evidence.isNone then
    if let some site := (← get).identityUnknown then noteUnclassified site
  if evidence.isNone && !(← get).identityFailureTraced then
    modify fun s => { s with identityFailureTraced := true }
    trace[InformationProvenance.check]
      "statement_identity_unresolved first={(← get).currentFirst} site={(← get).currentOrigin} type={type} registered={(← get).statement}"
  if let some evidence := evidence then
    if !type.hasLooseBVars && !type.hasMVar && !type.hasLevelMVar then
      modify fun s => { s with apartPropositions := s.apartPropositions.insert type evidence }
  -- admission-exit: checkedStatementType.2 rule=retained-witness.rule
  return evidence

mutual
-- Compare a complete observed proof type, including the type of a nominal
-- proof field. A quantified proof's open mathematical body is not another
-- observed proof value; closed statement subtypes still pass the same guard.
private partial def observedType (env : Environment) (type : Expr)
    (active : Array Expr := #[]) : WalkM TypeClassification := do
  let some kind ← occurrenceType type | return ← unknownType type
  if kind == .sort .zero then
    if ← typeMentions env type then return .statementMention
    unless (← checkedStatementType env type).isSome do
      return ← unknownType type "unresolved_statement_identity"
  -- admission-exit: observedType.1 rule=retained-witness.rule
  return ← inputType env type active

-- One structural fold over inferred types and their type-valued arguments.
-- Nominal fields are native occurrences specialized by constructor-index patterns.
private partial def inputType (env : Environment) (type : Expr)
    (active : Array Expr := #[]) : WalkM TypeClassification := do
  unless ← chargeSummaryWork (fun c => { c with recheckedNodes := c.recheckedNodes + 1 }) do
    return ← unknownType type
  if type.hasLooseBVars || type.hasMVar || type.hasLevelMVar then return ← unknownType type
  if ReadoutFamily.carrierHeads.contains (type.getAppFn.constName?.getD .anonymous) then
    let (decoded, work) := ReadoutFamily.carrier env type (← get).exprFuel
    unless ← chargeTraversal work do return ← unknownType type
    let some decoded := decoded | return ← unknownType type
    if decoded == type then return ← unknownType type
    -- admission-exit: inputType.1 rule=retained-witness.rule
    return ← inputType env decoded active
  let producerAllowed := carrierProducerAllowed env (← get).currentFirst
  -- admission-exit: inputType.2 rule=retained-witness.rule
  if let some cached ← reuseWitness (← get).cleanTypes type then return .allowlisted cached
  -- Closed proposition subtypes can themselves contain statement identity.
  -- Complete occurrence/field types, including open ones, use observedType.
  if closed type then
    let some kind ← occurrenceType type | return ← unknownType type
    if kind == .sort .zero then
      if ← typeMentions env type then return .statementMention
      unless (← checkedStatementType env type).isSome do
        return ← unknownType type "unresolved_statement_identity"
  unless ← chargeTraversal do return ← unknownType type
  let enclosingAssumptions := (← get).assumedFamilyDepth
  let enclosingProducer := (← get).assumedProducer
  modify fun s => { s with assumedFamilyDepth := none, assumedProducer := none }
  let classify : WalkM TypeClassification := do
    -- Recursive occurrences recheck their actual arguments before using an
    -- enclosing-family assumption.
    -- A telescope is already traversed domain by domain by this classifier.
    -- Rescanning each complete suffix with typeMentions would duplicate its
    -- binder reconstruction and comparisons at every level.
    if let .forallE n domain body bi := type then
      let exact ← compareCanonical type (← get).statement
      let decision ← compareCanonical type (← get).decision
      let (dm, du) := (← inputType env domain active).flags
      let (bm, bu) ← (TypeClassification.flags <$> Meta.withLocalDecl n bi domain fun x => do
        let some body ← substitute body #[x] | return ← unknownType type
        -- admission-exit: inputType.forward.1 rule=retained-witness.rule
        inputType env body active)
      -- admission-exit: inputType.3 rule=telescope
      return ← checkedType .telescope type (exact || decision || dm || bm) (du || bu)
    if let .letE _ domain value body _ := type then
      let exact ← compareCanonical type (← get).statement
      let decision ← compareCanonical type (← get).decision
      let (dm, du) := (← inputType env domain active).flags
      let vm ← typeMentions env value
      let some body ← substitute body #[value] | return ← unknownType type
      let (bm, bu) := (← inputType env body active).flags
      -- admission-exit: inputType.4 rule=letType
      return ← checkedType .letType type (exact || decision || dm || vm || bm) (du || bu)
    let mut mentions ← typeMentions env type
    if ← compareCanonical type (← get).decision then mentions := true
    let some reduced ← representationType type | do
      trace[InformationProvenance.check] "failed_type={type}"
      return ← checkedType .nominalFields type mentions true
    mentions := (← typeMentions env reduced) || mentions
    match reduced with
    | .forallE n domain body bi =>
      let (dm, du) := (← inputType env domain active).flags
      let (bm, bu) ← (TypeClassification.flags <$> Meta.withLocalDecl n bi domain fun x =>
        do
          let some body ← substitute body #[x] | return ← unknownType type
          -- admission-exit: inputType.forward.2 rule=retained-witness.rule
          inputType env body active)
      -- admission-exit: inputType.5 rule=telescope
      return ← checkedType .telescope reduced (mentions || dm || bm) (du || bu)
    | .lam n domain body bi =>
      -- Type-valued lambda expressions are generated by dependent recursors
      -- (for example `Fin.casesOn` motives).  Inspect their domains and bodies
      -- through this same classifier instead of treating the lambda head as
      -- an unknown escape.
      let (dm, du) := (← inputType env domain active).flags
      let (bm, bu) ← (TypeClassification.flags <$> Meta.withLocalDecl n bi domain fun x => do
        let some body ← substitute body #[x] | return ← unknownType type
        -- admission-exit: inputType.forward.3 rule=retained-witness.rule
        inputType env body active)
      -- admission-exit: inputType.6 rule=lambdaType
      return ← checkedType .lambdaType reduced (mentions || dm || bm) (du || bu)
    | .letE n domain value body nd =>
      let (dm, du) := (← inputType env domain active).flags
      let (vm, vu) := (← inputType env value active).flags
      let (bm, bu) ← (TypeClassification.flags <$> Meta.withLetDecl n domain value (fun x => do
        let some body ← substitute body #[x] | return ← unknownType type
        -- admission-exit: inputType.forward.4 rule=retained-witness.rule
        inputType env body active) (nondep := nd))
      -- admission-exit: inputType.7 rule=letType
      return ← checkedType .letType reduced (mentions || dm || vm || bm) (du || vu || bu)
    | .mdata _ body =>
      let (bm, bu) := (← inputType env body active).flags
      -- admission-exit: inputType.8 rule=metadataType
      return ← checkedType .metadataType reduced (mentions || bm) bu
    | _ =>
      -- admission-exit: inputType.9 rule=sortKind
      if reduced.isSort then return ← checkedType .sortKind reduced mentions false
      let some (head, args) ← applicationParts reduced | return ← checkedType .nominalFields type mentions true
      if let .lam .. := head then
        let some body ← aliasBody head args | return ← checkedType .nominalFields type mentions true
        let (bm, bu) := (← inputType env body active).flags
        -- admission-exit: inputType.10 rule=betaType
        return ← checkedType .betaType reduced (mentions || bm) bu
      let mut unclassified := false
      for arg in args do
        if let .const n _ := arg.getAppFn then directConstant env n
        if let .proj n _ _ := arg.getAppFn then directProjection env n
        let some argType ← occurrenceType arg | return ← checkedType .nominalFields type mentions true
        let (tm, tu) := (← inputType env argType active).flags
        mentions := mentions || tm
        unclassified := unclassified || tu
        if let .family result ← typeFamilyArgument env arg argType active then
          let (am, au) := result.flags
          mentions := mentions || am
          unclassified := unclassified || au
      -- A local type-family head is allowed only after its inferred type has
      -- itself passed the funnel.  This keeps local neutral syntax from being
      -- an unknown-tolerant escape hatch.
      if head.isFVar then
        let some neutralType ← occurrenceType reduced | return ← checkedType .nominalFields type mentions true
        let (fm, fu) := (← inputType env neutralType active).flags
        -- admission-exit: inputType.11 rule=scopedParameter
        return ← checkedType .scopedParameter reduced (mentions || fm) (unclassified || fu)
      if let .proj _ _ receiver := head then
        -- Infer both the receiver and projection in the same context. Lean
        -- supplies the receiver's actual parameters, indices and universe.
        let some receiverType ← occurrenceType receiver | return ← checkedType .nominalFields type mentions true
        let (rm, ru) := (← inputType env receiverType active).flags
        let some projectionType ← occurrenceType head | return ← checkedType .auditedProjection type (mentions || rm) true
        let (pm, pu) := (← inputType env projectionType active).flags
        -- admission-exit: inputType.12 rule=auditedProjection
        return ← checkedType .auditedProjection reduced (mentions || rm || pm) (ru || pu || unclassified)
      let .const name _ := head | return ← unknownType reduced
      directProjection env name
      let some declaration := env.find? name | return ← checkedType .nominalFields type mentions true
      unless ← chargeTraversal do return ← checkedType .nominalFields type mentions true
      let knownKind ← if declaration.hasValue (allowOpaque := true) then pure none
        else reuseWitness (← get).cleanKinds head
      if !declaration.hasValue (allowOpaque := true) && knownKind.isNone then
        -- The actual head occurrence supplies its inferred kind. This closed
        -- kind is independent of the caller's recursive-family assumptions.
        let some kind ← occurrenceType head | return ← checkedType .nominalFields type mentions true
        let kindVerdict ← inputType env kind #[]
        let (km, ku) := kindVerdict.flags
        mentions := mentions || km
        unclassified := unclassified || ku
        let state ← get
        if !km && !ku && !state.incomplete && !state.forbidden && state.unclassified.isNone then
          unless ← chargeTraversal do return ← checkedType .nominalFields type mentions true
          if let some evidence := kindVerdict.witness? then
            modify fun s => { s with cleanKinds := s.cleanKinds.insert (head, evidence.sourceDependency) evidence }
      let some evidence ← statementBoundary | return ← unknownType reduced
      let statement := evidence.matchedType
      let natOrder := fun e =>
        let h := e.getAppFn
        h.isConstOf ``Nat.le || h.isConstOf ``Nat.lt ||
          ((h.isConstOf ``LE.le || h.isConstOf ``LT.lt) &&
            e.getAppArgs[0]?.any (·.isConstOf ``Nat))
      if natOrder reduced && natOrder statement then return ← checkedType .nominalFields type mentions true
      -- Membership of propositions is not a data-carrier boundary. Inspect
      -- the actual receiver carrier even when the interface projection is stuck.
      if name == ``Membership.mem && args.size >= 2 then
        let element := args[0]!
        if element == .sort .zero then return ← checkedType .nominalFields type mentions true
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
        -- admission-exit: inputType.13 rule=equality
        return ← checkedType .equality reduced mentions unclassified
      -- Nat.le has only natural indices and recursive Nat.le premises. Check
      -- the actual operands above; if S is itself an order statement, reject
      -- conservatively so no recursive order subproof can conceal it. This
      -- avoids enumerating numeric representation bounds (UInt32, Char, ...).
      if name == ``Nat.le then
        let some statement ← representationType statement
          | return ← checkedType .nominalFields type mentions true
        let head := statement.getAppFn
        let order := head.isConstOf ``Nat.le || head.isConstOf ``Nat.lt ||
          ((head.isConstOf ``LE.le || head.isConstOf ``LT.lt) &&
            statement.getAppArgs[0]?.any (·.isConstOf ``Nat))
        -- admission-exit: inputType.14 rule=naturalOrder
        return ← checkedType .naturalOrder reduced mentions (unclassified || order)
      -- Membership and uniqueness proofs over checked data carriers contain
      -- only recursive Mem/Pairwise and equality/function proof forms. The
      -- positive statement heads below cannot specialize to those forms.
      if (name == ``List.Pairwise || name == ``List.Mem) && args.size == 3 then
        let some kind ← occurrenceType args[0]! | return ← checkedType .nominalFields type mentions true
        let some (.sort level) ← representationType kind
          | return ← checkedType .nominalFields type mentions true
        let relation := mkApp (mkConst ``Ne [level]) args[0]!
        let some carrier ← namedCarrier env args[0]! | return ← checkedType .nominalFields type mentions true
        let some rigid ← boundedMeta (do
          let carrier ← pure carrier
          let .fvar id := carrier | return false
          return (← id.getDecl).value? (allowNondep := true) |>.isNone) `carrier_rigidity
          | return ← checkedType .nominalFields type mentions true
        -- A rigid parameter is scoped to this occurrence. Applications and
        -- enclosing case substitutions get freshly inferred field types.
        -- admission-exit: inputType.15 rule=rigidCarrier
        let mut carrierEvidence ← if rigid then pure (some (witness .rigidCarrier carrier))
          -- admission-exit: inputType.16 rule=scalarCarrier
          else if carrier.isConstOf ``Nat then pure (some (witness .scalarCarrier carrier))
          else dataCarrier env args[0]!
        if carrierEvidence.isNone && level.isNeverZero then
          let some carrier ← representationType carrier
            | return ← checkedType .nominalFields type mentions true
          if let some (.inductInfo family) := (carrier.getAppFn.constName?.bind env.find?) then
            let nullary := family.numParams == 0 && family.numIndices == 0 &&
              family.ctors.all (fun ctor => match env.find? ctor with
                | some (.ctorInfo info) => info.numFields == 0
                | _ => false)
            if nullary && closed carrier && !carrier.hasLevelMVar then
              unless ← chargeTraversal do return ← checkedType .nominalFields type mentions true
              if let some cached := (← get).certifiedNullaryCarriers[carrier]? then
                carrierEvidence := some cached
              else
                let some branches ← caseFields carrier | return ← checkedType .nominalFields type mentions true
                if branches.all (fun (_, _, fields) => fields.isEmpty) then
                  -- admission-exit: inputType.17 rule=nullaryCarrier
                  let evidence := witness .nullaryCarrier carrier
                  carrierEvidence := some evidence
                  unless ← chargeTraversal do return ← checkedType .nominalFields type mentions true
                  modify fun s => { s with certifiedNullaryCarriers :=
                    s.certifiedNullaryCarriers.insert carrier evidence }
        let relationAllowed := args[1]! == relation || match args[1]! with
          | .lam _ _ (.lam _ _ body _) _ =>
            body.isAppOfArity ``Ne 3 && body.getAppArgs[1]! == .bvar 1 &&
              body.getAppArgs[2]! == .bvar 0
          | _ => false
        if carrierEvidence.isSome && (name == ``List.Mem || relationAllowed) then
          let some statement ← representationType statement
            | return ← checkedType .nominalFields type mentions true
          let disjoint ← listStatementBoundary env statement
          -- admission-exit: inputType.18 rule=listMetadata
          if disjoint.isSome then return ← checkedType .listMetadata reduced mentions unclassified
        trace[InformationProvenance.check] "unsupported_list_boundary type={reduced} carrier={carrier} allowed={carrierEvidence.isSome} relation={relationAllowed}"
        return ← checkedType .nominalFields type mentions true
      if Lean.isClass env name && !listedTypeClasses.contains name then
        trace[InformationProvenance.check] "unsupported_class={name} type={type}"
        return ← checkedType .nominalFields type mentions true
      -- Quotient carriers and lifted type families expose their relation or
      -- predicate to the same argument classifier; no predicate is a leaf.
      if let some (.quotInfo info) := env.find? name then
        if match info.kind with | .type | .lift => true | _ => false then
          -- admission-exit: inputType.19 rule=quotientType
          return ← checkedType .quotientType reduced mentions unclassified
      if let some (.recInfo recursor) := env.find? name then
        if #[``Bool.rec, ``Nat.rec, ``List.rec, ``Prod.rec, ``Sum.rec, ``Option.rec,
            ``PUnit.rec, ``Fin.rec].contains name then
          -- admission-exit: inputType.20 rule=recursorType
          return ← checkedType .recursorType reduced mentions unclassified
        -- A kernel recursor over one parameter-free, index-free enumeration
        -- has no abstract carrier or proof payload in its constructors. Its
        -- actual motive, branches and major argument were checked above.
        -- This rule classifies output types; registered statement spellings
        -- still reject every recursor in statementStep.
        if recursor.numParams == 0 && recursor.numIndices == 0 &&
            recursor.numMotives == 1 then
          if let [familyName] := recursor.all then
            if let some (.inductInfo family) := env.find? familyName then
              let mut enumeration := family.numParams == 0 && family.numIndices == 0
              for constructor in family.ctors do
                unless ← chargeTraversal do return ← unknownType reduced
                enumeration := enumeration && (env.find? constructor).any fun declaration =>
                  match declaration with
                  | .ctorInfo constructor => constructor.numParams == 0 && constructor.numFields == 0
                  | _ => false
              if enumeration then
                -- admission-exit: inputType.21 rule=enumRecursorType
                return ← checkedType .enumRecursorType reduced mentions unclassified
        trace[InformationProvenance.check] "unclassified_recursor_head={name} type={reduced}"
        return ← unknownType reduced
      if let some (.defnInfo _) := env.find? name then
        -- An explicit type alias forwards its actual parameters. Its raw body
        -- must pass the same structural families; computed data is not evaluated.
        let value ← Core.instantiateValueLevelParams declaration head.constLevels! (allowOpaque := false)
        let some unfolded ← aliasBody value args | return ← checkedType .nominalFields type mentions true
        if unfolded == reduced then return ← checkedType .nominalFields type mentions true
        let (um, uu) := (← inputType env unfolded active).flags
        -- admission-exit: inputType.22 rule=aliasType
        return ← checkedType .aliasType reduced (mentions || um) (unclassified || uu)
      let some (.inductInfo info) := env.find? name | return ← checkedType .nominalFields type mentions true
      for depth in [:active.size] do
        let previous := active[depth]!
        let some (previousHead, previousArgs) ← applicationParts previous | return ← checkedType .nominalFields type mentions true
        unless ← chargeTraversal do return ← checkedType .nominalFields type mentions true
        if hash previousHead != hash head then continue
        unless ← chargeExpression previousHead do return ← checkedType .nominalFields type mentions true
        unless ← chargeExpression head do return ← checkedType .nominalFields type mentions true
        if previousHead == head then
          let mut sameParameters := true
          for index in [:info.numParams] do
            unless ← chargeTraversal do return ← checkedType .nominalFields type mentions true
            let some a := previousArgs[index]? | return ← checkedType .nominalFields type mentions true
            let some b := args[index]? | return ← checkedType .nominalFields type mentions true
            sameParameters := (a == b) && sameParameters
          let mut coveredIndices := true
          for index in [info.numParams:args.size] do
            unless ← chargeTraversal do return ← checkedType .nominalFields type mentions true
            let current := args[index]!
            -- Recursive occurrences with fresh indices share the enclosing
            -- family obligation. Concrete changed indices require fresh cases.
            if current.hasFVar then
              let some normalized ← representationType current | return ← checkedType .nominalFields type mentions true
              if normalized.hasFVar then continue
            let some previous := previousArgs[index]? | return ← checkedType .nominalFields type mentions true
            coveredIndices := (previous == current) && coveredIndices
          if sameParameters && coveredIndices then
            noteFamilyAssumption depth
            -- admission-exit: inputType.23 rule=recursiveFamily
            return ← checkedType .recursiveFamily reduced mentions unclassified
          -- Different parameters are a fresh obligation, as in nested products.
      let some branches ← caseFields reduced | do
        trace[InformationProvenance.check] "unsupported_nominal_fields type={reduced}"
        return ← checkedType .nominalFields type mentions true
      unless ← chargeTraversal (active.size + 1) do return ← checkedType .nominalFields type mentions true
      let nextActive := active.push reduced
      for (lctx, instances, fields) in branches do
        unless ← chargeTraversal do return ← checkedType .nominalFields type mentions true
        for field in fields do
          unless ← chargeTraversal do return ← checkedType .nominalFields type mentions true
          let (fm, fu) ← (TypeClassification.flags <$> Meta.withLCtx lctx instances do
            let some fieldType ← occurrenceType field | return ← unknownType type
            let some concrete ← representationType fieldType | return ← unknownType fieldType
            -- Constructor fields that introduce a carrier, or hide their value
            -- behind such a carrier, have no concrete representation witness.
            unless ← chargeTraversal args.size do return ← unknownType concrete
            let parameter := args.contains concrete
            -- Predicate slots of these reviewed interfaces are followed at each
            -- actual use. The two project containers require protected imports,
            -- so no value of their type can acquire the external implementation
            -- leaf rule; concrete statement/decision fields remain inspected.
            -- Course-of-values type recursion uses PProd to hold prior types.
            -- This representation is supported only at a protected implementation
            -- or a kernel constructor/recursor with inspected actual arguments.
            -- An opaque external producer of PProd Type still has no witness.
            let auditedProduct := name == ``PProd && producerAllowed
            if auditedProduct then
              modify fun s => { s with assumedProducer := some s.currentFirst }
            let auditedFamily := auditedProduct ||
              (Lean.isClass env name && listedTypeClasses.contains name) ||
              #[`D5.S3.ConceptDynamics.CIRPT.DecidableKernel,
                `D5.S3.ConceptDynamics.InformationEscape.TheoremUnit].contains name ||
              ReadoutFamily.carrierHeads.any fun selector =>
              (env.getProjectionFnInfo? selector).any fun projection =>
                (env.find? projection.ctorName).any fun declaration =>
                  match declaration with
                  | .ctorInfo ctor => ctor.induct == name
                  | _ => false
            let fieldEvidence ← if auditedFamily then do
              -- admission-exit: inputType.field.1 rule=fieldAudited
              pure (some (witness .fieldAudited concrete))
            else nominalFieldShape env concrete (args.extract 0 info.numParams)
            let carrierValued := fieldEvidence.isNone
            if carrierValued ||
                (concrete.isFVar && !parameter && !auditedFamily) then
              trace[InformationProvenance.check] "unclassified_abstract_carrier family={name} field_type={concrete} first={(← get).currentFirst}"
              return ← unknownType concrete "unclassified_abstract_carrier"
            -- admission-exit: inputType.forward.5 rule=retained-witness.rule
            observedType env concrete nextActive)
          mentions := mentions || fm
          unclassified := unclassified || fu
      -- admission-exit: inputType.24 rule=nominalFields
      return ← checkedType .nominalFields reduced mentions unclassified

  let result ← classify
  let producerDependency := (← get).assumedProducer
  let result := bindWitnessSource result producerDependency
  -- Constructor scans introduced in this call have now completed; discharge
  -- their recursive assumptions. A dependency on an enclosing unfinished family
  -- still forbids caching. Independent nested checks can be reused immediately.
  unless ← chargeTraversal do return ← unknownType type
  let unresolved := (← get).assumedFamilyDepth.filter (· < active.size)
  modify fun s => { s with
    assumedFamilyDepth := mergeAssumptions enclosingAssumptions unresolved
    assumedProducer := enclosingProducer.or producerDependency }
  let state ← get
  if let some evidence := result.witness? then
    if unresolved.isNone && !type.hasLooseBVars && !type.hasMVar && !type.hasLevelMVar &&
        !state.incomplete && !state.forbidden && state.unclassified.isNone then
      unless ← chargeTraversal do return ← unknownType type
      modify fun s => { s with cleanTypes := s.cleanTypes.insert (type, evidence.sourceDependency) evidence }
  -- admission-exit: inputType.25 rule=retained-witness.rule
  return result

-- Probe the inferred telescope first. Only functions ending in Sort supply
-- type families; ordinary data functions keep their term-provenance treatment.
private partial def typeFamilyArgument (env : Environment) (value type : Expr)
    (active : Array Expr) : WalkM FamilyClassification := do
  unless ← chargeTraversal do return .family (← unknownType type)
  -- admission-exit: typeFamilyArgument.1 rule=retained-witness.rule
  if let some cached ← reuseWitness (← get).dataFunctionTypes type then return .data cached
  let canCache := #[value, type].all fun e =>
    !e.hasLooseBVars && !e.hasMVar && !e.hasLevelMVar
  let source := (← get).currentFirst
  let cache := (← get).cleanFamilies
  if let some cached := cache[(value, type, (none : Option Name))]?.orElse fun _ => cache[(value, type, some source)]? then
    modify fun s => { s with
      counters.familyMemoHits := s.counters.familyMemoHits + 1
      assumedProducer := s.assumedProducer.or cached.sourceDependency }
    -- admission-exit: typeFamilyArgument.2 rule=retained-witness.rule
    return .family (.allowlisted cached)
  let enclosing := (← get).assumedFamilyDepth
  let enclosingProducer := (← get).assumedProducer
  modify fun s => { s with assumedFamilyDepth := none, assumedProducer := none }
  let inspect : WalkM FamilyClassification := do
    let some reduced ← representationType type | return .family (← unknownType type)
    match reduced with
    | .forallE n domain body bi =>
      let result ← Meta.withLocalDecl n bi domain fun x => do
        let some body ← substitute body #[x] | return .family (← unknownType type)
        unless ← chargeTraversal do return .family (← unknownType type)
        -- admission-exit: typeFamilyArgument.forward.1 rule=retained-witness.rule
        typeFamilyArgument env (mkApp value x) body active
      -- admission-exit: typeFamilyArgument.3 rule=retained-witness.rule
      let .family verdict := result | return result
      let (bm, bu) := verdict.flags
      let (dm, du) := (← inputType env domain active).flags
      -- admission-exit: typeFamilyArgument.4 rule=typeFamily
      return .family (← checkedType .typeFamily value (dm || bm) (du || bu))
    | .sort _ => return .family (← inputType env value active)
    | _ =>
      -- Non-family delegation also requires the positive carrier classification.
      -- A shape outside the type allowlist cannot become data by falling through.
      let verdict ← inputType env reduced active
      match verdict with
      -- admission-exit: typeFamilyArgument.5 rule=retained-witness.rule
      | .allowlisted evidence => return .data evidence
      | _ => return .family verdict
  let result ← inspect
  let state ← get
  let result := match result with
    | .family verdict => .family (bindWitnessSource verdict state.assumedProducer)
    -- admission-exit: typeFamilyArgument.forward.2 rule=retained-witness.rule
    | .data evidence => .data { evidence with sourceDependency := state.assumedProducer }
  modify fun s => { s with
    assumedFamilyDepth := mergeAssumptions enclosing state.assumedFamilyDepth
    assumedProducer := enclosingProducer.or state.assumedProducer }
  -- This fold opens no family frame: every surviving assumption is external.
  match result with
  | .family (.allowlisted evidence) =>
    if canCache && state.assumedFamilyDepth.isNone &&
        !state.incomplete && !state.forbidden && state.unclassified.isNone then
      unless ← chargeTraversal do return .family (← unknownType type)
      modify fun s => { s with cleanFamilies := s.cleanFamilies.insert (value, type, evidence.sourceDependency) evidence }
  | .data evidence =>
    if closed type && state.assumedFamilyDepth.isNone then
      unless ← chargeTraversal do return .family (← unknownType type)
      modify fun s => { s with dataFunctionTypes := s.dataFunctionTypes.insert (type, evidence.sourceDependency) evidence }
  | _ => pure ()
  -- admission-exit: typeFamilyArgument.6 rule=retained-witness.rule
  return result
end

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

/-- Declared-template provenance enters the existing fail-closed walker only at
raw supplied arguments. All arguments share one lower-only debit, including
reused syntax summaries; no template body is sent through this path. -/
def templateArgumentsCurrent (theoremName : Name) (arguments : Array Expr)
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
