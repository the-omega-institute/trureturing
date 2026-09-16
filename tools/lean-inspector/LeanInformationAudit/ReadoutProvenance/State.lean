import LeanInformationAudit.ReadoutProvenance.Family
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

def closed (e : Expr) : Bool := !e.hasLooseBVars && !e.hasFVar && !e.hasMVar

def decisionFamily : Array Name := #[
  ``Decidable, ``DecidablePred, ``DecidableRel, ``DecidableEq,
  ``DecidableLE, ``DecidableLT]

def listedProducers : Array Name := #[
  ``Decidable.isTrue, ``Decidable.isFalse, ``decidable_of_iff, ``decidable_of_iff',
  ``decidable_of_bool, ``decidable_of_decidable_of_iff, ``decidable_of_decidable_of_eq,
  ``decEq, ``Nat.decEq, ``Nat.decLt, ``Nat.decLe, ``Bool.decEq,
  ``instDecidableEqOfLawfulBEq, ``inferInstance, `Equiv.decidableEq]

def isCtorOrInductive (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | some (.inductInfo _) | some (.ctorInfo _) | some (.recInfo _) | some (.quotInfo _) => true
  | _ => false

private def moduleName (env : Environment) (n : Name) : Name :=
  (env.getModuleIdxFor? n).map (env.header.modules[·.toNat]!.module) |>.getD env.header.mainModule

-- Lean orders imported modules after their dependencies. Protect every module
-- importing a protected module, regardless of its library or declaration names.
-- Missing import metadata is protected too; it cannot justify an external leaf.
def classifyModules (env : Environment) : Std.HashMap Name Bool := Id.run do
  let mut classes : Std.HashMap Name Bool := {}
  for index in [:env.header.modules.size] do
    let name := env.header.modules[index]!.module
    let inherited := match env.header.moduleData[index]? with
      | none => true
      | some data => data.imports.any (fun i => classes[i.module]?.getD true)
    classes := classes.insert name
      (name.getRoot == `D5 || name.getRoot == `LeanInformationAudit || inherited)
  return classes

initialize moduleScopeCache : EnvExtension (Option (Std.HashMap Name Bool)) ←
  registerEnvExtension (pure none)

def inProtected (env : Environment) (n : Name) : Bool :=
  if (env.getModuleIdxFor? n).isNone then true else
    let m := moduleName env n
    m == env.header.mainModule ||
      ((moduleScopeCache.getState env).bind (·[m]?)).getD true

-- These producers expose their implementations or have kernel-controlled
-- computation rules. Arbitrary external definitions have no such permission.
def carrierProducerAllowed (env : Environment) (name : Name) : Bool :=
  inProtected env name || isCtorOrInductive env name || name == ``Nat.brecOn

def namespaceLabel (env : Environment) (n : Name) : String :=
  if inProtected env n then
    if moduleName env n == env.header.mainModule then "protected:current"
    else if (moduleName env n).getRoot == `LeanInformationAudit then "protected:judge" else "protected:D5"
  else if n.getRoot == `Classical then "external:Classical"
  else "external:other"

structure Unclassified where
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

inductive TypeClassification where
  | allowlisted (witness : ProvenanceAdmissionWitness)
  | statementMention
  | forbidden
  | unclassified (site : Unclassified)
  | incomplete

instance : Inhabited TypeClassification := ⟨.incomplete⟩

def TypeClassification.flags : TypeClassification → Bool × Bool
  -- admission-exit: TypeClassification.flags.forward.1 rule=retained-witness.rule
  | .allowlisted _ => (false, false)
  | .statementMention | .forbidden => (true, false)
  | .unclassified _ | .incomplete => (false, true)

def TypeClassification.witness? : TypeClassification → Option ProvenanceAdmissionWitness
  -- admission-exit: TypeClassification.witness?.forward.1 rule=retained-witness.rule
  | .allowlisted witness => some witness
  | _ => none

inductive FamilyClassification where
  | data (witness : ProvenanceAdmissionWitness)
  | family (verdict : TypeClassification)

inductive Position where | dataPos | proofPos | typePos
  deriving BEq, Hashable, Inhabited

-- A cached declaration contains only its typed roots. Children are requested
-- lazily after the occurrence boundary; no proof implementation is summarized.
structure SyntaxNode where
  expr : Expr
  position : Position
  deriving Inhabited

structure Summary where
  nodes : Array SyntaxNode := #[]
  roots : Array Nat := #[]
  visits : Nat := 0
  constructionWork : Nat := 0
  incomplete : Bool := false
  deriving Inhabited

def summarise (_env : Environment) (inputs : Array (Position × Expr)) (fuel : Nat) :
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
initialize summaryCache : EnvExtension (Std.HashMap (Name × List Level) Summary) ←
  registerEnvExtension (pure {})
initialize countersCache : EnvExtension ProvenanceCounters ←
  registerEnvExtension (pure {})

def getProvenanceCounters : CoreM ProvenanceCounters := do
  return countersCache.getState (← getEnv)

structure WalkState where
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

abbrev WalkM := StateRefT WalkState MetaM

def noteIncomplete (cause operation : Name) : WalkM Unit := do
  modify fun s => { s with incomplete := true }
  trace[InformationProvenance.check]
    "incomplete cause={cause} operation={operation} first={(← get).currentFirst} site={(← get).currentOrigin}"

-- Every pass over a summary is charged to the same per-query expression fuel
-- as syntax construction.  In particular, a cache hit must not make the
-- statement fold free: otherwise a large cached summary could be replayed
-- without consuming the bound that protects the allowlist check.
def chargeSummaryWork (update : ProvenanceCounters → ProvenanceCounters) (amount : Nat := 1) :
    WalkM Bool := do
  if amount > (← get).exprFuel then
    trace[InformationProvenance.check] "incomplete cause=expression_budget operation=work_reservation first={(← get).currentFirst} site={(← get).currentOrigin}"
    modify fun s => { s with incomplete := true }
    return false
  modify fun s => { s with
    exprFuel := s.exprFuel - amount
    counters := update s.counters }
  return true

def chargeTraversal (amount : Nat := 1) : WalkM Bool :=
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

def chargeExpression (e : Expr) : WalkM Bool := do
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

def substitute (e : Expr) (locals : Array Expr) : WalkM (Option Expr) := do
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

def applicationParts (e : Expr) : WalkM (Option (Expr × Array Expr)) := do
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

def resultHead (raw : Expr) : WalkM (Option Name) := do
  let mut e := raw
  repeat
    unless ← chargeTraversal do return none
    match e with
    | .forallE _ _ body _ | .mdata _ body => e := body
    | _ => break
  let some (head, _) ← applicationParts e | return none
  return head.constName?

def noteUnclassified (u : Unclassified) : WalkM Unit := do
  if (← get).unclassified |>.isNone then modify fun s => { s with unclassified := some u }

def witness (rule : ProvenanceAllowRule) (type : Expr) : ProvenanceAdmissionWitness :=
  ⟨rule, type.getAppFn, type, none⟩

-- Cache only the exact dependency that justified a producer-sensitive rule.
-- Most types have no such dependency and remain reusable at every occurrence.
-- A source name is occurrence data, never a caller-selectable classification mode.
def reuseWitness (cache : Std.HashMap (Expr × Option Name) ProvenanceAdmissionWitness)
    (type : Expr) : WalkM (Option ProvenanceAdmissionWitness) := do
  let source := (← get).currentFirst
  let found := cache[(type, (none : Option Name))]?.orElse fun _ => cache[(type, some source)]?
  let found := found.filter fun evidence => evidence.sourceDependency.all (· == source)
  if let some evidence := found then
    modify fun s => { s with assumedProducer := s.assumedProducer.or evidence.sourceDependency }
  -- admission-exit: reuseWitness.1 rule=retained-witness.rule
  return found

def bindWitnessSource (verdict : TypeClassification) (source : Option Name) :
    TypeClassification := match verdict with
  -- admission-exit: bindWitnessSource.forward.1 rule=retained-witness.rule
  | .allowlisted evidence => .allowlisted { evidence with sourceDependency := source }
  | other => other

def unknownType (type : Expr) (className : String := "unclassified_argument_type") :
    WalkM TypeClassification := do
  let state ← get
  let first := if state.currentFirst.isAnonymous then
    type.getAppFn.constName?.getD state.theoremName else state.currentFirst
  return .unclassified ⟨className, first, namespaceLabel (← getEnv) first, state.currentOrigin⟩

-- A rule discharges a structural obligation only when every child was
-- classified. Rejection flags are projections of typed child verdicts; a
-- failed branch can never supply the witness accepted by the caller or memo.
def checkedType (rule : ProvenanceAllowRule) (type : Expr)
    (mentions unknown : Bool) : WalkM TypeClassification := do
  if mentions then return .statementMention
  if unknown then return ← unknownType type
  -- admission-exit: checkedType.1 rule=retained-witness.rule
  return .allowlisted (witness rule type)

def queue (name : Name) (levels : List Level) : WalkM Unit := do
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
def compareCanonical (a b : Expr) : WalkM Bool := do
  unless ← chargeTraversal do return false
  -- Hash mismatch is a constant-time negative prefilter. Hash agreement is
  -- conservatively treated as a possible mention, never as proof of equality.
  return hash a == hash b ||
    (hash b == hash (← get).statement && (← get).statementForms.any (fun form => hash form == hash a))

-- Preserve constant provenance before reduction, including constants discovered
-- only in a constructor field's type. Direct forbidden sources take precedence.
def directConstant (env : Environment) (n : Name) : WalkM Unit := do
  if n == (← get).theoremName || isJudgeIdentity env n then
    modify fun s => { s with forbidden := true, walked := s.walked.insert n }

def directProjection (env : Environment) (n : Name) : WalkM Unit := do
  if isJudgeProjection n then
    modify fun s => { s with forbidden := true, walked := s.walked.insert n }

-- Eligible instance heads still require the same structural fold over their
-- parameters and every constructor field. An unfamiliar class never inherits external-leaf
-- status from its module. In particular proof-carrying user classes are unclassified.
def listedTypeClasses : Array Name := #[
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

def boundedMeta (action : MetaM α) (site : Name := `type_classification)
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
def occurrenceType (e : Expr) : WalkM (Option Expr) := do
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
def naturalLiteral (e : Expr) : Option Nat := do
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

def exactScalarStatement (e : Expr) : WalkM Bool := do
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

def caseFields (type : Expr) :
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

end LeanInformationAudit.RegistrationGates
