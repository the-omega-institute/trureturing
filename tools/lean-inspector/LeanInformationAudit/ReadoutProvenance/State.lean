import Lean.Data.Options
import Lean.Data.Json
import LeanInformationAudit.ReadoutProvenance.View
import LeanInformationAudit.Contract.NodeFacts
/-!
Occurrence type shapes are projected from compiled declarations in their original
lexical binder context at the existing work limit. An allowlist checks structural
type families, specialized constructor fields and explicit carrier projections. Independent proofs stop at the compiled
Prop boundary. Their implementations never enter executable provenance. Unknown
forms fail closed; exhausted work returns an incomplete closure. Reusable caches
contain declaration syntax only, while projected types and verdicts are query-local.
-/

namespace LeanInformationAudit.RegistrationGates
open Lean

-- §10.1 budget record: safety limit outside the capacity domain; owner=governance lane;
-- basis=the existing 4100-link closure-exhaustion fixture;
-- exit condition=the supported closure corpus or pinned Lean version changes,
-- then rerun that fixture and review the safety ceiling before changing it.
def provenanceConstantFuel : Nat := 4096
-- InformationRoot and TemplateShadow profiles, Lean 4.33.0:
-- the context-selection query consumed 8,034,836 work units;
-- InformationRoot's largest query consumed 3,247,448.
private def provenanceReferenceQueryWork : Nat := 8034836
-- §10.1 budget record: safety limit outside the capacity domain; owner=governance lane;
-- basis=the measured 8,034,836 work-unit maximum plus 25%
-- safety headroom, rounded upward; exit condition=the pinned Lean version,
-- supported readout corpus, or measurement profile changes, then remeasure.
def provenanceExpressionFuel : Nat := (5 * provenanceReferenceQueryWork + 3) / 4
register_option provenanceExpressionLimit : Nat := {
  defValue := provenanceExpressionFuel
  descr := "Readout work limit, capped by the production expression policy" }

-- Allocation per compiled type-shape query is independently bounded.
-- Exhaustion produces an incomplete result at the original operation address.
def provenanceDefEqHeartbeats : Nat := 20000

register_option provenanceDefEqLimit : Nat := {
  defValue := provenanceDefEqHeartbeats
  descr := "Maximum raw heartbeats for compiled type-shape queries; legacy option name; zero is incomplete" }

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
  `LeanInformationAudit.TemplateAudit.assessedPlanBytes,
  `LeanInformationAudit.TemplateBinding.inventory,
  `LeanInformationAudit.TemplateBinding.records,
  `LeanInformationAudit.TypedAssessment.assessSnapshot,
  `LeanInformationAudit.assessTypedRegistrations,
  `LeanInformationAudit.TemplateBinding.assessJoined,
  `LeanInformationAudit.TemplateBinding.exportSnapshot,
  `LeanInformationAudit.TemplateBinding.joinedSnapshot,
  `LeanInformationAudit.TemplateBinding.targetJson,
  `LeanInformationAudit.assessReportTargets,
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
      `LeanInformationAudit.RegistrationInput, `LeanInformationAudit.TemplateEnrollmentInput,
      `LeanInformationAudit.SealInput, `LeanInformationAudit.TemplateBinding.ResolvedDeclaration,
      `LeanInformationAudit.InformationRegistryEntry, `LeanInformationAudit.ExpectedOccurrence,
      `LeanInformationAudit.TemplateAudit.TemplatePlanData,
      `LeanInformationAudit.TemplateAudit.TemplateIndex,
      `LeanInformationAudit.TemplateAudit.DependencyIdentity,
      `LeanInformationAudit.TemplateOccurrenceKey, `LeanInformationAudit.TemplateOccurrenceEvent,
      `LeanInformationAudit.TemplateBindingCertificate, `LeanInformationAudit.TemplateBindingResult,
      `LeanInformationAudit.BindingRecord, `LeanInformationAudit.TemplateBindingClaim,
      `LeanInformationAudit.TemplateBinding.JoinedRecords,
      `LeanInformationAudit.AutoDerivedSemanticCertificate,
      `LeanInformationAudit.CatalogUnitRecord, `LeanInformationAudit.CatalogRecord,
      `LeanInformationAudit.SealArenaRecord,
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
def isJudgeIdentity (env : CompiledView) (name : Name) : Bool :=
  provenanceJudgeAPIs.contains name || generatedAddress name || judgePayloadType name ||
    (env.find? name).any judgePayload ||
    ((env.getProjectionFnInfo? name).bind (fun p => env.find? p.ctorName)).any judgePayload

/-- A raw projection names its structure, rather than its projection function. -/
def isJudgeProjection (name : Name) : Bool :=
  provenanceJudgeAPIs.contains name || generatedAddress name || judgePayloadType name

def closed (e : Expr) : Bool := !e.hasLooseBVars && !e.hasFVar && !e.hasMVar

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


def decisionFamily : Array Name := #[
  ``Decidable, ``DecidablePred, ``DecidableRel, ``DecidableEq,
  ``DecidableLE, ``DecidableLT]

def listedProducers : Array Name := #[
  ``Decidable.isTrue, ``Decidable.isFalse, ``decidable_of_iff, ``decidable_of_iff',
  ``decidable_of_bool, ``decidable_of_decidable_of_iff, ``decidable_of_decidable_of_eq,
  ``decEq, ``Nat.decEq, ``Nat.decLt, ``Nat.decLe, ``Bool.decEq,
  ``instDecidableEqOfLawfulBEq, ``inferInstance, `Equiv.decidableEq]

def isCtorOrInductive (env : CompiledView) (n : Name) : Bool :=
  match env.find? n with
  | some (.inductInfo _) | some (.ctorInfo _) | some (.recInfo _) | some (.quotInfo _) => true
  | _ => false

private def moduleName (env : CompiledView) (name : Name) : Name :=
  (env.ownerOf name).getD env.mainModule

def inProtected (env : CompiledView) (name : Name) : Bool :=
  match env.ownerOf name with
  | none => true
  | some owner => owner == env.mainModule || env.protectedModules[owner]?.getD true

-- These producers expose their implementations or have kernel-controlled
-- computation rules. Arbitrary external definitions have no such permission.
def carrierProducerAllowed (env : CompiledView) (name : Name) : Bool :=
  inProtected env name || isCtorOrInductive env name || name == ``Nat.brecOn

def namespaceLabel (env : CompiledView) (n : Name) : String :=
  if inProtected env n then
    if moduleName env n == env.mainModule then "protected:current"
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
  | statementHeadApart | statementScalarApart
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

def summarise (_env : CompiledView) (inputs : Array (Position × Expr)) (fuel : Nat) :
    IO Summary := do
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

/-- Retained statement syntax scoped to one binding validation. -/
structure StatementAliasMemo where
  theoremName : Name
  statement : Expr
  /-- Keep the identified declaration table alive for the memo's lifetime. -/
  constants : CompiledView
  isExporting : Bool
  forms : Array Expr
  recognized : ProvenanceAdmissionWitness

/-- A syntax index of bound operands and their complete checked type arguments. -/
structure BoundNodeIndex where
  operands : Std.HashMap Expr (Array Contract.NodeFacts.BoundOperand) := {}
  typeSorts : Std.HashMap Expr (Array Level) := {}
  deriving Inhabited

/-- Process-local syntax caches and output observations. Query verdicts and
lexical occurrence types remain in WalkState. -/
structure ProvenanceSession where
  summaries : Std.HashMap (Name × List Level) Summary := {}
  counters : ProvenanceCounters := {}
  aliasMemo : Bool × Option StatementAliasMemo := (false, none)
  wholeReadoutCalls : Nat := 0
  nodeWork : Nat := 0
  nodeIndexes : Std.HashMap USize (Array Contract.NodeFacts.BoundOperand ×
    BoundNodeIndex) := {}
  deriving Inhabited

structure QueryContext where
  view : CompiledView
  session : IO.Ref ProvenanceSession
  locals : LocalContext := {}
  nodeFacts : Array Contract.NodeFacts.BoundOperand := #[]
  options : Options := {}
  heartbeatStart : Nat
  heartbeatLimit : Nat
  trace : String → IO Unit := fun _ => pure ()

abbrev QueryM := ReaderT QueryContext IO

def getCompiledView [Monad m] [MonadReaderOf QueryContext m] : m CompiledView :=
  return (← read).view

def getQueryOptions [Monad m] [MonadReaderOf QueryContext m] : m Options :=
  return (← read).options

def getQueryLocals [Monad m] [MonadReaderOf QueryContext m] : m LocalContext :=
  return (← read).locals

def querySession [Monad m] [MonadReaderOf QueryContext m] : m (IO.Ref ProvenanceSession) :=
  return (← read).session

def auditTrace [Monad m] [MonadReaderOf QueryContext m] [MonadLiftT IO m]
    (message : String) : m Unit := do
  let context ← read
  if context.options.getBool `trace.InformationProvenance.check false then
    context.trace message

def localDeclaration (id : FVarId) : QueryM LocalDecl := do
  let some declaration := (← getQueryLocals).find? id
    | throw <| IO.userError s!"incomplete_closure:provenance.local:{id.name}"
  return declaration

def queryConstant (name : Name) : QueryM ConstantInfo := do
  let some info := (← getCompiledView).find? name
    | throw <| IO.userError s!"incomplete_closure:provenance.constant:{name}"
  return info

def compiledValue (info : ConstantInfo) (levels : List Level)
    (allowOpaque : Bool := false) : QueryM Expr := do
  unless info.levelParams.length == levels.length do
    throw <| IO.userError s!"incomplete_closure:provenance.levels:{info.name}"
  let some value := info.value? (allowOpaque := allowOpaque)
    | throw <| IO.userError s!"incomplete_closure:provenance.value:{info.name}"
  return Contract.Literal.instantiateRawLevels info.levelParams levels value

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
  binderContexts : Std.HashMap (Array Expr) (LocalContext × Array Expr) := {}
  nextLocal : Nat := 0
  exprFuel : Nat := provenanceExpressionFuel
  constFuel : Nat := provenanceConstantFuel

abbrev WalkM := StateRefT WalkState QueryM

def freshLocalId : WalkM FVarId := do
  let mut index := (← get).nextLocal
  let locals ← getQueryLocals
  while locals.contains ⟨Name.num `compiledProvenanceLocal index⟩ do index := index + 1
  modify fun state => { state with nextLocal := index + 1 }
  return ⟨Name.num `compiledProvenanceLocal index⟩

def withCompiledLocal (name : Name) (info : BinderInfo) (type : Expr)
    (action : Expr → WalkM α) : WalkM α := do
  let id ← freshLocalId
  withReader (fun context : QueryContext =>
    { context with locals := context.locals.mkLocalDecl id name type info })
    (action (mkFVar id))

def withCompiledLet (name : Name) (type value : Expr) (action : Expr → WalkM α)
    (nondep : Bool := false) : WalkM α := do
  let id ← freshLocalId
  withReader (fun context : QueryContext =>
    { context with locals := context.locals.mkLetDecl id name type value nondep })
    (action (mkFVar id))

def withCompiledLocals (locals : LocalContext) (action : WalkM α) : WalkM α :=
  withReader (fun context : QueryContext => { context with locals }) action


def noteIncomplete (cause operation : Name) : WalkM Unit := do
  modify fun s => { s with incomplete := true }
  auditTrace s!
    "incomplete cause={cause} operation={operation} first={(← get).currentFirst} site={(← get).currentOrigin}"

-- Every pass over a summary is charged to the same per-query expression fuel
-- as syntax construction.  In particular, a cache hit must not make the
-- statement fold free: otherwise a large cached summary could be replayed
-- without consuming the bound that protects the allowlist check.
def chargeSummaryWork (update : ProvenanceCounters → ProvenanceCounters) (amount : Nat := 1) :
    WalkM Bool := do
  if amount > (← get).exprFuel then
    auditTrace s! "incomplete cause=expression_budget operation=work_reservation first={(← get).currentFirst} site={(← get).currentOrigin}"
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
  auditTrace s! "unknown_type class={className} first={state.currentFirst} site={state.currentOrigin} type={type}"
  let first := if state.currentFirst.isAnonymous then
    type.getAppFn.constName?.getD state.theoremName else state.currentFirst
  return .unclassified ⟨className, first, namespaceLabel (← getCompiledView) first, state.currentOrigin⟩

-- A rule discharges a structural obligation only when every child was
-- classified. Rejection flags are projections of typed child verdicts; a
-- failed branch can never supply the witness accepted by the caller or memo.
def checkedType (rule : ProvenanceAllowRule) (type : Expr)
    (mentions unknown : Bool) : WalkM TypeClassification := do
  if mentions then return .statementMention
  if unknown then
    auditTrace s! "unknown_rule rule={repr rule} type={type}"
    return ← unknownType type
  -- admission-exit: checkedType.1 rule=retained-witness.rule
  return .allowlisted (witness rule type)

def queue (name : Name) (levels : List Level) : WalkM Unit := do
  let n := (name, levels)
  let s ← get
  if s.queued.contains n then return
  if s.constFuel == 0 then
    auditTrace s! "incomplete cause=constant_budget operation=constant_enqueue first={name} site={s.currentOrigin}"
    modify fun s => { s with incomplete := true }
  else
    modify fun s => { s with queued := s.queued.insert n, pending := List.cons n s.pending, constFuel := s.constFuel - 1 }

-- No failed or exhausted compiled query can supply a positive allowlist verdict.
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
def directConstant (env : CompiledView) (n : Name) : WalkM Unit := do
  if n == (← get).theoremName || isJudgeIdentity env n then
    modify fun s => { s with forbidden := true, walked := s.walked.insert n }

def directProjection (_env : CompiledView) (n : Name) : WalkM Unit := do
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

/-- Bound facts supply compiler-checked types and relations. The lookup closes
 the actual lexical telescope; it never infers a type or reduces a term. -/
private def closeNode (locals : LocalContext) (e : Expr) : Expr := Id.run do
  let mut result := e
  for declaration in locals.decls.toArray.reverse do
    if let some declaration := declaration then
      let x := mkFVar declaration.fvarId
      let body := result.abstract #[x]
      result := if let some value := declaration.value? (allowNondep := true) then
        .letE declaration.userName declaration.type value body declaration.isNondep
      else .lam declaration.userName declaration.type body declaration.binderInfo
  return result

private def openNodeType (locals : LocalContext) (type : Expr) : Option Expr := Id.run do
  let mut result := type
  for declaration in locals.decls.toArray do
    if let some declaration := declaration then
      match result with
      | .forallE _ _ body _ => result := body.instantiate1 (mkFVar declaration.fvarId)
      | .letE _ _ _ body _ => result := body.instantiate1 (mkFVar declaration.fvarId)
      | _ => return none
  return some result

private def closeProposition (locals : LocalContext) (e : Expr) : Expr := Id.run do
  let mut result := e
  for declaration in locals.decls.toArray.reverse do
    if let some declaration := declaration then
      let body := result.abstract #[mkFVar declaration.fvarId]
      result := if let some value := declaration.value? (allowNondep := true) then
        .letE declaration.userName declaration.type value body declaration.isNondep
      else .forallE declaration.userName declaration.type body declaration.binderInfo
  return result

-- Index construction is a mechanical fact traversal, separately charged to the
-- same query work fuel. Each insertion retains the type-query heartbeat ceiling;
-- completing a syntax index never classifies an occurrence or caches a verdict.
private def prepareNodeIndex (fuel : Nat) : QueryM Unit := do
  let context ← read
  let identity := unsafe ptrAddrUnsafe context.nodeFacts
  let budget := min provenanceDefEqHeartbeats (provenanceDefEqLimit.get context.options)
  unless budget > 0 do
    throw <| IO.userError "incomplete_closure:E8.compiled_expression_heartbeats"
  if (← context.session.get).nodeIndexes.contains identity then return
  let mut index : BoundNodeIndex := {}
  let mut work := 0
  for fact in context.nodeFacts do
    let amount := 1 + (if fact.proposition.isSome then 1 else 0) +
      (if fact.type.isSome && fact.typeSort.isSome then 1 else 0)
    unless work + amount ≤ fuel do
      throw <| IO.userError "incomplete_closure:E8.node_work"
    let start ← IO.getNumHeartbeats
    let key := fact.value
    index := { index with
      operands := index.operands.insert key ((index.operands[key]?).getD #[] |>.push fact) }
    if let some type := fact.type then
      if let some sortLevel := fact.typeSort then
        index := { index with
          typeSorts := index.typeSorts.insert type ((index.typeSorts[type]?).getD #[] |>.push sortLevel) }
    if let some proposition := fact.proposition then
      let boundary := { fact with
        value := proposition, role := .type,
        type := some (mkSort .zero), typeSort := some (.succ .zero),
        proposition := some proposition,
        relation := none, other := none, otherLocation := none }
      let key := proposition
      index := { index with
        operands := index.operands.insert key ((index.operands[key]?).getD #[] |>.push boundary) }
    work := work + amount
    context.session.modify fun session => { session with nodeWork := session.nodeWork + amount }
    unless (← IO.getNumHeartbeats) - start ≤ budget do
      throw <| IO.userError "incomplete_closure:E8.compiled_expression_heartbeats"
  unless work + 1 ≤ fuel do
    throw <| IO.userError "incomplete_closure:E8.node_work"
  let start ← IO.getNumHeartbeats
  context.session.modify fun session => { session with
    nodeWork := session.nodeWork + 1,
    nodeIndexes := session.nodeIndexes.insert identity (context.nodeFacts, index) }
  unless (← IO.getNumHeartbeats) - start ≤ budget do
    context.session.modify fun session => { session with
      nodeIndexes := session.nodeIndexes.erase identity }
    throw <| IO.userError "incomplete_closure:E8.compiled_expression_heartbeats"

private def factsAt (e : Expr) : QueryM (Array Contract.NodeFacts.BoundOperand) := do
  let context ← read
  prepareNodeIndex 524288
  let identity := unsafe ptrAddrUnsafe context.nodeFacts
  let session ← context.session.get
  let index : Std.HashMap Expr (Array Contract.NodeFacts.BoundOperand) :=
    ((session.nodeIndexes[identity]?).map (·.2.operands)).getD {}
  let closed := closeNode context.locals e
  let proposition := closeProposition context.locals e
  let raw := (index[e]?).getD #[]
  let scopedFacts : Array Contract.NodeFacts.BoundOperand := if closed.equal e then #[] else (index[closed]?).getD #[]
  let boundaries := (index[proposition]?).getD #[]
  let inferred := boundaries.filter fun fact =>
    fact.role == .type && fact.proposition.any (·.equal fact.value)
  context.session.modify fun session => { session with
    nodeWork := session.nodeWork + context.locals.numIndices + 3 +
      raw.size + scopedFacts.size + boundaries.size }
  -- A full lexical endpoint keeps later dependent field queries in the same
  -- actual telescope. A closed endpoint remains available when no scoped
  -- endpoint exists; every candidate still carries its checked raw binding.
  return scopedFacts ++ raw ++ inferred

private def matchingFact (e : Expr) : QueryM (Option Contract.NodeFacts.BoundOperand) := do
  return (← factsAt e).find? (·.type.isSome)

/-- Only an actual bound operand's kernel-checked type starts raw child typing.
 An expected type of an unbound application supplies no authority. -/
def hasTypedNodeFact (e : Expr) : QueryM Bool := do
  return (← matchingFact e).any (·.type.isSome)

/-- Type aliases are the actual checked type arguments of bound operands.
 A scoped Pi alias supplies only Prop classification, never an inner sort. -/
private def typeSortsAt (e : Expr) (includeContext : Bool := false) : QueryM (Array Level) := do
  let context ← read
  prepareNodeIndex 524288
  let identity := unsafe ptrAddrUnsafe context.nodeFacts
  let index : Std.HashMap Expr (Array Level) :=
    (((← context.session.get).nodeIndexes[identity]?).map (·.2.typeSorts)).getD {}
  let key := if includeContext then closeProposition context.locals e else e
  let sorts := (index[key]?).getD #[]
  context.session.modify fun session => { session with
    nodeWork := session.nodeWork + 1 + sorts.size +
      (if includeContext then context.locals.numIndices else 0) }
  return sorts

/-- A bound generic declaration type retains its checked sort at an explicit
 universe instance. The complete instantiated operand must match the actual
 compiler declaration type before its sort enters the syntax index. -/
private def cacheConstantTypeSort (info : ConstantInfo) (levels : List Level)
    (actualType : Expr) : QueryM Unit := do
  if info.levelParams.isEmpty then return
  unless (← typeSortsAt actualType).isEmpty do return
  let context ← read
  let candidates ← factsAt info.type
  for fact in candidates do
    context.session.modify fun session => { session with nodeWork := session.nodeWork + 1 }
    unless fact.location.declaration == info.name && fact.location.part == .type &&
        fact.location.path.isEmpty &&
        fact.location.levels == info.levelParams.map Level.param do continue
    unless fact.value.equal info.type do continue
    let some (.sort sortLevel) := fact.type | continue
    let value := Contract.Literal.instantiateRawLevels info.levelParams levels fact.value
    unless value.equal actualType do continue
    let .sort actualSort := Contract.Literal.instantiateRawLevels info.levelParams levels
      (mkSort sortLevel) | continue
    let identity := unsafe ptrAddrUnsafe context.nodeFacts
    let some (_, index) := (← context.session.get).nodeIndexes[identity]? | return
    let sorts := (index.typeSorts[actualType]?).getD #[]
    context.session.modify fun session => { session with
      nodeWork := session.nodeWork + info.levelParams.length + sorts.size + 1,
      nodeIndexes := session.nodeIndexes.insert identity (context.nodeFacts,
        { index with typeSorts := index.typeSorts.insert actualType (sorts.push actualSort) }) }
    return

def typedNodeType (e : Expr) : QueryM Expr := do
  (← read).session.modify fun session => { session with nodeWork := session.nodeWork + 1 }
  if e.isAppOfArity ``lcProof 1 then return e.appArg!
  if let .fvar id := e then return (← localDeclaration id).type
  if let .const name levels := e then
    let info ← queryConstant name
    unless info.levelParams.length == levels.length do
      throw <| IO.userError "contract.node_binding:type_levels"
    let actualType := Contract.Literal.instantiateRawLevels info.levelParams levels info.type
    cacheConstantTypeSort info levels actualType
    return actualType
  if let some sortLevel := ((← typeSortsAt e)[0]?) then return mkSort sortLevel
  let some fact ← matchingFact e
    | throw <| IO.userError "unclassified_form:node.type_fact_missing"
  let some type := fact.type
    | throw <| IO.userError "unclassified_form:node.type_fact_missing"
  if fact.value == e || (fact.role == .type && fact.proposition.any (·.equal fact.value)) then return type
  let some type := openNodeType (← read).locals type
    | throw <| IO.userError "contract.node_binding:type_telescope"
  return type

/-- Only an explicit ExactMatch supplies a certified compiler head. -/
def exactNodeHead? (e : Expr) : QueryM (Option Expr) := do
  let context ← read
  let mut hasExact := false
  for fact in ← factsAt e do
    unless fact.relation == some ``Contract.NodeFact.exact do continue
    let some target := fact.other | continue
    hasExact := true
    context.session.modify fun session => { session with nodeWork := session.nodeWork + 1 }
    -- Query candidates use alpha syntax; their original coordinate bindings
    -- retain strict raw equality independently of this lookup.
    if fact.value == e then return some target
    let mut result := target
    let mut opens := true
    for declaration in context.locals.decls.toArray do
      if let some declaration := declaration then
        if !opens then break
        context.session.modify fun session => { session with nodeWork := session.nodeWork + 1 }
        match result with
        | .lam _ _ body _ | .letE _ _ _ body _ =>
          result := body.instantiate1 (mkFVar declaration.fvarId)
        | _ => opens := false
    -- An eta relation may have fewer explicit target wrappers. Only another
    -- already-bound endpoint that opens the full actual telescope is usable.
    if opens then return some result
  if hasExact then throw <| IO.userError "contract.node_binding:exact_telescope"
  return none

/-- An absent exact fact leaves the compiler expression unchanged. -/
def exactNodeHead (e : Expr) : QueryM Expr := do
  return (← exactNodeHead? e).getD e

/-- Decode one named structure field from a literal, kernel-bound record.
 The field index is compiler layout data; no beta, recursor or conversion runs. -/
def literalRecordField (structureName : Name) (index : Nat) (base : Expr) : QueryM Expr := do
  let view ← getCompiledView
  let value ← exactNodeHead base
  let value ← IO.ofExcept <| Contract.Literal.referencedValue view.find? value
  let .const constructor _ := value.getAppFn
    | throw <| IO.userError "unclassified_form:node.record_literal"
  let some (.ctorInfo info) := view.find? constructor
    | throw <| IO.userError "unclassified_form:node.record_constructor"
  unless info.induct == structureName && index < info.numFields do
    throw <| IO.userError "contract.node_binding:record_layout"
  let some field := value.getAppArgs[info.numParams + index]?
    | throw <| IO.userError "contract.node_binding:record_arity"
  return field

def typedNodeProp (e : Expr) : QueryM Bool := do
  let classify : Array Level → QueryM Bool := fun sorts => do
    if sorts.any (· == Level.zero) then return true
    if sorts.any Level.isNeverZero then return false
    throw <| IO.userError "unclassified_form:node.type_sort_unclassified"
  let exact ← typeSortsAt e
  unless exact.isEmpty do return ← classify exact
  let scopedSorts ← typeSortsAt e true
  unless scopedSorts.isEmpty do return ← classify scopedSorts
  match ← exactNodeHead (← typedNodeType e) with
  | .sort sortLevel => classify #[sortLevel]
  | _ => pure false

/-- An absent proof classification retains the raw subtree without erasure. -/
def typedNodeProof (e : Expr) : QueryM Bool := do
  if e.isAppOfArity ``lcProof 1 then return true
  if let .const name levels := e then
    let info ← queryConstant name
    unless info.levelParams.length == levels.length do
      throw <| IO.userError "contract.node_binding:proof_levels"
    if info matches .thmInfo _ then return true
  if let some fact ← matchingFact e then
    if fact.role == .proof then return true
    if fact.role == .type then return false
    -- A data or relation constructor can itself carry a proof. Only the
    -- compiler-checked universe of its complete type authorizes this cut.
    if fact.typeSort == some .zero then return true
  return false

/-- Eq and Iff witnesses are used only for mathematical correspondence.
 Exact compiler operand binding has already been checked by NodeFacts.fact. -/
def certifiedNodeRelation (left right : Expr) : QueryM Bool := do
  if left.equal right then return true
  let rightClosed := closeNode (← read).locals right
  return (← factsAt left).any fun fact =>
    fact.relation.any (#[``Contract.NodeFact.exact, ``Contract.NodeFact.equal,
      ``Contract.NodeFact.equivalent].contains ·) &&
      fact.other.any (fun value => value.equal right || value.equal rightClosed)

/-- Every fact lookup spends the same query-local work budget as traversal. -/
def boundQueryWork (action : QueryM α) (fuel : Nat := 524288) : QueryM (α × Nat) := do
  let session ← querySession
  let before := (← session.get).nodeWork
  let result ← action
  let work := (← session.get).nodeWork - before
  unless work ≤ fuel do throw <| IO.userError "incomplete_closure:E8.node_work"
  return (result, work)

private partial def eraseBoundNode (e : Expr) (depth : Nat) : StateT Nat QueryM Expr := do
  unless (← get) > 0 && depth ≤ 256 do
    throw <| IO.userError "incomplete_closure:E8.node_erasure"
  modify (· - 1)
  if ← typedNodeProof e then
    let proposition ← typedNodeType e
    return mkApp (mkConst ``lcProof) (← eraseBoundNode proposition (depth + 1))
  let child := fun e => eraseBoundNode e (depth + 1)
  match e with
  | .app f a => return .app (← child f) (← child a)
  | .lam name type body info | .forallE name type body info =>
    let domain ← child type
    let context ← read
    let id : FVarId := ⟨Name.num `boundErasure context.locals.numIndices⟩
    let localTerm := mkFVar id
    let body ← withReader (fun context : QueryContext => { context with
      locals := context.locals.mkLocalDecl id name type info }) <|
      child (body.instantiate1 localTerm)
    let body := body.abstract #[localTerm]
    return if e.isLambda then .lam name domain body info else .forallE name domain body info
  | .letE name type value body nondep =>
    let domain ← child type
    let value' ← child value
    let context ← read
    let id : FVarId := ⟨Name.num `boundErasure context.locals.numIndices⟩
    let localTerm := mkFVar id
    let body ← withReader (fun context : QueryContext => { context with
      locals := context.locals.mkLetDecl id name type value nondep }) <|
      child (body.instantiate1 localTerm)
    return .letE name domain value' (body.abstract #[localTerm]) nondep
  | .mdata data body => return .mdata data (← child body)
  | .proj name index receiver => return .proj name index (← child receiver)
  | .mvar _ | .bvar _ => throw <| IO.userError "incomplete_closure:E7.node_erasure_open"
  | _ => return e

/-- Proof cuts come only from bound kernel-checked facts. The proposition is
 retained and recursively inspected; absent facts never authorize erasure. -/
def eraseBoundProofs (e : Expr) (fuel : Nat := 524288) : QueryM (Expr × Nat) := do
  let limit := min 524288 fuel
  let ((result, remaining), queries) ← boundQueryWork ((eraseBoundNode e 0).run limit) limit
  let work := limit - remaining + queries
  unless work ≤ limit do throw <| IO.userError "incomplete_closure:E8.node_erasure_work"
  return (result, work)

def boundedQuery (action : QueryM α) (site : Name := `type_classification)
    (operations : Nat := 1) : WalkM (Option α) := do
  unless ← chargeSummaryWork (fun c => { c with canonicalizations := c.canonicalizations + operations }) operations do
    return none
  let budget := min provenanceDefEqHeartbeats (provenanceDefEqLimit.get (← getQueryOptions))
  if budget == 0 then
    modify fun s => { s with incomplete := true }
    auditTrace s!"incomplete cause=heartbeat_exhaustion operation={site} first={(← get).currentFirst} site={(← get).currentOrigin}"
    return none
  let available := (← get).exprFuel
  let preparationStart := (← (← querySession).get).nodeWork
  let prepared : Except IO.Error (Unit × Nat) ← try
    pure (.ok (← boundQueryWork (prepareNodeIndex available) available))
  catch error => pure (.error error)
  match prepared with
  | .error error =>
    let work := (← (← querySession).get).nodeWork - preparationStart
    discard <| chargeTraversal work
    auditTrace s!"incomplete cause=fact_index operation={site}: {error}"
    modify fun s => { s with incomplete := true }
    return none
  | .ok (_, work) =>
    unless ← chargeTraversal work do return none
  let start ← IO.getNumHeartbeats
  let available := (← get).exprFuel
  let queryStart := (← (← querySession).get).nodeWork
  let result : Except IO.Error (α × Nat) ← try
    let value ← withReader (fun context : QueryContext =>
      { context with heartbeatStart := start, heartbeatLimit := budget * operations })
      (boundQueryWork action available)
    if (← IO.getNumHeartbeats) - start > budget * operations then
      throw <| IO.userError s!"incomplete_closure:E8.compiled_expression_heartbeats:spent={(← IO.getNumHeartbeats) - start}:limit={budget * operations}"
    pure (.ok value)
  catch error => pure (.error error)
  match result with
  | .ok (value, work) =>
    unless ← chargeTraversal work do return none
    return some value
  | .error error =>
    let work := (← (← querySession).get).nodeWork - queryStart
    discard <| chargeTraversal work
    (← read).trace s!"query_failure operation={site}: {error}"
    let heartbeat := error.toString.contains "compiled_expression_heartbeats"
    modify fun s => { s with incomplete := true }
    auditTrace s!"incomplete cause={if heartbeat then "heartbeat_exhaustion" else "query_runtime_exception"} operation={site} first={(← get).currentFirst} site={(← get).currentOrigin}"
    return none

-- Declaration and bound-fact types retain actual levels and local identities.
-- The same query-local map holds raw child kinds projected from checked
-- applications and lambdas. An unbound expected type is never cached.
def occurrenceType (e : Expr) : WalkM (Option Expr) := do
  unless ← chargeTraversal do return none
  if e.hasLooseBVars || e.hasMVar || e.hasLevelMVar then
    noteUnclassified ⟨"unclassified_occurrence", `occurrence, "unclassified", `occurrence⟩
    return none
  if let some type := (← get).inferredTypes[e]? then return some type
  let some type ← boundedQuery (typedNodeType e) `type_shape | return none
  modify fun s => { s with
    inferredTypes := s.inferredTypes.insert e type
    counters.inferredOccurrences := s.counters.inferredOccurrences + 1 }
  return some type

/-- Project parameter types from a kernel-checked raw constant application.
 Each retained argument is the actual child of that application. The cache
 also retains raw children of an already checked lambda at its codomain;
 synthetic applications never enter this path through an expected type. -/
def checkedApplicationArguments (application : Expr) : WalkM (Option (Array Expr)) := do
  let some (head, arguments) ← applicationParts application | return none
  unless head.isConst do return none
  if arguments.isEmpty then return some #[]
  unless ← chargeTraversal do return none
  unless (← get).inferredTypes.contains application do
    let some checked ← boundedQuery (hasTypedNodeFact application) `application_parameter_fact
      | return none
    unless checked do return none
  let some initial ← occurrenceType head | return none
  let mut telescope := initial
  let mut types := #[]
  for argument in arguments do
    unless ← chargeTraversal do return none
    let .forallE _ domain body _ := telescope | return none
    types := types.push domain
    let some next ← substitute body #[argument] | return none
    telescope := next
    -- The compiler checked this whole application against its actual head.
    -- Preserve a separately bound actual type when it is already available.
    unless (← get).inferredTypes.contains argument do
      unless ← chargeTraversal do return none
      modify fun state => { state with
        inferredTypes := state.inferredTypes.insert argument domain }
  unless types.size == arguments.size do return none
  return some types

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

-- Constructor telescopes are projected from compiled occurrences. Only literal
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

private partial def constructorFields (type : Expr) (args : Array Expr)
    (parameters : Nat) (k : Array Expr → Expr → WalkM α)
    (fields : Array Expr := #[]) : WalkM (Option α) := do
  unless ← chargeTraversal do return none
  match type with
  | .forallE n domain body bi =>
    if parameters > 0 then
      let some arg := args[0]? | return none
      let some body ← substitute body #[arg] | return none
      constructorFields body (args.extract 1 args.size) (parameters - 1) k fields
    else
      withCompiledLocal n bi domain fun field => do
        let some body ← substitute body #[field] | return none
        constructorFields body args 0 k (fields.push field)
  | _ => return some (← k fields type)

def caseFields (type : Expr) :
    WalkM (Option (Array (LocalContext × Array Expr))) := do
  let some (head, args) ← applicationParts type | return none
  let .const name levels := head | return none
  let some (.inductInfo family) := (← getCompiledView).find? name | return none
  let parent ← getQueryLocals
  let mut branches := #[]
  for ctor in family.ctors do
    unless ← chargeTraversal do return none
    let some constructorType ← occurrenceType (mkConst ctor levels) | return none
    let result ← constructorFields constructorType args family.numParams fun fields result => do
      if fields.isEmpty then return some (parent, #[])
      let some (_, indices) ← applicationParts result | return none
      let mut bindings : Std.HashMap FVarId Expr := {}
      for i in [family.numParams:args.size] do
        let some pattern := indices[i]? | return none
        let some next ← bindIndex pattern args[i]! bindings | return none
        bindings := next
      -- Only substitute already fixed index binders, never solve new equations.
      let mut actualFields := #[]
      -- Rebuild from the actual parent, not the temporary constructor telescope
      -- that already contains every original field. Earlier field identities
      -- are replaced in order; fixed index bindings retain priority.
      let mut lctx := parent
      let mut fieldBindings := bindings
      for field in fields do
        let .fvar originalId := field | return none
        let original ← localDeclaration originalId
        let some fieldType ← occurrenceType field | return none
        unless ← chargeExpression fieldType do return none
        let fieldType := fieldType.replace fun e => match e with
          | .fvar id => fieldBindings[id]?
          | _ => none
        let id ← freshLocalId
        lctx := lctx.mkLocalDecl id original.userName fieldType original.binderInfo original.kind
        let actual := mkFVar id
        actualFields := actualFields.push actual
        unless fieldBindings.contains originalId do
          unless ← chargeTraversal do return none
          fieldBindings := fieldBindings.insert originalId actual
      return some (lctx, actualFields)
    let some result := result | return none
    -- A constructor with a distinct literal index has no fields at this index.
    if let some branch := result then branches := branches.push branch
    else if family.numIndices > 0 then
      -- Unknown index patterns do not justify a clean nominal boundary.
      return none
  modify fun s => { s with counters.caseExpansions := s.counters.caseExpansions + 1 }
  return some branches

/-- A field domain is in the context preceding that field. Its own binder and
 later fields cannot enter the closed telescope used for fact binding. -/
def fieldDomainPrefix (lctx : LocalContext) (field : Expr) : WalkM (Option LocalContext) := do
  let .fvar id := field | return none
  let some declaration := lctx.find? id | return none
  unless ← chargeTraversal (lctx.numIndices - declaration.index + 1) do return none
  let mut fieldPrefix := lctx
  while fieldPrefix.numIndices > declaration.index do
    fieldPrefix := fieldPrefix.pop
  unless fieldPrefix.numIndices == declaration.index do return none
  return some fieldPrefix

-- A recognized representation alias forwards its actual arguments through its
-- explicit lambda telescope. It does not evaluate a computed data expression.

end LeanInformationAudit.RegistrationGates
