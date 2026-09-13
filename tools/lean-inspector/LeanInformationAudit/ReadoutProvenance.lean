import Lean

namespace LeanInformationAudit.RegistrationGates
open Lean

def provenanceConstantFuel : Nat := 4096
def provenanceExpressionFuel : Nat := 524288

-- policy-override, G1b-2, owner: governance lane, 2026-09-13. Raw Lean
-- allocation heartbeats per definitional comparison; exhaustion is unknown.
-- Revisit when the supported readout corpus or the pinned Lean version changes.
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

private def stripMData : Expr → Expr
  | .mdata _ e => stripMData e
  | e => e

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
  indices : Std.HashMap (Expr × Position × Array Expr) Nat := {}
  fuel : Nat

private abbrev SummaryM := StateRefT SummaryBuild CoreM

private partial def summariseExpr (env : Environment) (pos : Position) (raw : Expr)
    (context : Array Expr := #[]) :
    SummaryM (Option Nat) := do
  let s ← get
  if s.fuel == 0 then
    modify fun s => { s with summary.incomplete := true }
    return none
  if s.summary.visits % 256 == 0 then Core.checkMaxHeartbeats "readout provenance"
  modify fun s => { s with fuel := s.fuel - 1, summary.visits := s.summary.visits + 1 }
  let e := stripMData raw
  let keyContext := if e.hasLooseBVars then context else #[]
  if let some i := (← get).indices[(e, pos, keyContext)]? then return some i
  let inputs : Array (Position × Expr × Array Expr) := match e with
    | .app f a => #[(pos, f, context), (pos, a, context)]
    | .lam _ t b _ | .forallE _ t b _ => #[(.typePos, t, context), (pos, b, context.push e)]
    | .letE _ t v b _ => #[(.typePos, t, context), (pos, v, context), (pos, b, context.push e)]
    | .proj _ _ b => #[(pos, b, context)]
    | _ => #[]
  let mut children := #[]
  for (childPos, child, childContext) in inputs do
    if let some i ← summariseExpr env childPos child childContext then children := children.push i
  let ownContent := match e with
    | .const n _ => inProtected env n && !env.isProjectionFn n &&
        (env.find? n).any (fun info => match info with
          | .defnInfo _ | .opaqueInfo _ | .thmInfo _ => true
          | _ => false)
    | _ => false
  let nodes := (← get).summary.nodes
  let pContent := ownContent || children.any (fun i => nodes[i]!.pContent)
  let declaredType := e.constName?.bind (fun n => (env.find? n).map (·.type))
  let node : SyntaxNode := ⟨e, keyContext, pos, children, ← propLooking env e, pContent, declaredType⟩
  modify fun s => { s with
    summary.nodes := s.summary.nodes.push node
    indices := s.indices.insert (e, pos, keyContext) nodes.size }
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
  /-- Nodes of a cached summary rechecked against the current statement. -/
  recheckedNodes : Nat := 0
  /-- Child edges (application/binder spines) inspected while rechecking. -/
  spineArguments : Nat := 0
  /-- Canonical-expression comparisons performed while rechecking. -/
  canonicalizations : Nat := 0
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
  pending : List (Name × Position × Name) := []
  typeObligations : List (Expr × Array Expr × Bool × Bool × Name × Name) := []
  appObligations : List (Expr × Array Expr × Bool × Name) := []
  comparisons : Std.HashMap (Expr × Expr) Bool := {}
  typeChecks : Std.HashMap (Expr × Array Expr × Bool) (Bool × Bool × Bool) := {}
  forbidden : Bool := false
  unclassified : Option Unclassified := none
  incomplete : Bool := false
  exprFuel : Nat := provenanceExpressionFuel
  constFuel : Nat := provenanceConstantFuel

private abbrev WalkM := StateRefT WalkState MetaM

-- Every pass over a summary is charged to the same per-query expression fuel
-- as syntax construction.  In particular, a cache hit must not make the
-- statement fold free: otherwise a large cached summary could be replayed
-- without consuming the bound that protects the allowlist check.
private def chargeSummaryWork (update : ProvenanceCounters → ProvenanceCounters) :
    WalkM Bool := do
  if (← get).exprFuel == 0 then
    modify fun s => { s with incomplete := true }
    return false
  modify fun s => { s with
    exprFuel := s.exprFuel - 1
    counters := update s.counters }
  return true

private def noteUnclassified (u : Unclassified) : WalkM Unit := do
  if (← get).unclassified |>.isNone then modify fun s => { s with unclassified := some u }

private def queue (n : Name) (pos : Position) (site : Name) : WalkM Unit := do
  let s ← get
  if s.queued.contains n then return
  if s.constFuel == 0 then modify fun s => { s with incomplete := true } else
    modify fun s => { s with queued := s.queued.insert n, pending := List.cons (n, pos, site) s.pending, constFuel := s.constFuel - 1 }

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

private def typeConstant (env : Environment) (n : Name) : WalkM Unit := do
  directConstant env n
  if let some info := env.find? n then
    if (← compareCanonical info.type (← get).statement) ||
        (← compareCanonical info.type (← get).decision) then
      modify fun s => { s with forbidden := true, walked := s.walked.insert n }
    if inProtected env n then queue n .typePos n
  else modify fun s => { s with incomplete := true }

-- Positive policies for instance types whose parameters are still checked by
-- the same structural fold. An unfamiliar class never inherits external-leaf
-- status from its module. In particular proof-carrying user classes are unknown.
private def listedTypeClasses : Array Name := #[
  ``Decidable, ``OfNat, ``Inhabited, ``Subsingleton, ``BEq, ``LawfulBEq,
  `Fintype, `Finite, `NeZero,
  -- Scalar operator interfaces: their actual type parameters are checked too.
  ``Zero, ``One, ``Add, ``HAdd, ``Mul, ``HMul, ``Sub, ``HSub, ``Div, ``HDiv,
  ``Neg, ``Inv, ``Pow, ``HPow, ``Mod, ``HMod, ``LT, ``LE]

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
  if (← compareCanonical type (← get).statement) || (← compareCanonical type (← get).decision) then
    modify fun s => { s with forbidden := true }
  return some type

private partial def inBinderContext (context : Array Expr) (k : Array Expr → WalkM α)
    (index : Nat := 0) (locals : Array Expr := #[]) : WalkM α := do
  if h : index < context.size then
    let next := fun locals => inBinderContext context k (index + 1) locals
    match context[index] with
    | .lam n t _ bi | .forallE n t _ bi =>
      Meta.withLocalDecl n bi (t.instantiateRev locals) fun x => next (locals.push x)
    | .letE n t v _ nd =>
      Meta.withLetDecl n (t.instantiateRev locals) (v.instantiateRev locals)
        (fun x => next (locals.push x)) (nondep := nd)
    | _ => k locals
  else k locals

-- The syntax scan checks TERM occurrences inside types. They are not themselves
-- assumed to be types (e.g. Classical constants on either side of an equality).
private partial def typeMentions (env : Environment) (e : Expr) : WalkM Bool := do
  unless ← chargeSummaryWork (fun c => { c with recheckedNodes := c.recheckedNodes + 1 }) do
    return false
  if ← compareCanonical e (← get).statement then return true
  match e with
  | .const n _ => typeConstant env n; return false
  | .app f a =>
    let _ ← appliedValueType e
    return (← typeMentions env f) || (← typeMentions env a)
  | .lam n t b bi | .forallE n t b bi =>
    let domain ← typeMentions env t
    let body ← Meta.withLocalDecl n bi t fun x => typeMentions env (b.instantiate1 x)
    return domain || body
  | .letE n t v b nd =>
    let domain ← typeMentions env t
    let value ← typeMentions env v
    let body ← Meta.withLetDecl n t v (fun x => typeMentions env (b.instantiate1 x)) (nondep := nd)
    return domain || value || body
  | .mdata _ b => typeMentions env b
  | .proj n _ b => directProjection env n; typeMentions env b
  | _ => return false

-- No provisional verdict is cached. A regular recursive field closes only its
-- active, identical obligation; changing an index on a recursive edge is unknown.
private partial def inputType (env : Environment) (type : Expr)
    (active : Array Expr := #[]) (checkResult : Bool := true) : WalkM (Bool × Bool) := do
  unless ← chargeSummaryWork (fun c => { c with recheckedNodes := c.recheckedNodes + 1 }) do
    return (false, true)
  let mut mentions ← typeMentions env type
  if ← compareCanonical type (← get).decision then mentions := true
  let some reduced ← boundedMeta (Meta.whnf type) | return (mentions, true)
  if reduced != type then mentions := (← typeMentions env reduced) || mentions
  match reduced with
  | .forallE n domain body bi =>
    let (dm, du) ← inputType env domain active
    let (bm, bu) ← Meta.withLocalDecl n bi domain fun x =>
      inputType env (body.instantiate1 x) active checkResult
    return (mentions || dm || bm, du || bu)
  | _ =>
    if !checkResult then return (mentions, false)
    if reduced.isSort then return (mentions, false)
    let head := reduced.getAppFn
    let args := reduced.getAppArgs
    let mut unknown := false
    for arg in args do
      let some isType ← boundedMeta (Meta.isType arg) | return (mentions, true)
      if isType then
        let (am, au) ← inputType env arg active
        mentions := mentions || am
        unknown := unknown || au
    -- A neutral type family is allowed with its actual local binder context.
    if head.isFVar then return (mentions, unknown)
    let .const name levels := head | return (mentions, true)
    if Lean.isClass env name then
      return (mentions, unknown || !listedTypeClasses.contains name)
    if listedPropositions.contains name then return (mentions, unknown)
    let some (.inductInfo info) := env.find? name | return (mentions, true)
    if active.contains reduced then return (mentions, unknown)
    if active.any (fun e => e.getAppFn == head) then return (mentions, true)
    for ctorName in info.ctors do
      let some ctor := env.find? ctorName | return (mentions, true)
      let mut ctorType := ctor.type.instantiateLevelParams ctor.levelParams levels
      for arg in args[:info.numParams] do
        let .forallE _ _ body _ := ctorType | return (mentions, true)
        ctorType := body.instantiate1 arg
      let (cm, cu) ← inputType env ctorType (active.push reduced) false
      mentions := mentions || cm
      unknown := unknown || cu
    return (mentions, unknown)

-- Declared types and value binders share this contextual classifier. Constructor
-- results are scanned nominally; their input types require a positive verdict.
private def classifyType (env : Environment) (type : Expr) (context : Array Expr)
    (checkResult : Bool) : WalkM (Bool × Bool × Bool) := do
  let context := if type.hasLooseBVars then context else #[]
  let key := (type, context, checkResult)
  if let some cached := (← get).typeChecks[key]? then return cached
  let verdict ← inBinderContext context fun locals => do
    let type := type.instantiateRev locals
    let exact ← compareCanonical type (← get).statement
    let decision ← compareCanonical type (← get).decision
    let (mentions, unknown) ← inputType env type #[] checkResult
    return (exact || decision, mentions, unknown)
  modify fun s => { s with typeChecks := s.typeChecks.insert key verdict }
  return verdict

private def visitSummary (env : Environment) (origin : Name) (summary : Summary) : WalkM Unit := do
  for node in summary.nodes do
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
    modify fun s => { s with exprFuel := s.exprFuel - 1 }
    let node := summary.nodes[index]!
    let e := node.expr
    let occurrence := (e, node.position, node.context)
    if (← get).visited.contains occurrence then continue
    modify fun s => { s with visited := s.visited.insert occurrence }
    let dataPos := node.position == .dataPos
    let checkU (x : SyntaxNode) : WalkM Unit := do
      if dataPos && x.prop && closed x.expr && x.pContent then
        noteUnclassified (Unclassified.mk "closed_decision"
          (x.expr.getAppFn.constName?.getD `closed_decision)
          (namespaceLabel env (x.expr.getAppFn.constName?.getD origin)) origin)
    if dataPos && closed e && containsStatement[index]! && !(← compareCanonical e statement) then
      noteUnclassified (Unclassified.mk "statement_subterm"
        (e.getAppFn.constName?.getD `statement_subterm)
        (namespaceLabel env (e.getAppFn.constName?.getD origin)) origin)
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
            if let some h := resultHead i.type then
              if decisionFamily.contains h && !listedProducers.contains n then
                noteUnclassified (Unclassified.mk "unlisted_decision_producer" n (namespaceLabel env n) origin)
      if let some type := node.declaredType then
        if (← compareCanonical type statement) || (← compareCanonical type (← get).decision) then
          modify fun s => { s with forbidden := true }
        modify fun s => { s with typeObligations :=
          (type, #[], false, info.any (fun i => i.value?.isNone), n, origin) :: s.typeObligations }
        if inProtected env n && !(← get).queued.contains n then queue n node.position origin
      else modify fun s => { s with incomplete := true }
    | .app _ _ =>
      -- Check instantiated domains after scanning constant dependencies, so a
      -- large type cannot hide a known forbidden API behind budget exhaustion.
      let full := (e.getAppFn.constName?.bind (env.find? ·)).any (fun info => info.value?.isNone)
      modify fun s => { s with appObligations := (e, node.context, full, origin) :: s.appObligations }
      let args := e.getAppArgs
      if let .const head _ := e.getAppFn then
        if (head == ``Decidable.isTrue || head == ``Decidable.isFalse) && args.size > 0 then
          if ← compareCanonical args[0]! (← get).statement then
            modify fun s => { s with forbidden := true }
    | .lam _ t _ _ | .forallE _ t _ _ | .letE _ t _ _ _ =>
      modify fun s => { s with typeObligations :=
        (t, node.context, true, true, t.getAppFn.constName?.getD origin, origin) :: s.typeObligations }
      if let some typeIndex := node.children[0]? then checkU summary.nodes[typeIndex]!
    | .proj n _ _ => directProjection env n
    | .mvar _ => modify fun s => { s with incomplete := true }
    | _ => pure ()
    pending := node.children.toList ++ pending

private def visit (env : Environment) (pos : Position) (origin : Name) (e : Expr) : WalkM Unit := do
  let summary ← summarise env #[(pos, e)] (← get).exprFuel
  modify fun s => { s with counters.visits := s.counters.visits + summary.visits }
  visitSummary env origin summary

private def process (env : Environment) : WalkM Unit := do
  while !(← get).forbidden do
    let some (n, _, _) := (← get).pending.head? | do
      if let some (type, context, full, rejectUnknown, first, origin) := (← get).typeObligations.head? then
        modify fun s => { s with typeObligations := s.typeObligations.tail! }
        let (exact, mentions, unknown) ← classifyType env type context full
        if exact then modify fun s => { s with forbidden := true }
        else if mentions || rejectUnknown && unknown then
          noteUnclassified ⟨if mentions then "statement_mentioning_type" else "unclassified_argument_type",
            first, namespaceLabel env first, origin⟩
        continue
      if let some (e, context, full, origin) := (← get).appObligations.head? then
        modify fun s => { s with appObligations := s.appObligations.tail! }
        inBinderContext context fun locals => do
          if let some type ← appliedValueType (e.instantiateRev locals) then
            if !full then return
            let (_, mentions, unknown) ← classifyType env type #[] false
            if mentions || unknown then
              noteUnclassified ⟨"unclassified_argument_type", origin, namespaceLabel env origin, origin⟩
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

private def collectReadout (env : Environment) (theoremName address : Name) (readout : Expr) : CoreM WalkResult := do
  let scope := (moduleScopeCache.getState env).getD (classifyModules env)
  let env := moduleScopeCache.setState env (some scope)
  modifyEnv (moduleScopeCache.setState · (some scope))
  let some theoremInfo := env.find? theoremName | return { forbidden := false, unclassified := none, incomplete := true, walked := #[] }
  let statement := theoremInfo.type
  let decision := mkApp (mkConst ``Decidable) statement
  let computation : WalkM Unit := do
    visit env .dataPos address readout
    process env
  let (_, state) ← Meta.MetaM.run' <| computation.run {
    theoremName, statement, decision, summaries := summaryCache.getState env }
  let counters := { state.counters with chargedVisits := provenanceExpressionFuel - state.exprFuel }
  modifyEnv (summaryCache.setState · state.summaries)
  modifyEnv (countersCache.setState · counters)
  trace[InformationProvenance.check]
    "theorem={theoremName} P_constants_summarised={counters.summarisedConstants} visits={counters.visits} memo_hits={counters.memoHits} charged_visits={counters.chargedVisits} rechecked_nodes={counters.recheckedNodes} spine_arguments={counters.spineArguments} canonicalizations={counters.canonicalizations}"
  let names := state.walked.toArray.map Name.toString |>.qsort (· < ·)
  return (WalkResult.mk state.forbidden state.unclassified state.incomplete names)

private def safeCollect (env : Environment) (theoremName address : Name) (readout : Expr) : CoreM WalkResult :=
  tryCatchRuntimeEx (collectReadout env theoremName address readout)
    (fun _ => pure { forbidden := false, unclassified := none, incomplete := true, walked := #[] })

private def readoutClosureCurrent (theoremName : Name) (readout : Expr) : CoreM (Bool × Option (Array String)) := do
  let env ← getEnv
  let r ← safeCollect env theoremName (readout.getAppFn.constName?.getD `readout) readout
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
    | some e => safeCollect env theoremName address e
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
