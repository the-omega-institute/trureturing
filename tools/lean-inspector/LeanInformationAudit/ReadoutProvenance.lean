import Lean

namespace LeanInformationAudit.RegistrationGates
open Lean Meta

/-- Correctness bounds, independent of machine speed: at most 4096 constants,
524288 expression nodes, and forwarding recursion with fuel 256.
Exhaustion always means incomplete, including on the clean path. -/
def provenanceConstantFuel : Nat := 4096
def provenanceExpressionFuel : Nat := 524288

/-- These judge APIs cannot supply independent object readouts. Membership is
by declaration identity, independent of the theorem key's representation. -/
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

/-- The last check only compares already reduced, closed types. Reduction and
comparison each have a fresh fixed budget; either failure is incomplete. -/
private def boundedDefEq (a b : Expr) : MetaM Bool :=
  withCurrHeartbeats <| withOptions
    (fun o => (o.set `maxHeartbeats (10000 : Nat)).set `maxRecDepth (1024 : Nat)) <|
    withTransparency .default do
      isDefEq a b

initialize registerTraceClass `InformationProvenance.check
initialize registerTraceClass `InformationProvenance.filter

/-- Only expose record construction; never reduce a readout or a proof. -/
private def recordHead (env : Environment) : Nat → Expr → Option Expr
  | 0, _ => none
  | fuel + 1, e => do
    let args := e.getAppArgs
    match e.getAppFn with
    | .mdata _ body => recordHead env fuel (mkAppN body args)
    | .letE _ _ value body _ => recordHead env fuel (mkAppN (body.instantiate1 value) args)
    | .lam _ _ _ _ =>
      if args.isEmpty then some e else recordHead env fuel (e.getAppFn.beta args)
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

/-- Project schema carriers wherever elaboration inserts them, including implicit
motives for empty readouts. All other syntax, including explicit proof terms and
let annotations, stays raw. Each projection and syntax descent has fixed fuel. -/
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

/-- Native and legacy paths share the same raw readout-family extraction. The
legacy bridge contributes its type's realization argument, never its proof. -/
private def readoutFamily (env : Environment) (realization : Name) : Option Expr := do
  let info ← env.find? realization
  let root ← match info with
    | .thmInfo info => do
      let type ← recordHead env 256 info.type
      unless type.isAppOfArity
          `D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization 3 do none
      type.getAppArgs[2]?
    | .defnInfo _ => some (mkConst realization)
    | _ => none
  let value ← recordHead env 256 root
  let name ← value.getAppFn.constName?
  unless name == `D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.mk ||
      name == `LeanInformationAudit.StructuralPrimitiveRealization.mk do none
  familyCarriers env 256 (← value.getAppArgs[2]?)

/-- Generated names are recognized as declaration addresses, never as Name
values. Registry/catalog/proof builders append these reserved terminal segments,
locally or after the single root/arena/catalog segment. Projection builders put
all their products below __kernel_projection. Future catalog products retain
__catalog_ / __system_catalog_ prefixes. -/
private def generatedAddress : Name → Bool
  | .str parent suffix =>
      #["__information_unit", "__primitive_realization", "__structural_unit",
        "__structural_realization", "__information_catalog", "__lowers_escape",
        "__escape_enriched", "__trivial_in_catalog", "__state_enumeration",
        "__information_registration_diagnostic", "__kernel_projection"].contains suffix ||
      suffix.startsWith "__catalog_" || suffix.startsWith "__system_catalog_" ||
      generatedAddress parent
  | .num parent _ => generatedAddress parent
  | .anonymous => false

/-- Constructor families from RegistryTypes, SealCommand, AnalysisDisposition
and DispositionEvidence. Constructor membership comes from ConstantInfo's
induct field (including every constructor of the listed sum types). -/
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

private inductive CandidateClass where
  | proof | instance | family | data | proposition
  deriving Inhabited, BEq, Repr

private structure ConstantType where
  params : List Name
  type : Expr
  candidateClass : CandidateClass

/-- A registration-independent scan. Only closed normalized types leave the
binder context. Dependencies retain the raw type/value syntax, including proofs.
A failed scan is cached as incomplete, never as an empty successful list. -/
private structure ConstantCandidates where
  types : Array Expr := #[]
  dependencies : Array Name := #[]
  expressionCost : Nat := 0
  proofCost : Nat := 0
  incomplete : Bool := false
  deriving Inhabited

/-- Compilation-local, registration-independent metadata. This extension is not
serialized into oleans; scoped environment queries cannot leak cache entries. -/
private structure TypeCache where
  constants : Std.HashMap Name ConstantType := {}
  candidates : Std.HashMap Name ConstantCandidates := {}
  reduced : Std.HashMap Expr Expr := {}
  localPolicies : List (Name × ReducibilityStatus) := []
  overrides : List (Name × ReducibilityStatus) := []
  classes : List Name := []
  deriving Inhabited

private initialize typeCache : EnvExtension TypeCache ← registerEnvExtension (pure {})

/-- New declarations preserve cached results. Changing the reduction policy of
an existing declaration (including scoped/imported overrides), or class metadata,
invalidates them. Imported declarations themselves are immutable in this env. -/
private def compilationCache (env : Environment) : TypeCache := Id.run do
  let old := typeCache.getState env
  let overrides := (reducibilityExtraExt.getState env).map₂.toList
  let classes := (classExtension.getState env).outParamMap.map₂.toList.map Prod.fst
  let changed := old.overrides != overrides || old.classes != classes ||
    old.localPolicies.any (fun (n, status) => getReducibilityStatusCore env n != status)
  let cache := if changed then {} else old
  let localPolicies := env.constants.map₂.toList.map fun (n, _) =>
    (n, getReducibilityStatusCore env n)
  return { cache with localPolicies, overrides, classes }

private structure ClosureState where
  constants : NameHashSet := {}
  pending : List Name := []
  visited : Std.HashSet Expr := {}
  compared : Std.HashMap Expr Bool := {}
  decisionStatement : Expr := mkConst ``False
  classifiedTypes : Std.HashSet Expr := {}
  candidates : Std.HashSet Expr := {}
  inferred : Std.HashMap Expr Expr := {}
  reduced : Std.HashMap Expr Expr := {}
  cache : TypeCache := {}
  intersections : Std.HashMap (Bool × Name) Bool := {}
  statementConstants : NameHashSet := {}
  decisionConstants : NameHashSet := {}
  filterEnabled : Bool := false
  expressionFuel : Nat := provenanceExpressionFuel
  proofFuel : Nat := provenanceExpressionFuel
  forbidden : Bool := false

private abbrev ClosureM := StateRefT ClosureState MetaM

/-- All reduction/type inference has a fixed local heartbeat bound as well as
 the enclosing query bound. Only closed proposition types reach isDefEq. -/
private def boundedMeta (action : MetaM α) : MetaM α :=
  withCurrHeartbeats <| withOptions
    (fun o => (o.set `maxHeartbeats (10000 : Nat)).set `maxRecDepth (1024 : Nat)) action

/-- Strip the type telescope under rigid binders, then inspect its WHNF result.
Proof result types and proposition-valued type formers are distinct. A universe
parameter or stuck dependent result stays family-valued: specializing it may
expose Prop or Decidable. No proof/readout value is evaluated here. -/
private def constantType (name : Name) : ClosureM ConstantType := do
  if let some cached := (← get).cache.constants[name]? then return cached
  let info ← getConstInfo name
  let candidateClass ← boundedMeta <| withTransparency .default <|
    forallTelescopeReducing info.type fun _ result => do
      let result ← whnf result
      match result.getAppFn with
      | .fvar .. | .bvar .. | .proj .. => return .family
      | .sort .zero => return .proposition
      | .sort (.succ _) => return .data
      | .sort _ => return .family
      | .const n _ =>
        if n == ``Decidable || isClass (← getEnv) n then return .instance
        if ← isProp result then return .proof
        -- A stuck recursor/definition can reveal a family after specialization.
        if result.hasFVar then
          unless (← getConstInfo n).isInductive do return .family
        return .data
      | _ => return .family
  let cached := { params := info.levelParams, type := info.type, candidateClass }
  modify fun s => { s with cache.constants := s.cache.constants.insert name cached }
  trace[InformationProvenance.check] "class {name}: {repr candidateClass}"
  return cached

/-- Expression caches are local to a readout; rigid FVarIds never escape it.
Generic constant types/classes are shared by registrations in this compilation. -/
private def inferredType (e : Expr) : ClosureM Expr := do
  if let some type := (← get).inferred[e]? then return type
  let type ← match e with
    | .const name levels => do
      let cached ← constantType name
      pure (cached.type.instantiateLevelParams cached.params levels)
    | _ => boundedMeta (inferType e)
  if type.hasMVar then throwError "unresolved provenance type"
  modify fun s => { s with inferred := s.inferred.insert e type }
  return type

/-- Bounded type-only forwarding preserves open aliases at instances
transparency. Repeat after iota/projection reduction can reveal another alias. -/
private def normalizeType : Nat → Expr → MetaM Expr
  | 0, _ => throwError "provenance type forwarding budget"
  | fuel + 1, e => withTransparency .instances do
    let some forwarded := recordHead (← getEnv) 256 e
      | throwError "provenance type forwarding budget"
    let type ← instantiateMVars (← whnf forwarded)
    if type == forwarded then return type
    normalizeType fuel type

private def reducedType (e : Expr) : ClosureM Expr := do
  if let some type := (← get).reduced[e]? then return type
  let closed := !e.hasFVar && !e.hasLooseBVars && !e.hasMVar
  if closed then
    if let some type := (← get).cache.reduced[e]? then return type
  let type ← boundedMeta (normalizeType 256 e)
  if type.hasMVar then throwError "unresolved provenance type"
  modify fun s => { s with
    reduced := s.reduced.insert e type
    cache.reduced := if closed then s.cache.reduced.insert e type else s.cache.reduced }
  return type

/-- Soundness: for closed types, type-forwarded instances-transparency WHNF exposes the same
rigid head in any definitionally equal pair: the same constant (including
constructors), sort, or binder shape. Thus different rigid heads certify
inequality before isDefEq. Stuck projections/variables are unknown, never a
negative certificate. This is only a necessary condition, so matching heads
still require the bounded semantic check. WHNF exhaustion propagates as
incomplete_closure; it never produces a head mismatch or a clean result. -/
private def headsMayMatch (a b : Expr) : Bool :=
  match a.getAppFn, b.getAppFn with
  | .const n _, .const m _ => n == m
  | .sort _, .sort _ | .forallE .., .forallE .. | .lam .., .lam .. => true
  | .const .., .sort .. | .const .., .forallE .. | .const .., .lam ..
  | .sort .., .const .. | .sort .., .forallE .. | .sort .., .lam ..
  | .forallE .., .const .. | .forallE .., .sort .. | .forallE .., .lam ..
  | .lam .., .const .. | .lam .., .sort .. | .lam .., .forallE .. => false
  | _, _ => true

/-- A constant head in WHNF survives normalization. Inspect only type domains
and codomains under rigid binders; no full normalization or proof evaluation is
needed to exhibit a constant in nf(S). Without a witness we disable the filter,
including for pure binder/sort statements. Fuel exhaustion also disables it. -/
private def hasNormalConstant : Nat → Expr → MetaM Bool
  | 0, _ => pure false
  | fuel + 1, e => withTransparency .instances do
    let some e := recordHead (← getEnv) 256 e | return false
    let e ← whnf e
    if let .const name _ := e.getAppFn then
      match (← getEnv).find? name with
      | some (.inductInfo _) | some (.axiomInfo _) | some (.opaqueInfo _) => return true
      | some (.defnInfo _) => return ← hasNormalConstant fuel e
      | _ => pure ()
    match e with
    | .forallE n t b bi =>
      if ← hasNormalConstant fuel t then return true
      withLocalDecl n bi t fun x => hasNormalConstant fuel (b.instantiate1 x)
    | _ => return false

/-- The transitive constant closure includes declaration types, obtainable
values and inductive/recursor families (kernel reduction can expose constructors).
This is an overapproximation, never a claim of normal-form equality. -/
private def typeConstants (env : Environment) (e : Expr)
    (stopAt : NameHashSet := {}) : MetaM (NameHashSet × Bool) := do
  let mut seen : NameHashSet := {}
  let mut pending := e.getUsedConstants.toList
  while let name :: rest := pending do
    pending := rest
    if stopAt.contains name then return (seen, true)
    if seen.contains name then continue
    if seen.size >= provenanceConstantFuel then throwError "provenance type-closure budget"
    seen := seen.insert name
    let some info := env.find? name | throwError "unavailable provenance type constant"
    pending := info.getUsedConstantsAsSet.toList ++ pending
    Core.checkMaxHeartbeats "provenance type closure"
  return (seen, false)

/-- Soundness: definitionally equal closed types have coincident normal heads;
every constant in a normal form belongs to the original term's transitive
constant closure. Our irreducible-head witness ensures nf(S) contains a constant. Consequently
closure(T) disjoint from closure(S) implies T is not definitionally S. The same
argument applies to Decidable S. We use the union for the initial type filter,
then S alone for proposition comparisons. Unknown/open inputs fall back to the
semantic classifier; exhaustion remains incomplete, never a clean verdict. -/
private def mayMatch (decision : Bool) (candidate : Expr) : ClosureM Bool := do
  if !(← get).filterEnabled || candidate.hasFVar || candidate.hasLooseBVars then return true
  let s ← get
  let target := if decision then s.decisionConstants else s.statementConstants
  for name in candidate.getUsedConstants do
    if target.contains name then return true
    let shared ← match (← get).intersections[(decision, name)]? with
      | some answer => pure answer
      | none => do
        let (seen, answer) ← boundedMeta (typeConstants (← getEnv) (mkConst name) target)
        modify fun s => { s with intersections := s.intersections.insert (decision, name) answer }
        -- Only a completed disjoint search certifies every visited dependency.
        unless answer do
          modify fun s =>
            let cache := seen.toArray.foldl (fun c n => c.insert (decision, n) false) s.intersections
            { s with intersections := cache }
        pure answer
    if shared then return true
  trace[InformationProvenance.filter] "disjoint: {candidate}"
  return false

private def sameStatement (statement type : Expr) : ClosureM Bool := do
  -- Reduce the proposition argument separately: Decidable (family x) can be
  -- closed after family discards x, even though its raw syntax is open (F1).
  let decision := type.isAppOfArity ``Decidable 1
  let candidate ← if decision then reducedType type.appArg! else pure type
  if candidate.hasFVar || candidate.hasLooseBVars then return false
  if candidate.hasMVar then throwError "unresolved provenance type"
  let candidateType := if decision then mkApp (mkConst ``Decidable) candidate else candidate
  if let some answer := (← get).compared[candidateType]? then return answer
  let state ← get
  let target := if decision then state.decisionStatement else statement
  let answer ← if headsMayMatch candidateType target && (!decision || headsMayMatch candidate statement) then do
      if ← mayMatch false candidate then boundedDefEq candidate statement else pure false
    else pure false
  modify fun s => { s with compared := s.compared.insert candidateType answer }
  return answer

/-- Scan independently of S. Normalize before rejecting open types: a family
can discard a rigid binder, including inside the argument of Decidable (F1). -/
private def addCandidate (type : Expr) : ClosureM Unit := do
  if (← get).classifiedTypes.contains type then return
  modify fun s => { s with classifiedTypes := s.classifiedTypes.insert type }
  let type ← reducedType type
  let type ← if type.isAppOfArity ``Decidable 1 then do
      pure <| mkApp (mkConst ``Decidable) (← reducedType type.appArg!)
    else pure type
  unless type.hasFVar || type.hasLooseBVars do
    modify fun s => { s with candidates := s.candidates.insert type }

private def eligibleClass : CandidateClass → Bool
  | .proof | .instance | .family => true
  | .data | .proposition => false

/-- Decide from the head's declared result before inference. In particular,
Eq/And/etc. form propositions; they do not inhabit them. Rigid locals use their
binder type, and lets/projections/lambdas retain the open-alias treatment.
This selection never reduces a proof or a data-valued application. -/
private def candidateHead : Nat → Expr → ClosureM Bool
  | 0, _ => throwError "provenance head forwarding budget"
  | fuel + 1, e => do
    let args := e.getAppArgs
    match e.getAppFn with
    | .const name _ => return eligibleClass (← constantType name).candidateClass
    | .mdata _ body => candidateHead fuel (mkAppN body args)
    | .letE _ _ value body _ => candidateHead fuel (mkAppN (body.instantiate1 value) args)
    | .lam n t b bi =>
      if args.isEmpty then
        withLocalDecl n bi t fun x => candidateHead fuel (b.instantiate1 x)
      else candidateHead fuel (e.getAppFn.beta args)
    | .proj name index _ =>
      if let some projection := (getStructureInfo? (← getEnv) name).bind (·.getProjFn? index) then
        return eligibleClass (← constantType projection).candidateClass
      let some reduced := recordHead (← getEnv) fuel e
        | throwError "provenance projection forwarding budget"
      if reduced == e then return true -- unresolved dependent family
      candidateHead fuel reduced
    | .fvar id =>
      let type := (← id.getDecl).type
      match type.getAppFn with
      | .const name _ =>
        let cls := (← constantType name).candidateClass
        return cls == .proposition || cls == .family || name == ``Decidable || isClass (← getEnv) name
      | .sort .. => return false
      | _ => return true -- dependent binder/family, without inventing a value
    | _ => return false

private def classifyType (e : Expr) : ClosureM Unit := do
  -- Unspecialized constants are served by their own cached declared type.
  -- Universe-specialized constants and applications still need their instance.
  if let .const _ [] := e then return
  unless ← candidateHead 256 e do return
  addCandidate (← inferredType e)

private def reach (name : Name) : ClosureM Unit := do
  if (← get).constants.contains name then return
  if (← get).constants.size >= provenanceConstantFuel then
    throwError "provenance constant budget"
  modify fun s => { s with
    constants := s.constants.insert name, pending := name :: s.pending }

/-- Binder-aware traversal: every let value is visited before its contextual
body. Local declarations stay in scope for inferType, including dependent
projection result types. Raw proof values are never reduced away. -/
private partial def visit (proofScan : Bool) (e : Expr) : ClosureM Unit :=
  withIncRecDepth do
    Core.checkMaxHeartbeats "readout provenance"
    let s ← get
    if s.expressionFuel == 0 || (proofScan && s.proofFuel == 0) then
      throwError "provenance expression/proof-scan budget"
    modify fun s => { s with
      expressionFuel := s.expressionFuel - 1
      proofFuel := if proofScan then s.proofFuel - 1 else s.proofFuel }
    if s.visited.contains e then return
    modify fun s => { s with visited := s.visited.insert e }
    let e ← instantiateMVars e
    if e.hasMVar || e.hasLooseBVars then throwError "unresolved provenance expression"
    if e.getAppNumArgs > 256 then throwError "provenance argument budget"
    classifyType e
    match e with
    | .const name _ => reach name
    | .app f a => visit proofScan f; visit proofScan a
    | .lam n t b bi | .forallE n t b bi =>
      visit proofScan t
      withLocalDecl n bi t fun x => visit proofScan (b.instantiate1 x)
    | .letE n t v b nd =>
      visit proofScan t
      visit proofScan v
      -- Instantiate even nondependent lets/haves; Meta's default zetaDelta
      -- intentionally hides their values when they predate its telescope.
      withLetDecl n t v (nondep := nd) fun _ =>
        visit proofScan (b.instantiate1 v)
    | .mdata _ b => visit proofScan b
    | .proj name _ b => reach name; visit proofScan b
    | _ => pure ()

/-- Build once in a fresh binder/traversal context, sharing only closed metadata.
The root body uses this same scanner without memoisation on every registration. -/
private def scanConstant (info : ConstantInfo) : ClosureM ConstantCandidates := do
  let (incomplete, scan) ← (do
    tryCatchRuntimeEx (do
      addCandidate info.type
      visit false info.type
      if let some value := info.value? (allowOpaque := true) then
        visit info.isTheorem value
      return false)
      (fun _ => pure true) : ClosureM Bool).run { cache := (← get).cache }
  modify fun s => { s with cache := scan.cache }
  return {
    types := scan.candidates.toArray
    dependencies := scan.constants.toArray
    expressionCost := provenanceExpressionFuel - scan.expressionFuel
    proofCost := provenanceExpressionFuel - scan.proofFuel, incomplete }

private def constantCandidates (info : ConstantInfo) : ClosureM ConstantCandidates := do
  if let some entry := (← get).cache.candidates[info.name]? then return entry
  let entry ← scanConstant info
  modify fun s => { s with cache.candidates := s.cache.candidates.insert info.name entry }
  trace[InformationProvenance.check] "scan {info.name}: {entry.types.size} candidates"
  return entry

private def compareCandidates (statement : Expr) (types : Array Expr) : ClosureM Unit := do
  for type in types do
    if (← get).forbidden then break
    if ← sameStatement statement type then
      modify fun s => { s with forbidden := true }

/-- Reachability and API/generated checks are registration-specific. Every
transitively reached constant supplies its memoised candidates and raw edges;
only the readout's own definition is scanned again. Cached costs retain the
per-query exhaustion bounds, so reuse cannot turn an incomplete closure clean. -/
private def collectReadout (env : Environment) (theoremName : Name) (readout : Expr) :
    ClosureM (Bool × Option (Array String)) := do
  let some theoremInfo := env.find? theoremName | return (false, none)
  let statement ← reducedType theoremInfo.type
  let decisionStatement ← reducedType (mkApp (mkConst ``Decidable) statement)
  modify fun s => { s with decisionStatement }
  if ← boundedMeta (hasNormalConstant 256 statement) then
    let (constants, _) ← boundedMeta (typeConstants env theoremInfo.type)
    let (decision, _) ← boundedMeta (typeConstants env (mkApp (mkConst ``Decidable) theoremInfo.type))
    modify fun s => { s with
      statementConstants := constants, decisionConstants := decision, filterEnabled := true }
  visit false readout
  compareCandidates statement (← get).candidates.toArray
  while let name :: rest := (← get).pending do
    modify fun s => { s with pending := rest }
    let some info := env.find? name | throwError "unavailable provenance constant"
    -- Preserve the observable additional type-closure intersection filter.
    let _ ← mayMatch true info.type
    if provenanceJudgeAPIs.contains name || generatedAddress name || judgePayload info then
      modify fun s => { s with forbidden := true }
    let ownBody := readout.getAppFn.constName? == some name
    if (info.value? (allowOpaque := true)).isNone && (ownBody || (info.isAxiom &&
        !#[`propext, `Classical.choice, `Quot.sound].contains name)) then
      throwError "unavailable provenance definition"
    let entry ← if ownBody then scanConstant info else constantCandidates info
    let s ← get
    if entry.incomplete || entry.expressionCost > s.expressionFuel || entry.proofCost > s.proofFuel then
      throwError "provenance incomplete constant scan"
    modify fun s => { s with
      expressionFuel := s.expressionFuel - entry.expressionCost
      proofFuel := s.proofFuel - entry.proofCost }
    compareCandidates statement entry.types
    for dependency in entry.dependencies do reach dependency
  let s ← get
  return (s.forbidden || s.constants.contains theoremName,
    some (s.constants.toArray.map Name.toString |>.qsort (· < ·)))

/-- A query owns one fresh Meta context and one type-comparison cache. A total
200000-heartbeat/1024-depth bound also covers proof scanning and type inference.
Frozen registrations call this once at registration; the seal consumes metadata. -/
private def readoutClosureCurrent (theoremName : Name) (readout : Expr) :
    CoreM (Bool × Option (Array String)) := do
  let env ← getEnv
  trace[InformationProvenance.check] "{theoremName}: {readout.getAppFn.constName?}"
  tryCatchRuntimeEx (do
    withCurrHeartbeats <| withOptions
      (fun o => (o.set `maxHeartbeats (200000 : Nat)).set `maxRecDepth (1024 : Nat)) <|
      do
        let (answer, state) ← (tryCatchRuntimeEx (collectReadout env theoremName readout)
          (fun _ => pure (false, none))).run
          { cache := compilationCache env } |>.run'
        modifyEnv (typeCache.setState · state.cache)
        return answer)
    (fun _ => pure (false, none))

/-- Explicit environment queries are scoped; production registrations use the
current environment so its compilation-local cache survives the query. -/
def readoutClosure (env : Environment) (theoremName : Name) (readout : Expr) :
    CoreM (Bool × Option (Array String)) :=
  withEnv env (readoutClosureCurrent theoremName readout)

/-- IE-C050 precedes all readout-value diagnostics, including IE-C021. A family
is checked as one dependent function, covering every signature index without
sampling or enumerating realizations. Inline families use the realization owner
as their address; named families retain the defining constant's address. -/
def provenanceErrorCurrent (root catalog theoremName realization : Name) :
    CoreM (Option String) := do
  let env ← getEnv
  let readout := readoutFamily env realization
  let address := readout.bind (·.getAppFn.constName?) |>.getD realization
  let (forbidden, closure) ← match readout with
    | some e => readoutClosureCurrent theoremName e
    | none => pure (false, none)
  if !forbidden && closure.isSome then return none
  let reason := if closure.isNone then "incomplete_closure" else "forbidden_dependency"
  let payload := match closure with
    | some names => Json.arr (names.map Json.str)
    | none => Json.null
  return some s!"IE-C050 ClosedTruthReadout key={root}/{catalog}/{theoremName} \
    readout={address} reason={reason} provenance={payload.compress}"

/-- Scoped variant for explicit environment queries. -/
def provenanceError (env : Environment) (root catalog theoremName realization : Name) :
    CoreM (Option String) :=
  withEnv env (provenanceErrorCurrent root catalog theoremName realization)

end LeanInformationAudit.RegistrationGates
