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

/-- A fresh, fixed budget per comparison; exceptions propagate to the query's
incomplete result. Only types and identity data are reduced, never proof values. -/
private def boundedDefEq (a b : Expr) (decisionType : Bool := false) : MetaM Bool :=
  withCurrHeartbeats <| withOptions
    (fun o => (o.set `maxHeartbeats (10000 : Nat)).set `maxRecDepth (1024 : Nat)) <|
    withTransparency .default do
      -- Escalate only at the final semantic match. An alias may hide Decidable;
      -- its argument may discard a rigid binder only at default transparency.
      let a ← whnf a
      if decisionType && !a.isAppOfArity ``Decidable 1 then return false
      let a ← instantiateMVars (← whnf (if decisionType then a.appArg! else a))
      if a.hasMVar then throwError "unresolved provenance type"
      if a.hasFVar || a.hasLooseBVars then return false
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

private structure ClosureState where
  constants : NameHashSet := {}
  pending : List Name := []
  visited : Std.HashSet Expr := {}
  compared : Std.HashMap (Bool × Expr) Bool := {}
  classifiedTypes : Std.HashSet Expr := {}
  inferred : Std.HashMap Expr Expr := {}
  reduced : Std.HashMap Expr Expr := {}
  constantTypes : Std.HashMap Name (List Name × Expr) := {}
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

/-- One cache for the entire readout family/registration, across all its slots.
FVarIds are rigid, unique context identities; no metavariables enter these keys.
Constant types come directly from ConstantInfo once, then instantiate universes. -/
private def inferredType (e : Expr) : ClosureM Expr := do
  if let some type := (← get).inferred[e]? then return type
  let type ← match e with
    | .const name levels => do
      let (params, type) ← match (← get).constantTypes[name]? with
        | some cached => pure cached
        | none => do
          let info ← getConstInfo name
          let cached := (info.levelParams, info.type)
          modify fun s => { s with constantTypes := s.constantTypes.insert name cached }
          pure cached
      pure (type.instantiateLevelParams params levels)
    | _ => boundedMeta (inferType e)
  if type.hasMVar then throwError "unresolved provenance type"
  modify fun s => { s with inferred := s.inferred.insert e type }
  return type

private def reducedType (e : Expr) : ClosureM Expr := do
  if let some type := (← get).reduced[e]? then return type
  let type ← boundedMeta <| withTransparency .instances do instantiateMVars (← whnf e)
  if type.hasMVar then throwError "unresolved provenance type"
  modify fun s => { s with reduced := s.reduced.insert e type }
  return type

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

private def sameStatement (statement candidate : Expr) (decisionType := false) : ClosureM Bool := do
  if candidate.hasMVar then throwError "unresolved provenance type"
  -- Reduce under the active binder context before excluding open propositions:
  -- family x may discard x and expose the closed registered statement.
  let candidate ← reducedType candidate
  let key := (decisionType, candidate)
  if let some answer := (← get).compared[key]? then return answer
  let answer ← if ← mayMatch decisionType candidate then
    boundedDefEq candidate statement decisionType else pure false
  modify fun s => { s with compared := s.compared.insert key answer }
  return answer

/-- Classify by inferred types, including constructors and dependent projections.
Let variables are substituted by the contextual traversal before inference.
An open term may supply a closed type (e.g. f S x : Decidable S); no equality
query ever synthesizes values for binders or compares an open proposition. -/
private def classifyType (statement : Expr) (e : Expr) : ClosureM Unit := do
  if (← get).forbidden then return
  match e with
  | .sort .. | .lit .. | .forallE .. => return
  | _ => pure ()
  let type ← inferredType e
  if (← get).classifiedTypes.contains type then return
  modify fun s => { s with classifiedTypes := s.classifiedTypes.insert type }
  unless ← mayMatch true type do return
  let proposition ← boundedMeta (isProp type)
  -- A known data inductive head cannot become Decidable. Function and sort
  -- types cannot either. Leave aliases/projections/instance producers to whnf.
  unless proposition || type.isAppOfArity ``Decidable 1 do
    match type.getAppFn with
    | .forallE .. | .sort .. | .fvar .. => return
    | .const name _ =>
      if let some (.inductInfo _) := (← getEnv).find? name then return
    | _ => pure ()
  let type ← reducedType type
  let decision := !proposition && !type.isAppOfArity ``Decidable 1
  let candidate := if !proposition && !decision then type.appArg! else type
  -- Rule 2(a): an inhabitant of S; rule 2(b): an instance of Decidable S.
  if ← sameStatement statement candidate decision then
    modify fun s => { s with forbidden := true }

private def reach (name : Name) : ClosureM Unit := do
  if (← get).constants.contains name then return
  if (← get).constants.size >= provenanceConstantFuel then
    throwError "provenance constant budget"
  modify fun s => { s with
    constants := s.constants.insert name, pending := name :: s.pending }

/-- Binder-aware traversal: every let value is visited before its contextual
body. Local declarations stay in scope for inferType, including dependent
projection result types. Raw proof values are never reduced away. -/
private partial def visit (statement : Expr) (proofScan : Bool) (e : Expr) : ClosureM Unit :=
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
    classifyType statement e
    match e with
    | .const name _ => reach name
    | .app f a => visit statement proofScan f; visit statement proofScan a
    | .lam n t b bi | .forallE n t b bi =>
      visit statement proofScan t
      withLocalDecl n bi t fun x => visit statement proofScan (b.instantiate1 x)
    | .letE n t v b nd =>
      visit statement proofScan t
      visit statement proofScan v
      -- Instantiate even nondependent lets/haves; Meta's default zetaDelta
      -- intentionally hides their values when they predate its telescope.
      withLetDecl n t v (nondep := nd) fun _ =>
        visit statement proofScan (b.instantiate1 v)
    | .mdata _ b => visit statement proofScan b
    | .proj name _ b => reach name; visit statement proofScan b
    | _ => pure ()

/-- The dependency queue visits each ConstantInfo type and obtainable value.
Rule 2(c) and rule 3(iii) share exact theorem reachability: a theorem-dependent
proposition's constants and their types/values enter this same transitive queue.
After a forbidden hit, collection continues to completion for canonical payloads. -/
private def collectReadout (env : Environment) (theoremName : Name) (readout : Expr) :
    ClosureM (Bool × Option (Array String)) := do
  let some theoremInfo := env.find? theoremName | return (false, none)
  -- Prepare the registered statement once per readout, never once per constant.
  let statement ← boundedMeta (withTransparency .instances (whnf theoremInfo.type))
  if ← boundedMeta (hasNormalConstant 256 statement) then
    let (constants, _) ← boundedMeta (typeConstants env theoremInfo.type)
    let (decision, _) ← boundedMeta (typeConstants env (mkApp (mkConst ``Decidable) theoremInfo.type))
    modify fun s => { s with
      statementConstants := constants, decisionConstants := decision, filterEnabled := true }
  visit statement false readout
  while let name :: rest := (← get).pending do
    modify fun s => { s with pending := rest }
    let some info := env.find? name | throwError "unavailable provenance constant"
    -- Rule 3(i), rule 3(ii), and the shared rule 2(c)/3(iii), respectively.
    if provenanceJudgeAPIs.contains name then
      modify fun s => { s with forbidden := true }
    if generatedAddress name || judgePayload info then
      modify fun s => { s with forbidden := true }
    if name == theoremName then
      modify fun s => { s with forbidden := true }
    visit statement false (mkConst name (info.levelParams.map Level.param))
    visit statement false info.type
    match info.value? (allowOpaque := true) with
    | some value => visit statement info.isTheorem value
    | none =>
      if readout.isConstOf name || (info.isAxiom &&
          !#[`propext, `Classical.choice, `Quot.sound].contains name) then
        throwError "unavailable provenance definition"
  let s ← get
  return (s.forbidden, some (s.constants.toArray.map Name.toString |>.qsort (· < ·)))

/-- A query owns one fresh Meta context and one type-comparison cache. A total
200000-heartbeat/1024-depth bound also covers proof scanning and type inference.
Frozen registrations call this once at registration; the seal consumes metadata. -/
def readoutClosure (env : Environment) (theoremName : Name) (readout : Expr) :
    CoreM (Bool × Option (Array String)) := do
  trace[InformationProvenance.check] "{theoremName}: {readout.getAppFn.constName?}"
  tryCatchRuntimeEx (do
    withEnv env <| withCurrHeartbeats <| withOptions
      (fun o => (o.set `maxHeartbeats (200000 : Nat)).set `maxRecDepth (1024 : Nat)) <|
      (collectReadout env theoremName readout).run' {} |>.run')
    (fun _ => pure (false, none))

/-- IE-C050 precedes all readout-value diagnostics, including IE-C021. A family
is checked as one dependent function, covering every signature index without
sampling or enumerating realizations. Inline families use the realization owner
as their address; named families retain the defining constant's address. -/
def provenanceError (env : Environment) (root catalog theoremName realization : Name) :
    CoreM (Option String) := do
  let readout := readoutFamily env realization
  let address := readout.bind (·.getAppFn.constName?) |>.getD realization
  let (forbidden, closure) ← match readout with
    | some e => readoutClosure env theoremName e
    | none => pure (false, none)
  if !forbidden && closure.isSome then return none
  let reason := if closure.isNone then "incomplete_closure" else "forbidden_dependency"
  let payload := match closure with
    | some names => Json.arr (names.map Json.str)
    | none => Json.null
  return some s!"IE-C050 ClosedTruthReadout key={root}/{catalog}/{theoremName} \
    readout={address} reason={reason} provenance={payload.compress}"

end LeanInformationAudit.RegistrationGates
