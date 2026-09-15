import LeanInformationAudit.RegistrationGates
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import LeanInformationAudit.Sha256
import LeanInformationAudit.FixedSnapshot
import LeanInformationAudit.FrozenBaseline
import Lean

-- Reifier validation shares the registry module to preserve the seal import closure.
namespace LeanInformationAudit.RegistrationReifier
open Lean Meta D5.S3.ConceptDynamics.InformationEscape

register_option informationReifier.fuel : Nat := {
  defValue := 65536
  descr := "Lower-only expression traversal budget for the P1 reifier" }

/-- Every exception, including heartbeat/recursion exhaustion, fails certification. -/
def bounded (action : MetaM α) : MetaM α :=
  tryCatchRuntimeEx (RegistrationGates.budget action) fun e => do
    if (← e.toMessageData.toString).startsWith "P1." then throw e
    throwError "P1.IncompleteCheck: {e.toMessageData}"

def closed (e : Expr) : MetaM Unit := do
  if e.hasMVar || e.hasFVar || e.hasLooseBVars then
    throwError "P1.UnresolvedMetavariables: {e}"

private def canonical (e : Expr) : StateT Nat (Except String) Expr := do
  let fuel ← get
  if fuel == 0 then throw "P1.IncompleteCheck: expression fuel exhausted"
  set (fuel - 1)
  match e with
  | .app f a => return .app (← canonical f) (← canonical a)
  | .lam _ t b bi => return .lam .anonymous (← canonical t) (← canonical b) bi
  | .forallE _ t b bi => return .forallE .anonymous (← canonical t) (← canonical b) bi
  | .letE _ t v b nd => return .letE .anonymous (← canonical t) (← canonical v) (← canonical b) nd
  | .mdata m b => return .mdata m (← canonical b)
  | .proj n i b => return .proj n i (← canonical b)
  | _ => return e
termination_by structural e

private def normalizeNames (e : Expr) : MetaM Expr := do
  match (canonical e).run (min 65536 (informationReifier.fuel.get (← getOptions))) with
  | .ok (e, _) => return e
  | .error reason => throwError reason

private def difference (a b : Expr) (path := "type") : String := Id.run do
  if a.equal b then return ""
  match a, b with
    | .app f x, .app g y =>
      return if !f.equal g then difference f g (path ++ ".fn") else difference x y (path ++ ".arg")
    | .forallE _ t x bi, .forallE _ u y bj
    | .lam _ t x bi, .lam _ u y bj =>
      if bi != bj then return path
      return if !t.equal u then difference t u (path ++ ".domain") else difference x y (path ++ ".body")
    | .letE _ t v x nd, .letE _ u w y ne =>
      if nd != ne then return path
      if !t.equal u then return difference t u (path ++ ".type")
      return if !v.equal w then difference v w (path ++ ".value") else difference x y (path ++ ".body")
    | .proj n i x, .proj m j y =>
      return if n == m && i == j then difference x y (path ++ ".value") else path
    | .mdata m x, .mdata n y =>
      return if (Expr.mdata m (mkBVar 0)).equal (.mdata n (mkBVar 0)) then
        difference x y (path ++ ".body") else path
    | _, _ => return path
termination_by structural a

/-- Alpha-renaming only; deliberately NOT Expr's BEq or definitional equality. -/
def exact (a b : Expr) : MetaM Bool := bounded do
  closed a; closed b
  return (← normalizeNames a).equal (← normalizeNames b)

def requireExact (reason : String) (a b : Expr) : MetaM Unit := do
  unless ← exact a b do
    withOptions (fun o => (o.setBool `pp.universes true).setBool `pp.explicit true) do
      throwError "P1.{reason} path={difference (← normalizeNames a) (← normalizeNames b)}\nactual={a}\nexpected={b}"

def rigid (name : Name) : MetaM Expr := do
  let info ← getConstInfo name
  return mkConst name (info.levelParams.map Level.param)

/-- The content module is loaded by the registering client, never by the judge. -/
def providerModule : Name := `D5.S3.ConceptDynamics.InformationEscape.ReifierTemplates

def pointwiseProvider : Name := providerModule.str "pointwise"
def sensitivityProvider : Name := providerModule.str "sensitivity"
def variationProvider : Name := providerModule.str "variation"

private def pointwiseArenaName : Name :=
  `D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.pointwiseEqArena

/-- Build a closed telescope by abstraction alone, without a local or global environment. -/
private def pinForall (name : Name) (bi : BinderInfo) (domain : Expr)
    (body : Expr → Except MessageData Expr) : Except MessageData Expr := do
  let var := mkFVar ⟨name⟩
  return mkForall name bi domain ((← body var).abstract #[var])

private def pinForallD (name : Name) (domain : Expr)
    (body : Expr → Except MessageData Expr) : Except MessageData Expr :=
  pinForall name .default domain body

/-- Independent structural type pins. No provider lookup, type inference, or
normalization contributes to these expected telescopes. Binder names alone may vary. -/
private def providerType (name : Name) : Except MessageData Expr := do
  let zero := Level.zero
  let one := Level.succ zero
  let sensitivity := mkConst ``FiniteSlotSensitivity [zero, zero, zero]
  if name == variationProvider then
    let u := Level.param `u
    let v := Level.param `v
    let w := Level.param `w
    let arenaType := mkConst ``PrimitiveLawArena [u, v, w]
    pinForallD `A arenaType fun a => do
    let signature := mkApp (mkConst ``PrimitiveLawArena.signature [u, v, w]) a
    let object := mkApp (mkConst ``PrimitiveLawArena.toArena [u, v, w]) a
    let state := mkApp (mkConst ``Arena.State [u]) object
    let index := mkAppN (mkConst ``PrimitiveSignature.Index [u, v, w]) #[state, signature]
    pinForallD `i index fun i =>
    pinForallD `h (mkApp (mkConst ``FiniteSlotSensitivity [u, v, w]) a) fun h =>
      pure (mkApp (mkConst ``FiniteLawVariation [u, v, w]) a)
  else
    pinForall `X .implicit (mkSort one) fun x =>
    pinForall `Y .implicit (mkSort one) fun y =>
    pinForall `finite .instImplicit (mkApp (mkConst ``Fintype [zero]) x) fun finite =>
    pinForall `decX .instImplicit (mkApp (mkConst ``DecidableEq [one]) x) fun decX =>
    pinForall `decY .instImplicit (mkApp (mkConst ``DecidableEq [one]) y) fun decY => do
      let object := mkAppN (mkConst ``Arena.ofFintype [zero]) #[x, finite, decX]
      let arena := mkAppN (mkConst pointwiseArenaName) #[object, y, decY]
      if name == pointwiseProvider then
        let readoutType := mkForall .anonymous .default x y
        pinForallD `f readoutType fun f =>
        pinForallD `g readoutType fun g => do
          let statement ← pinForallD `x x fun arg =>
            pure (mkAppN (mkConst ``Eq [one]) #[y, mkApp f arg, mkApp g arg])
          let state := mkApp (mkConst ``Arena.State [zero])
            (mkApp (mkConst ``PrimitiveLawArena.toArena [zero, zero, zero]) arena)
          let realization := mkAppN
            (mkConst `D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.pointwiseEqRealization)
            #[state, y, decY, f, g]
          pure (mkAppN (mkConst ``LegacyPrimitiveRealization [zero, zero, zero]) #[arena, statement, realization])
      else if name == sensitivityProvider then
        pinForall `outputs .instImplicit (mkApp (mkConst ``Nontrivial [zero]) y) fun outputs =>
        pinForallD `h (mkApp (mkConst ``Arena.Nondegenerate [zero]) object) fun h =>
          pure (mkApp sensitivity arena)
      else throw m!"P1.UnsupportedDescriptor: unknown provider {name}"

/-- The complete provider decision consumes reflected metadata only. Fuel remains
lower-only, including for callers using the pure core directly. -/
def checkProviderPin (info : ConstantInfo) (owner : Name) (fuel : Nat := 65536) :
    Except MessageData ConstantInfo := do
  let name := info.name
  unless #[pointwiseProvider, sensitivityProvider, variationProvider].contains name do
    throw m!"P1.UnsupportedDescriptor: unknown provider {name}"
  unless info matches .thmInfo _ do
    throw m!"P1.UnsupportedDescriptor: provider is not a theorem {name}"
  let levels := if name == variationProvider then [Level.param `u, .param `v, .param `w] else []
  unless info.levelParams.length == levels.length do
    throw m!"P1.UnsupportedDescriptor: provider type pin universes {name}: {info.levelParams}"
  let actual := info.type.instantiateLevelParams info.levelParams levels
  let expected ← providerType name
  for e in #[actual, expected] do
    if e.hasMVar || e.hasFVar || e.hasLooseBVars then
      throw m!"P1.UnresolvedMetavariables: {e}"
  let normalize (e : Expr) : Except MessageData Expr :=
    match (canonical e).run (min 65536 fuel) with
    | .ok (e, _) => .ok e
    | .error reason => .error m!"{reason}"
  let a ← normalize actual
  let b ← normalize expected
  unless a.equal b do
    let reason := s!"UnsupportedDescriptor: provider type pin {name}"
    throw m!"P1.{reason} path={difference a b}\nactual={actual}\nexpected={expected}"
  unless owner == providerModule do
    throw m!"P1.UnsupportedDescriptor: provider module {name}: {owner}"
  return info

/-- Reflect imported ownership. Current declarations have no import index;
`checkedProvider` retains the current-module fallback in that case. -/
def declaringModuleOf (env : Environment) (name : Name) : Option Name :=
  (env.getModuleIdxFor? name).bind (env.header.moduleNames[·]?)

/-- Both insertion and persisted validation bind Name, raw type and declaring module.
A namespace spelling, even with an identical type, is not module ownership. -/
def checkedProvider (name : Name) : MetaM ConstantInfo := bounded do
  unless #[pointwiseProvider, sensitivityProvider, variationProvider].contains name do
    throwError "P1.UnsupportedDescriptor: unknown provider {name}"
  let env ← getEnv
  unless env.contains name do
    throwError "P1.UnsupportedDescriptor: missing provider {name}"
  let info ← getConstInfo name
  let owner := (declaringModuleOf env name).getD env.header.mainModule
  match checkProviderPin info owner (informationReifier.fuel.get (← getOptions)) with
  | .ok info => return info
  | .error message =>
    withOptions (fun o => (o.setBool `pp.universes true).setBool `pp.explicit true) do
      throwError message

/-- Only descriptor-created application sites beta-substitute a supplied lambda. -/
private def readoutBody (f arg : Expr) : Option Expr :=
  match f with
  | .lam _ _ body _ => some (body.instantiate1 arg)
  | .mdata data body => (readoutBody body arg).map (.mdata data)
  | _ => none
termination_by structural f

private def sourceSite (e : Expr) : Expr :=
  match e with
  | .app f arg => (readoutBody f arg).getD e
  | _ => e

/-- Instantiate the provider telescope without inferAppType's implicit beta step.
Only the two provider-created equality-side applications below may substitute. -/
def semanticSource (descriptor : Expr) : MetaM (Expr × Expr × Expr) := do
  closed descriptor
  unless descriptor.isAppOfArity pointwiseProvider 7 do
    throwError "P1.UnsupportedDescriptor: expected fully applied ReifierTemplates.pointwise"
  let .const provider levels := descriptor.getAppFn
    | throwError "P1.UnsupportedDescriptor: provider constant"
  let info ← checkedProvider provider
  discard <| checkedProvider sensitivityProvider
  discard <| checkedProvider variationProvider
  let mut type := info.type.instantiateLevelParams info.levelParams levels
  for arg in descriptor.getAppArgs do
    let .forallE _ _ body _ := type | throwError "P1.UnsupportedDescriptor: provider telescope"
    type := body.instantiate1 arg
  closed type
  unless type.isAppOfArity ``LegacyPrimitiveRealization 3 do
    throwError "P1.UnsupportedDescriptor: legacy triple missing"
  let args := type.getAppArgs
  let .forallE n domain body bi := args[1]! | throwError "P1.UnsupportedDescriptor: source family"
  unless body.isAppOfArity ``Eq 3 do throwError "P1.UnsupportedDescriptor: source equality"
  let eqArgs := body.getAppArgs
  let statement := Expr.forallE n domain
    (mkAppN body.getAppFn #[eqArgs[0]!, sourceSite eqArgs[1]!, sourceSite eqArgs[2]!]) bi
  return (args[0]!, statement, args[2]!)

private def arenaHead : Nat → Expr → MetaM Expr
  | 0, _ => throwError "P1.IncompleteCheck: arena head fuel exhausted"
  | fuel + 1, e => do
    if e.isAppOf `D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.pointwiseEqArena then return e
    match e with
    | .mdata _ body => arenaHead fuel body
    | _ =>
      let .const name levels := e.getAppFn | throwError "P1.ArenaMismatch: unsupported arena head"
      let some (.defnInfo info) := (← getEnv).find? name
        | throwError "P1.ArenaMismatch: unsupported arena declaration {name}"
      arenaHead fuel (info.value.instantiateLevelParams info.levelParams levels |>.beta e.getAppArgs)

/-- Freeze arena independently BEFORE descriptor elaboration or theorem matching. -/
def freezeArena (name : Name) : MetaM Expr := bounded do
  let arena ← rigid name
  closed arena
  let type ← inferType arena
  unless type.isAppOf ``PrimitiveLawArena do throwError "P1.ArenaMismatch: not a PrimitiveLawArena"
  unless (← getConstInfo name).levelParams.isEmpty do throwError "P1.RigidUniverseMismatch: arena"
  unless type.equal (mkConst ``PrimitiveLawArena [.zero, .zero, .zero]) do
    throwError "P1.RigidUniverseMismatch: arena must have three zero universe levels"
  return arena

def exactUse (theoremName : Name) (arena descriptor : Expr) : MetaM (Expr × Expr) := do
  let info ← getConstInfo theoremName
  unless info.levelParams.isEmpty do throwError "P1.RigidUniverseMismatch: {theoremName}"
  let (bridgeArena, statement, realization) ← semanticSource descriptor
  requireExact "ArenaMismatch" (← arenaHead 128 arena) bridgeArena
  requireExact s!"StatementIdentityMismatch theorem={theoremName} template=ReifierTemplates.pointwise arena={arena} bridge={descriptor}"
    info.type statement
  let expected ← mkAppM ``PrimitiveRealization #[← mkAppM ``PrimitiveLawArena.signature #[arena]]
  unless ← isDefEq (← inferType realization) expected do throwError "P1.BridgeBindingMismatch: signature"
  closed (← instantiateMVars expected)
  return (info.type, realization)

def occurrenceBinding (e : InformationRegistryEntry) : Array Name := #[
  e.theoremName, e.unitName, e.arenaName, e.realizationName, e.variationWitness,
  e.sensitivityWitness, e.catalogId, e.registrationModuleName, e.objectArenaName,
  e.resolvedArenaName, e.canonicalObjectArenaName, e.effectiveCatalogId]

private def declaration (name : Name) (type value : Expr) (proof := true) : MetaM Unit := do
  let type ← instantiateMVars type
  let value ← instantiateMVars value
  closed type; closed value
  if proof then
    addDecl (.thmDecl { name, levelParams := [], type, value })
  else
    addAndCompile (.defnDecl { name, levelParams := [], type, value, hints := .abbrev, safety := .safe })
  unless ← RegistrationGates.checked name type do throwError "P1.MissingEvidence: kernel/axioms {name}"

def unitValue (e : InformationRegistryEntry) : MetaM Expr := do
  mkAppM ``LegacyPrimitiveRealization.toTheoremUnit #[← rigid e.realizationName, ← rigid e.theoremName]

/-- No per-registration witness declarations: create the name-based gate inputs. -/
def derive (e : InformationRegistryEntry) (arena descriptor : Expr)
    (outputEvidence : Option Expr := none) : MetaM InformationRegistryEntry := bounded do
  let (statement, realization) ← exactUse e.theoremName arena descriptor
  let bridgeType ← mkAppM ``LegacyPrimitiveRealization #[arena, statement, realization]
  declaration e.realizationName bridgeType descriptor
  let nd := e.unitName.str "__nondegenerate"
  let ndType ← mkAppM ``Arena.Nondegenerate #[← mkAppM ``PrimitiveLawArena.toArena #[arena]]
  let some nondegenerate ← RegistrationGates.attempt (reduceEval (← mkDecide ndType) : MetaM Bool)
    | throwError "P1.IncompleteCheck: nondegeneracy decision"
  unless nondegenerate do throwError "P1.IE-C004 DegenerateArena: {e.arenaName}"
  let ndProof ← mkDecideProof ndType
  declaration nd ndType ndProof
  let params := descriptor.getAppArgs.extract 0 5
  let output := params[1]!
  let expected ← mkAppM ``Nontrivial #[output]
  let nontrivial ← match outputEvidence with
    | some value => pure value
    | none =>
      let .some value ← trySynthInstance expected
        | throwError "P1.MissingEvidence: Nontrivial {output}"
      pure value
  closed nontrivial
  unless ← isDefEq (← inferType nontrivial) expected do throwError "P1.MissingEvidence: output type"
  let sensitivity := e.unitName.str "__sensitivity"
  let sensitivityValue := mkAppN (mkConst sensitivityProvider)
    (params ++ #[nontrivial, ← rigid nd])
  declaration sensitivity (← mkAppM ``FiniteSlotSensitivity #[arena]) sensitivityValue
  let variation := e.unitName.str "__variation"
  let variationValue ← mkAppM variationProvider #[arena, mkConst ``Bool.false, ← rigid sensitivity]
  declaration variation (← mkAppM ``FiniteLawVariation #[arena]) variationValue
  let value ← unitValue e
  declaration e.unitName (← inferType value) value false
  let e := { e with variationWitness := variation, sensitivityWitness := sensitivity }
  return { e with derivedCertificate := some {
    occurrence := occurrenceBinding e, catalogKind := e.catalogKind,
    localRegistrationNames := e.localRegistrationNames, statementIdentity := e.statementIdentity,
    levelParams := (← getConstInfo e.theoremName).levelParams, statement,
    descriptor, arena, nondegenerate := nd, outputEvidence := nontrivial } }

/-- Full arena-indexed witness types and permitted axiom closures, not labels. -/
def lawSensitive (entry : InformationRegistryEntry) (arena : Expr) : MetaM Unit := do
  for (name, predicate) in #[(entry.variationWitness, ``FiniteLawVariation),
      (entry.sensitivityWitness, ``FiniteSlotSensitivity)] do
    unless ← RegistrationGates.checked name (← mkAppM predicate #[arena]) do
      throwError "P1.WitnessBindingMismatch: {name}"

/-- Shared insertion classification for a nonempty finite diagnostic. -/
def checkDiagnostic (diagnostic : String) : MetaM Unit := do
  if (diagnostic.splitOn " reason=incomplete_closure ").length > 1 then
    throwError "P1.IncompleteCheck: {diagnostic}"
  throwError "P1.SemanticRejected: {diagnostic}"

/-- Consume the completed registration-time scan, bound to the same immutable
module as the checked unit. Publication never executes the runtime scanner. -/
def closedTruthExcluded (entry : InformationRegistryEntry) : MetaM Unit := bounded do
  let some cert := entry.derivedCertificate | throwError "P1.MissingEvidence: uniform source"
  discard <| exactUse entry.theoremName cert.arena cert.descriptor
  let name := RegistrationGates.diagnosticName entry.unitName entry.registrationModuleName
  let info ← getConstInfo name
  let env ← getEnv
  unless env.getModuleIdxFor? name == env.getModuleIdxFor? entry.unitName &&
      info.type.equal (mkConst ``String) && info.value?.any (·.equal (mkStrLit "")) do
    throwError "P1.SemanticRejected: incomplete or unbound registration diagnostic"

/-- Consumer validation of persisted inputs, including copied/stale occurrence data. -/
def validateDerivedCertificate (entry : InformationRegistryEntry) : MetaM Unit := bounded do
  let some cert := entry.derivedCertificate | return
  let env ← getEnv
  let owner := env.getModuleIdxFor? entry.unitName |>.map
    (env.allImportedModuleNames[·]!) |>.getD env.header.mainModule
  unless cert.occurrence == occurrenceBinding entry && owner == entry.registrationModuleName &&
      cert.catalogKind == entry.catalogKind &&
      cert.localRegistrationNames == entry.localRegistrationNames &&
      cert.statementIdentity == entry.statementIdentity &&
      cert.levelParams == (← getConstInfo entry.theoremName).levelParams do
    throwError "P1.CertificateBindingMismatch: {entry.theoremName}"
  requireExact "CertificateBindingMismatch" cert.arena (← freezeArena entry.arenaName)
  let (statement, realization) ← exactUse entry.theoremName cert.arena cert.descriptor
  unless cert.statement.equal statement do
    throwError "P1.CertificateBindingMismatch: retained original statement"
  let bridge ← getConstInfo entry.realizationName
  requireExact "BridgeBindingMismatch" bridge.type
    (← mkAppM ``LegacyPrimitiveRealization #[cert.arena, statement, realization])
  let some value := bridge.value? (allowOpaque := true) | throwError "P1.BridgeBindingMismatch: no value"
  requireExact "BridgeBindingMismatch" value cert.descriptor
  let unit ← getConstInfo entry.unitName
  let some value := unit.value? | throwError "P1.UnitBindingMismatch: no value"
  let expectedUnit ← unitValue entry
  requireExact "UnitBindingMismatch" value expectedUnit
  requireExact "UnitBindingMismatch" unit.type (← inferType expectedUnit)
  for name in #[entry.realizationName, entry.unitName, entry.variationWitness,
      entry.sensitivityWitness, cert.nondegenerate] do
    unless (← getConstInfo name).levelParams.isEmpty do throwError "P1.RigidUniverseMismatch: {name}"
  let ndType ← mkAppM ``Arena.Nondegenerate #[← mkAppM ``PrimitiveLawArena.toArena #[cert.arena]]
  requireExact "WitnessBindingMismatch" (← getConstInfo cert.nondegenerate).type ndType
  unless ← RegistrationGates.checked cert.nondegenerate ndType do throwError "P1.MissingEvidence: nondegenerate"
  let sensitivity ← getConstInfo entry.sensitivityWitness
  requireExact "WitnessBindingMismatch" sensitivity.type (← mkAppM ``FiniteSlotSensitivity #[cert.arena])
  let some value := sensitivity.value? (allowOpaque := true)
    | throwError "P1.WitnessBindingMismatch: missing sensitivity"
  requireExact "WitnessBindingMismatch" value
    (mkAppN (mkConst sensitivityProvider)
      (cert.descriptor.getAppArgs.extract 0 5 ++ #[cert.outputEvidence, ← rigid cert.nondegenerate]))
  let variation ← getConstInfo entry.variationWitness
  requireExact "WitnessBindingMismatch" variation.type (← mkAppM ``FiniteLawVariation #[cert.arena])
  let some value := variation.value? (allowOpaque := true)
    | throwError "P1.WitnessBindingMismatch: missing variation"
  requireExact "WitnessBindingMismatch" value
    (← mkAppM variationProvider #[cert.arena, mkConst ``Bool.false, ← rigid entry.sensitivityWitness])
  lawSensitive entry cert.arena

end LeanInformationAudit.RegistrationReifier

namespace LeanInformationAudit

open Lean
open Lean.Meta

private def theoremUnitName : Name :=
  `D5.S3.ConceptDynamics.InformationEscape.TheoremUnit

private def primitiveLawArenaName : Name :=
  `D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena

private def primitiveRealizationName : Name :=
  `D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization

private def legacyPrimitiveRealizationName : Name :=
  `D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization

def theoremUnitSuffix := "__information_unit"

def primitiveRealizationSuffix := "__primitive_realization"

def generatedCompanionSuffixes : Array String := #[
  theoremUnitSuffix,
  primitiveRealizationSuffix,
  "__lowers_escape",
  "__trivial_in_catalog",
  "__escape_enriched",
  "__information_catalog",
  "__catalog_irredundant",
  "__catalog_redundant",
  "__system_catalog_irredundant",
  "__system_catalog_not_irredundant",
  "__information_registration_diagnostic"
]

def InformationRegistryEntry.lawArenaName (entry : InformationRegistryEntry) : Name :=
  entry.arenaName

/-- A correctness bound, independent of host speed and caller heartbeat options.
Every head transition, declaration lookup and environment lookup spends one unit. -/
def arenaAliasWorkBudget : Nat := 4096

/-- Elaboration provenance for a structure literal, retained across olean imports.
Lean's structure elaborator eta-contracts field-copy literals before storing them. -/
def arenaConstructionMarker : Name := `LeanInformationAudit.arenaConstruction

private inductive AliasClosure where
  | mk (term : Expr) (bindings : List AliasClosure)

/-- Fuelled weak-head reduction of forwarding aliases only (delta/beta/zeta).
Closures avoid substitution and never traverse or normalize argument subtrees.
Unlike unrestricted `whnfR`, this stops at constructors, projections and recursors,
and never performs structure eta. A bare named target becomes the next owner;
an application that constructs a value retains the last named owner.
The single budget covers both outer aliases and all work inside applications. -/
def resolveCanonicalArenaName (spelling : Name) : MetaM Name := do
  let env ← getEnv
  unless env.contains spelling do return spelling
  let mut owner := spelling
  let mut current := AliasClosure.mk (mkConst spelling) []
  let mut arguments : List AliasClosure := []
  let mut fuel := arenaAliasWorkBudget
  while fuel > 0 do
    fuel := fuel - 1
    let .mk term bindings := current
    match term with
    | .mdata data body =>
      if data.contains arenaConstructionMarker then return owner
      current := .mk body bindings
    | .app fn arg =>
      arguments := .mk arg bindings :: arguments
      current := .mk fn bindings
    | .letE _ _ value body _ =>
      current := .mk body (.mk value bindings :: bindings)
    | .lam _ _ body _ =>
      match arguments with
      | [] => return owner
      | arg :: rest =>
        arguments := rest
        current := .mk body (arg :: bindings)
    | .bvar index =>
      match bindings with
      | [] => throwError "IE-C003 ArenaResolutionFailed: {spelling}"
      | value :: rest =>
        current := if index == 0 then value else .mk (.bvar (index - 1)) rest
    | .const name _ =>
      if arguments.isEmpty then owner := name
      match env.find? name with
      | some (.defnInfo info) => current := .mk info.value []
      | _ => return owner
    | _ => return owner
  throwError "IE-C003 ArenaResolutionBudgetExceeded arena={spelling} limit={arenaAliasWorkBudget}"

def InformationRegistryEntry.occurrenceKey
    (entry : InformationRegistryEntry) : Name × Name :=
  (entry.canonicalObjectArenaName, entry.theoremName)

/-- The naming function used for all occurrence-qualified companions. -/
def catalogQualifiedName (rootId objectArenaName : Name) (catalogId : CatalogId)
    (theoremName : Name) (suffix : String) : Name :=
  theoremName
    |>.str (rootId.toString ++ "/" ++ objectArenaName.toString ++ "/" ++
      catalogId.toString)
    |>.str suffix

private def jsonStringArray (values : Array String) : String :=
  (Json.arr <| values.map Json.str).compress

def InformationRegistryEntry.occurrenceKeyString
    (entry : InformationRegistryEntry) : String :=
  entry.canonicalObjectArenaName.toString ++ "/" ++ entry.theoremName.toString

def qualifiedNameCollisionError (rootId : Name) (catalogId : CatalogId)
    (generatedName : Name) (entries : Array InformationRegistryEntry) : String :=
  let occurrences := entries.map (·.occurrenceKeyString) |>.toList.eraseDups.toArray
    |>.qsort (· < ·)
  s!"IE-C025 QualifiedNameCollision root={rootId} catalog={catalogId} \
generated_name={generatedName} occurrences={jsonStringArray occurrences}"

def qualifiedNameCollisionEntries (entries : Array InformationRegistryEntry)
    (generatedName : Name) (prospective : InformationRegistryEntry) :
    Array InformationRegistryEntry :=
  let owners := (entries.filter fun entry =>
    entry.unitName == generatedName || entry.realizationName == generatedName).push prospective
  owners.foldl (init := #[]) (fun result entry =>
    if result.any (fun owner => owner.occurrenceKey == entry.occurrenceKey) then result
    else result.push entry)
    |>.qsort (fun left right => left.occurrenceKeyString < right.occurrenceKeyString)

def rejectKernelAddressSemanticUse (rootId : Name) (catalogId : CatalogId)
    (address consumer : String) : Except String Unit :=
  .error s!"IE-C030 KernelAddressUsedAsSemanticEvidence root={rootId} \
catalog={catalogId} address={address} consumer={consumer}"

private initialize informationRegistryExt :
    SimplePersistentEnvExtension InformationRegistryEntry
      (Array InformationRegistryEntry) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun ess => ess.foldl (· ++ ·) #[]
  }

def InformationRegistry.entries (env : Environment) :
    Array InformationRegistryEntry :=
  informationRegistryExt.getState env

def InformationRegistry.find? (env : Environment) (theoremName : Name) :
    Option InformationRegistryEntry :=
  (entries env).find? fun entry => entry.theoremName == theoremName

def InformationRegistry.hasTheorem (env : Environment) (n : Name) : Bool :=
  (find? env n).isSome

def InformationRegistry.hasOccurrence (env : Environment)
    (objectArena theoremName : Name) : Bool :=
  (entries env).any fun entry =>
    entry.canonicalObjectArenaName == objectArena && entry.theoremName == theoremName

def InformationRegistry.hasUnit (env : Environment) (n : Name) : Bool :=
  (entries env).any fun entry => entry.unitName == n

/-- A deterministic identity for the theorem type stored in the elaborated environment. -/
def theoremStatementIdentity (env : Environment) (theoremName : Name) : String :=
  match env.find? theoremName with
  | some (.thmInfo info) => "sha256:" ++ Sha256.hex (toString info.type).toUTF8
  | _ => ""

/-- One independently declared row in a sealing root's expected-occurrence manifest. -/
structure ExpectedOccurrence where
  rootId : Name
  objectArenaName : Name
  theoremName : Name
  statementIdentity : String
  registrationModuleName : Name
  deriving Inhabited, Repr

private initialize expectedOccurrenceExt :
    SimplePersistentEnvExtension ExpectedOccurrence (Array ExpectedOccurrence) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun ess => ess.foldl (· ++ ·) #[]
  }

namespace ExpectedOccurrenceManifest

def declaredEntries (env : Environment) (rootId : Name) : Array ExpectedOccurrence :=
  expectedOccurrenceExt.getState env |>.filter (·.rootId == rootId)

def addEntry (env : Environment) (entry : ExpectedOccurrence) : Environment :=
  expectedOccurrenceExt.addEntry env entry

end ExpectedOccurrenceManifest

def frozenInformationRootId : Name :=
  `D5.S3.ConceptDynamics.InformationEscape.InformationRoot

/-- Companions of imported objects belong to this compilation, not the object's module.
Lean's private names preserve local source resolution while separating compiled roots.
The frozen root retains its public declarations: they are part of its frozen statement
identity and are consumed by SharedInformationRoot and SealBaseline. -/
def localCompanionName (env : Environment) (owner : Name) (suffix : String) : Name :=
  let name := owner.str suffix
  if env.header.mainModule == frozenInformationRootId || !env.isImportedConst owner then name
  else mkPrivateName env name

def designatedInformationRootId : Name :=
  `D5.S3.ConceptDynamics.InformationEscape.SharedInformationRoot

private def snapshotExpectations (rootId : Name) (rows : Array SnapshotOccurrence) :
    Array ExpectedOccurrence :=
  rows.map fun row => {
    rootId
    objectArenaName := row.objectArenaName
    theoremName := row.theoremName
    statementIdentity := row.statementIdentity
    registrationModuleName := row.registrationModuleName
  }

/-- Read-only expectations captured by SnapshotEnumerator, independently of the root. -/
def fixedSnapshotOccurrences (rootId : Name) : Array ExpectedOccurrence :=
  snapshotExpectations rootId fixedInformationSourceSnapshot.occurrences

/-- The historical frozen root is independent of future source snapshot generation. -/
def frozenBaselineOccurrences (rootId : Name) : Array ExpectedOccurrence :=
  snapshotExpectations rootId frozenInformationRootBaseline

/-- Resolve the independent expectation source for one sealing root. -/
def expectedOccurrencesForRoot (env : Environment) (rootId : Name) :
    Array ExpectedOccurrence :=
  if rootId == frozenInformationRootId then
    frozenBaselineOccurrences rootId
  else if rootId == designatedInformationRootId then
    fixedSnapshotOccurrences rootId
  else
    ExpectedOccurrenceManifest.declaredEntries env rootId

def isCompanionName : Name -> Bool
  | .str _ suffix =>
      generatedCompanionSuffixes.contains suffix
  | _ => false

/-- Complete, deterministic payload shared by prechecks, insertion and sealing.
`entries` contains every contributing registration, including a prospective one
when rejecting insertion; module names are a sorted set, count counts entries. -/
def duplicateRegistrationError (entry : InformationRegistryEntry)
    (entries : Array InformationRegistryEntry) : String :=
  let modules := entries.map (·.registrationModuleName.toString)
    |>.toList.eraseDups.toArray |>.qsort (· < ·)
  s!"IE-C002 DuplicateRegistration object_arena={entry.canonicalObjectArenaName} \
theorem_name={entry.theoremName} registration_modules={jsonStringArray modules} \
count={entries.size}"

/-- Resolve the prospective owner before any admission precheck. -/
def prepareRegistrationEntry (env : Environment)
    (entry : InformationRegistryEntry) : MetaM InformationRegistryEntry := do
  let spelling := if entry.objectArenaName.isAnonymous then entry.arenaName
    else entry.objectArenaName
  let resolvedArenaName ← resolveCanonicalArenaName spelling
  return { entry with
    resolvedArenaName
    registrationModuleName := if entry.registrationModuleName.isAnonymous then
      env.header.mainModule else entry.registrationModuleName }


private def statementMismatchError (name : Name) : String :=
  s!"IE-C006 StatementProofMismatch: {name}"

/-- Perform the environment-only checks shared by admission and sealing. -/
private def validateEntryDeclarations (env : Environment)
    (entry : InformationRegistryEntry) :
    Except String Unit := do
  if isCompanionName entry.theoremName then
    throw s!"IE-C011 GeneratedCertificateRegistered: {entry.theoremName}"
  match env.find? entry.theoremName with
  | some (.thmInfo _) => pure ()
  | _ => throw s!"IE-C001 UnregisteredTheoremUnit: {entry.theoremName}"
  unless env.contains entry.unitName do
    throw (statementMismatchError entry.theoremName)
  unless env.contains entry.arenaName do
    throw s!"IE-C003 ArenaResolutionFailed: {entry.arenaName}"
  unless env.contains entry.canonicalObjectArenaName do
    throw s!"IE-C003 ArenaResolutionFailed: {entry.canonicalObjectArenaName}"
  unless env.contains entry.realizationName do
    throw (statementMismatchError entry.theoremName)
  let unitInfo := env.find? entry.unitName |>.get!
  unless unitInfo.type.getAppFn.constName? == some theoremUnitName do
    throw (statementMismatchError entry.theoremName)

def compilePrimitiveBundle (arenaExpr realizationExpr : Expr) : MetaM Expr := do
  let realizationType <- instantiateMVars (← whnfR (← inferType realizationExpr))
  unless realizationType.getAppFn.constName? == some primitiveRealizationName do
    throwError "realization type mismatch"
  let realizationArgs := realizationType.getAppArgs
  unless realizationArgs.size == 2 do
    throwError "realization argument mismatch"
  let expectedSignature <- mkAppM
    `D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.signature
    #[arenaExpr]
  unless ← isDefEq realizationArgs[1]! expectedSignature do
    throwError "realization signature mismatch"
  let arenaValue <- mkAppM
    `D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.toArena
    #[arenaExpr]
  let stateType <- mkAppM
    `D5.S3.ConceptDynamics.InformationEscape.Arena.State #[arenaValue]
  let stateDecidableEq <- mkAppM
    `D5.S3.ConceptDynamics.InformationEscape.Arena.stateDecidableEq #[arenaValue]
  let compiler <- mkConstWithFreshMVarLevels
    `D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle
  return mkAppN compiler
    #[stateType, realizationArgs[1]!, stateDecidableEq, realizationExpr]

/-- Complete the declaration and definitional-equality checks shared by both phases. -/
private def validateEntryCore (env : Environment) (entry : InformationRegistryEntry) :
    MetaM (Except String Unit) := do
  match validateEntryDeclarations env entry with
  | .error message => return .error message
  | .ok () => pure ()
  try
    if entry.derivedCertificate.isSome then
      unless entry.statementIdentity == theoremStatementIdentity env entry.theoremName &&
          entry.resolvedArenaName == (← prepareRegistrationEntry env entry).resolvedArenaName do
        return .error "P1.CertificateBindingMismatch: current statement identity or arena ownership"
    RegistrationReifier.validateDerivedCertificate entry
  catch e => return .error (← e.toMessageData.toString)
  tryCatchRuntimeEx (do
    let theoremExpr <- mkConstWithFreshMVarLevels entry.theoremName
    let theoremType <- instantiateMVars (← whnfR (← inferType theoremExpr))
    let unitExpr <- mkConstWithFreshMVarLevels entry.unitName
    let unitType <- instantiateMVars (← whnfR (← inferType unitExpr))
    unless unitType.getAppFn.constName? == some theoremUnitName do
      return .error (statementMismatchError entry.theoremName)
    let unitArgs := unitType.getAppArgs
    if unitArgs.isEmpty then
      return .error (statementMismatchError entry.theoremName)
    let arenaExpr <- mkConstWithFreshMVarLevels entry.arenaName
    let arenaType <- instantiateMVars (← whnfR (← inferType arenaExpr))
    unless arenaType.getAppFn.constName? == some primitiveLawArenaName do
      return .error s!"IE-C003 ArenaResolutionFailed: {entry.arenaName}"
    let expectedArena <- mkAppM
      `D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.toArena
      #[arenaExpr]
    let objectArenaExpr <- if entry.objectArenaName.isAnonymous then
      pure expectedArena
    else
      let objectArenaExpr <- mkConstWithFreshMVarLevels entry.objectArenaName
      let objectArenaType <- instantiateMVars (← whnfR (← inferType objectArenaExpr))
      unless objectArenaType.getAppFn.constName? ==
          some `D5.S3.ConceptDynamics.InformationEscape.Arena do
        return .error s!"IE-C003 ArenaResolutionFailed: {entry.objectArenaName}"
      unless ← isDefEq expectedArena objectArenaExpr do
        return .error (statementMismatchError entry.theoremName)
      pure objectArenaExpr
    unless ← isDefEq unitArgs.back! objectArenaExpr do
      return .error (statementMismatchError entry.theoremName)
    let statementExpr <- mkAppM
      `D5.S3.ConceptDynamics.InformationEscape.TheoremUnit.Statement
      #[unitExpr]
    let statementType <- instantiateMVars (← whnfR statementExpr)
    let proofExpr <- mkAppM
      `D5.S3.ConceptDynamics.InformationEscape.TheoremUnit.proof
      #[unitExpr]
    let proofType <- instantiateMVars (← whnfR (← inferType proofExpr))
    unless ← isDefEq statementType theoremType do
      return .error (statementMismatchError entry.theoremName)
    unless ← isDefEq proofType statementType do
      return .error (statementMismatchError entry.theoremName)
    let realizationExpr <- mkConstWithFreshMVarLevels entry.realizationName
    let realizationType <- instantiateMVars (← whnfR (← inferType realizationExpr))
    let realizationHead := realizationType.getAppFn.constName?
    if realizationHead == some primitiveRealizationName then
      let expectedLaw <- mkAppM
        `D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.Law
        #[arenaExpr, realizationExpr]
      unless ← isDefEq theoremType expectedLaw do
        return .error (statementMismatchError entry.theoremName)
      let primitivesExpr <- mkAppM
        `D5.S3.ConceptDynamics.InformationEscape.TheoremUnit.primitives
        #[unitExpr]
      let compiledBundle <- compilePrimitiveBundle arenaExpr realizationExpr
      unless ← isDefEq primitivesExpr compiledBundle do
        return .error (statementMismatchError entry.theoremName)
    else if realizationHead == some legacyPrimitiveRealizationName then
      match env.find? entry.realizationName with
      | some (.thmInfo _) =>
        let legacyArgs := realizationType.getAppArgs
        unless legacyArgs.size == 3 do
          return .error (statementMismatchError entry.theoremName)
        unless ← isDefEq legacyArgs[0]! arenaExpr do
          return .error (statementMismatchError entry.theoremName)
        unless ← isDefEq legacyArgs[1]! theoremType do
          return .error (statementMismatchError entry.theoremName)
        let primitivesExpr <- mkAppM
          `D5.S3.ConceptDynamics.InformationEscape.TheoremUnit.primitives
          #[unitExpr]
        let compiledBundle <- compilePrimitiveBundle arenaExpr legacyArgs[2]!
        unless ← isDefEq primitivesExpr compiledBundle do
          return .error (statementMismatchError entry.theoremName)
      | _ => return .error (statementMismatchError entry.theoremName)
    else
      return .error (statementMismatchError entry.theoremName)
    return .ok ()) fun e => do
    if entry.derivedCertificate.isSome && e.isRuntime then
      return .error s!"P1.IncompleteCheck: {← e.toMessageData.toString}"
    return .error (statementMismatchError entry.theoremName)

private def sameCertificate : Option AutoDerivedSemanticCertificate →
    Option AutoDerivedSemanticCertificate → Bool
  | none, none => true
  | some a, some b =>
    a.occurrence == b.occurrence && a.catalogKind == b.catalogKind &&
      a.localRegistrationNames == b.localRegistrationNames && a.statementIdentity == b.statementIdentity &&
      a.levelParams == b.levelParams && a.nondegenerate == b.nondegenerate &&
      a.statement.equal b.statement && a.descriptor.equal b.descriptor &&
      a.arena.equal b.arena && a.outputEvidence.equal b.outputEvidence
  | _, _ => false

private def sameEntry (left right : InformationRegistryEntry) : Bool :=
  RegistrationReifier.occurrenceBinding left == RegistrationReifier.occurrenceBinding right &&
    left.catalogKind == right.catalogKind && left.statementIdentity == right.statementIdentity &&
    left.localRegistrationNames == right.localRegistrationNames &&
    sameCertificate left.derivedCertificate right.derivedCertificate

/-- Validate a prospective entry before insertion; neither registry key may exist yet. -/
def validateNewEntry (env : Environment) (entry : InformationRegistryEntry) :
    MetaM (Except String Unit) := do
  match ← validateEntryCore env entry with
  | .error message => return .error message
  | .ok () => pure ()
  let entries := InformationRegistry.entries env
  let occurrenceMatches := entries.filter fun candidate =>
    candidate.canonicalObjectArenaName == entry.canonicalObjectArenaName &&
      candidate.theoremName == entry.theoremName
  if !occurrenceMatches.isEmpty then
    return .error (duplicateRegistrationError entry (occurrenceMatches.push entry))
  let unitMatches := entries.filter fun candidate =>
    candidate.unitName == entry.unitName
  if !unitMatches.isEmpty then
    return .error <| qualifiedNameCollisionError env.header.mainModule
      entry.effectiveCatalogId entry.unitName (unitMatches.push entry)
  let realizationMatches := entries.filter fun candidate =>
    candidate.realizationName == entry.realizationName
  if !realizationMatches.isEmpty then
    return .error <| qualifiedNameCollisionError env.header.mainModule
      entry.effectiveCatalogId entry.realizationName (realizationMatches.push entry)
  return .ok ()

/-- Validate an entry already stored in the persistent registry exactly once. -/
def validatePersistedEntry (env : Environment) (entry : InformationRegistryEntry) :
    MetaM (Except String Unit) := do
  let entries := InformationRegistry.entries env
  let occurrenceMatches := entries.filter fun candidate =>
    candidate.canonicalObjectArenaName == entry.canonicalObjectArenaName &&
      candidate.theoremName == entry.theoremName
  let [stored] := occurrenceMatches.toList
    | return .error (duplicateRegistrationError entry occurrenceMatches)
  unless sameEntry stored entry do
    return .error "P1.CertificateBindingMismatch: supplied entry differs from authoritative raw row"
  -- Only the authoritative row determines whether derived checks are required.
  let entry := stored
  match ← validateEntryCore env entry with
  | .error message => return .error message
  | .ok () => pure ()
  try
    if entry.derivedCertificate.isSome then RegistrationReifier.closedTruthExcluded entry
  catch e => return .error (← e.toMessageData.toString)
  let unitMatches := entries.filter fun candidate => candidate.unitName == entry.unitName
  match unitMatches.toList with
  | [candidate] =>
    unless sameEntry candidate entry do
      return .error <| qualifiedNameCollisionError env.header.mainModule
        entry.effectiveCatalogId entry.unitName #[candidate, entry]
  | _ => return .error (qualifiedNameCollisionError env.header.mainModule
      entry.effectiveCatalogId entry.unitName unitMatches)
  let realizationMatches := entries.filter fun candidate =>
    candidate.realizationName == entry.realizationName
  match realizationMatches.toList with
  | [candidate] =>
    unless sameEntry candidate entry do
      return .error <| qualifiedNameCollisionError env.header.mainModule
        entry.effectiveCatalogId entry.realizationName #[candidate, entry]
  | _ => return .error (qualifiedNameCollisionError env.header.mainModule
      entry.effectiveCatalogId entry.realizationName realizationMatches)
  return .ok ()

def registerValidatedEntry (entry : InformationRegistryEntry) :
    Lean.Elab.Command.CommandElabM Unit := do
  let env ← getEnv
  let entry ← if entry.resolvedArenaName.isAnonymous then
      Lean.Elab.Command.liftTermElabM <| prepareRegistrationEntry env entry
    else pure entry
  let entry := { entry with statementIdentity := if entry.statementIdentity.isEmpty then
    theoremStatementIdentity env entry.theoremName else entry.statementIdentity }
  let result <- Lean.Elab.Command.liftTermElabM <|
    validateNewEntry (← getEnv) entry
  match result with
  | .ok () =>
    Lean.Elab.Command.liftTermElabM do
      let diagnostic ← RegistrationGates.validateFinite entry
      if entry.derivedCertificate.isSome && diagnostic.isSome then
        RegistrationReifier.checkDiagnostic diagnostic.get!
      RegistrationGates.publishDiagnostic entry.unitName diagnostic
    modifyEnv fun env => informationRegistryExt.addEntry env entry
  | .error message => throwError message

end LeanInformationAudit
