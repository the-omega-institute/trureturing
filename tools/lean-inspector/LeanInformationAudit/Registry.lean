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
  -- A reflexive source supplies no comparison between distinct object readouts.
  -- Preserve this P1 exclusion at both insertion and persisted consumption;
  -- exact uses alpha-only structural comparison, never function extensionality.
  if ← exact descriptor.getAppArgs[5]! descriptor.getAppArgs[6]! then
    throwError "P1.SemanticRejected: IE-C050 ClosedTruthReadout \
      key={theoremName} reason=unclassified_form rule=p1.reflexive_source"
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

/-- Consume the completed registration-time semantic diagnostic, bound to the
same immutable module as the unit. Publication does not repeat argument audits. -/
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

def sameEntry (left right : InformationRegistryEntry) : Bool :=
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


end LeanInformationAudit

namespace LeanInformationAudit.TemplateAudit
open Lean Meta

register_option informationTemplate.work : Nat := {
  defValue := 524288
  descr := "Lower-only DTR expression, substitution and byte-work quota" }

private structure WireState where
  bytes : ByteArray := {}
  remaining : Nat := 524288
  tokens : Option (Std.HashMap String Nat) := none

private abbrev WireM := StateT WireState (Except String)

private def wireCharge (amount : Nat) : WireM Unit := do
  unless amount ≤ (← get).remaining do throw "incomplete_closure:E8.serialization"
  modify fun s => { s with remaining := s.remaining - amount }

private def emitLiteral (text : String) : WireM Unit := do
  let bytes := text.toUTF8
  let lengthPrefix := (toString bytes.size ++ ":").toUTF8
  let size := lengthPrefix.size + bytes.size
  wireCharge size
  modify fun s => { s with bytes := s.bytes ++ lengthPrefix ++ bytes }

private def emit (text : String) : WireM Unit := do
  let some tokens := (← get).tokens | emitLiteral text
  -- Interning is plan-only. Charge every token's full input even on a hit;
  -- compression must not conceal logical serialization work.
  wireCharge (text.utf8ByteSize + 1)
  if let some index := tokens[text]? then
    let reference := ("@" ++ toString index ++ ":").toUTF8
    wireCharge reference.size
    modify fun s => { s with bytes := s.bytes ++ reference }
  else
    emitLiteral text
    modify fun s => { s with tokens := some (tokens.insert text tokens.size) }

private def wireName (name : Name) (depth : Nat := 0) : WireM Unit := do
  if depth > 256 then throw "incomplete_closure:E8.name_depth"
  match name with
  | .anonymous => emit "anonymous"
  | .str parent value => emit "str"; wireName parent (depth + 1); emit value
  | .num parent value => emit "num"; wireName parent (depth + 1); emit (toString value)

private def wireLevel (params : List Name) (level : Level) (depth : Nat := 0) : WireM Unit := do
  if depth > 256 then throw "incomplete_closure:E8.level_depth"
  match level with
  | .zero => emit "zero"
  | .succ value => emit "succ"; wireLevel params value (depth + 1)
  | .max a b => emit "max"; wireLevel params a (depth + 1); wireLevel params b (depth + 1)
  | .imax a b => emit "imax"; wireLevel params a (depth + 1); wireLevel params b (depth + 1)
  | .param name =>
    if params.contains name then emit "parameter"; emit (toString (params.idxOf name))
    else emit "rigid"; wireName name
  | .mvar _ => throw "incomplete_closure:E7.level_metavariable"

private def wireSubstring (s : Substring.Raw) : WireM Unit := do
  emit s.str; emit (toString s.startPos.byteIdx); emit (toString s.stopPos.byteIdx)

private def wireSource : SourceInfo → WireM Unit
  | .none => emit "none"
  | .synthetic p q canonical => do
    emit "synthetic"; emit (toString p.byteIdx); emit (toString q.byteIdx); emit (toString canonical)
  | .original leading p trailing q => do
    emit "original"; wireSubstring leading; emit (toString p.byteIdx)
    wireSubstring trailing; emit (toString q.byteIdx)

private partial def wireSyntax (depth : Nat) (stx : Syntax) : WireM Unit := do
  if depth > 256 then throw "incomplete_closure:E8.syntax_depth"
  match stx with
  | .missing => emit "missing"
  | .atom info value => emit "atom"; wireSource info; emit value
  | .node info kind children =>
    emit "node"; wireSource info; wireName kind; emit (toString children.size)
    for child in children do wireSyntax (depth + 1) child
  | .ident info raw name pre =>
    emit "ident"; wireSource info; wireSubstring raw; wireName name; emit (toString pre.length)
    for item in pre do
      match item with
      | .namespace name => emit "namespace"; wireName name
      | .decl name fields =>
        emit "decl"; wireName name; emit (toString fields.length)
        for field in fields do emit field

private def wireData (depth : Nat) : DataValue → WireM Unit
  | .ofString value => do emit "string"; emit value
  | .ofBool value => do emit "bool"; emit (toString value)
  | .ofName value => do emit "name"; wireName value
  | .ofNat value => do emit "nat"; emit (toString value)
  | .ofInt value => do emit "int"; emit (toString value)
  | .ofSyntax value => do emit "syntax"; wireSyntax depth value

private partial def wireExpr (params : List Name) (depth : Nat) (e : Expr) : WireM Unit := do
  if depth > 256 then throw "incomplete_closure:E8.expression_depth"
  let child := fun x => wireExpr params (depth + 1) x
  match e with
  | .bvar index => emit "bvar"; emit (toString index)
  | .fvar _ | .mvar _ => throw "incomplete_closure:E7.open_expression"
  | .sort level => emit "sort"; wireLevel params level
  | .const name levels =>
    emit "const"; wireName name; emit (toString levels.length)
    for level in levels do wireLevel params level
  | .app f a => emit "app"; child f; child a
  | .lam _ type body bi => emit "lambda"; emit (reprStr bi); child type; child body
  | .forallE _ type body bi => emit "forall"; emit (reprStr bi); child type; child body
  | .letE _ type value body nd =>
    emit "let"; emit (toString nd); child type; child value; child body
  | .lit (.natVal n) => emit "natLiteral"; emit (toString n)
  | .lit (.strVal s) => emit "stringLiteral"; emit s
  | .mdata data body =>
    emit "metadata"; emit (toString data.entries.length)
    for (key, value) in data.entries do wireName key; wireData (depth + 1) value
    child body
  | .proj name index body => emit "projection"; wireName name; emit (toString index); child body

/-- Domain-separated, length-prefixed raw Expr/Level identity. Binder names are
anonymous; instances, lets and metadata retain their complete structural bytes. -/
def rawIdentity (params : List Name) (e : Expr) (fuel : Nat := 524288) : Except String (String × Nat) := do
  let action : WireM Unit := do emit "DTR-raw-expr-v1"; wireExpr params 0 e
  let (_, state) ← action.run { remaining := min fuel 524288 }
  return (Sha256.hex state.bytes, state.bytes.size)

/-- Complete binding evidence uses the unshared raw-identity wire format.
Dependency arrays are separate length-delimited inputs, not annotations
outside the evidence identity. The evidence reference itself is not encoded. -/
def bindingIdentity (statementIdentity : String) (certificate : TemplateBindingCertificate)
    (fuel : Nat) : Except String (String × Nat) := do
  let action : WireM Unit := do
    emit "DTR-binding-evidence-v1"
    for name in #[certificate.key.root, certificate.key.registrationModule,
        certificate.key.theoremName, certificate.key.objectArena, certificate.key.catalog] do
      wireName name
    emit statementIdentity
    emit certificate.planIdentity
    emit certificate.descriptorIdentity
    emit certificate.actualIdentity
    for inputs in #[certificate.argumentInputs, certificate.extractionInputs] do
      emit (toString inputs.size)
      for input in inputs do
        wireName input.name; wireName input.owner
        emit input.typeIdentity; emit input.bodyIdentity
  let (_, state) ← action.run { remaining := min fuel 524288 }
  return (Sha256.hex state.bytes, state.bytes.size)

private partial def wirePlan (params : List Name) (depth : Nat) (plan : PlanNode) : WireM Unit := do
  if depth > 256 then throw "incomplete_closure:E8.plan_depth"
  let child := wirePlan params (depth + 1)
  let raw := wireExpr params (depth + 1)
  match plan with
  | .atom e => emit "body"; raw e
  | .supplied _ => throw "incomplete_closure:E7.supplied_in_static_plan"
  | .expanded e body => emit "expanded"; raw e; child body
  | .proofLeaf type e => emit "proof-leaf"; raw type; raw e
  | .typeNode checked => emit "type-node"; child checked
  | .audit input body => emit "audit-input"; child input; child body
  | .app f a => emit "application"; child f; child a
  | .lam t b bi => emit "lambda"; emit (reprStr bi); child t; child b
  | .forallE t b bi => emit "forall"; emit (reprStr bi); child t; child b
  | .letE t v b nd => emit "let"; emit (toString nd); child t; child v; child b
  | .mdata m b => emit "metadata"; raw (.mdata m (.bvar 0)); child b
  | .proj n i b => emit "projection"; wireName n; emit (toString i); child b

/-- The canonical wire includes every retained plan node and raw proof/expansion,
all slots, identities, policy and source references. The hash and byte count are
outputs of this encoding and are not recursively encoded inside themselves. -/
def planEncodingWithWork (plan : TemplatePlanData) (fuel : Nat := 524288) :
    Except String (ByteArray × Nat) := do
  let action : WireM Unit := do
    emit "DTR-checked-plan-v2"
    for version in #[plan.schemaVersion, plan.grammarVersion, plan.constructorRecursionVersion,
        plan.compatibilityVersion] do emit (toString version)
    emit plan.compiler; emit plan.toolchain; emit plan.policyIdentity
    wireName plan.name; wireName plan.definitionOwner; wireName plan.enrollmentOwner
    emit (toString plan.levelParams.length)
    emit plan.typeIdentity; emit plan.bodyIdentity
    emit (toString plan.slots.size)
    for slot in plan.slots do
      emit (reprStr slot.kind); emit (reprStr slot.binderInfo)
      wireExpr plan.levelParams 0 slot.type
    emit (toString plan.dependencies.size)
    for dep in plan.dependencies do
      wireName dep.name; wireName dep.owner; emit dep.typeIdentity; emit dep.bodyIdentity
    emit (toString plan.sourceInputs.size)
    for input in plan.sourceInputs do emit input.path; emit input.sha256
    emit (toString plan.rules.size)
    for rule in plan.rules do emit rule
    -- The fixed-width work field is outside the token table so its changing
    -- digits cannot affect references, serialized size or either pass's work.
    emitLiteral (String.ofList (List.replicate (6 - (toString plan.chargedWork).length) '0') ++ toString plan.chargedWork)
    wirePlan plan.levelParams 0 plan.typePlan
    wirePlan plan.levelParams 0 plan.plan
  let limit := min fuel 524288
  let (_, state) ← action.run { remaining := limit, tokens := some {} }
  if state.bytes.size > 65536 then throw s!"incomplete_closure:E8.plan_bytes:{state.bytes.size}"
  return (state.bytes, limit - state.remaining)

def planEncoding (plan : TemplatePlanData) (fuel : Nat := 524288) : Except String ByteArray :=
  (planEncodingWithWork plan fuel).map Prod.fst

def sourcePath (name : Name) : String :=
  (if name.toString.startsWith "LeanInformationAudit." then "tools/lean-inspector/" else "") ++
    name.toString.replace "." "/" ++ ".lean"

def policyPaths : Array String := #[
  "Meta/lean-report.toml", "lean-toolchain", "lake-manifest.json",
  "tools/lean-inspector/LeanInformationAudit/RegistryTypes.lean",
  "tools/lean-inspector/LeanInformationAudit/Registry.lean",
  "tools/lean-inspector/LeanInformationAudit/ReadoutProvenance.lean",
  "tools/lean-inspector/LeanInformationAudit/Syntax.lean"]

def readSourceInput (path : String) : CoreM SourceInput := do
  let bytes ← IO.FS.readBinFile path
  return { path, sha256 := Sha256.hex bytes }

namespace NativeCoherence

private structure Snapshot where
  inputs : Array SourceInput
  data : ModuleData


private def repositoryModule (name : Name) : Bool :=
  name.toString.startsWith "D5." || name.toString.startsWith "LeanInformationAudit." ||
    name == `Trureturing

private def parseHash (text : String) : Except String UInt64 := do
  unless text.utf8ByteSize == 16 do throw "incomplete_closure:E7.native_trace_hash"
  text.toUTF8.foldlM (init := 0) fun result byte => do
    let digit ← if 48 ≤ byte && byte ≤ 57 then pure (byte - 48) else
      if 97 ≤ byte && byte ≤ 102 then pure (byte - 87)
      else throw "incomplete_closure:E7.native_trace_hash"
    return result * 16 + digit.toUInt64

private def binaryHash (bytes : ByteArray) : UInt64 := mixHash 1723 (hash bytes)
private def textHash (text : String) : UInt64 := mixHash 1723 (hash text.crlfToLf)

private def field (json : Json) (key : String) : CoreM Json :=
  ofExcept <| json.getObjVal? key

private partial def traceHash (value : Json) (depth : Nat := 0) : Except String UInt64 := do
  if depth > 256 then throw "incomplete_closure:E7.native_trace_depth"
  if let .str text := value then return ← parseHash text
  let inputs ← value.getArr?
  inputs.foldlM (init := 1723) fun result input => do
    let pair ← input.getArr?
    unless pair.size == 2 do throw "incomplete_closure:E7.native_trace_pair"
    return mixHash result (← traceHash pair[1]! (depth + 1))

private def child (value : Json) (caption : String) : CoreM Json := do
  let inputs ← ofExcept <| value.getArr?
  let matching := inputs.filter fun input =>
    (((input.getArr?).toOption.bind (·[0]?)).bind (·.getStr?.toOption)) == some caption
  unless matching.size == 1 do throwError "incomplete_closure:E7.native_trace_input:{caption}"
  let pair ← ofExcept <| matching[0]!.getArr?
  unless pair.size == 2 do throwError "incomplete_closure:E7.native_trace_pair"
  return pair[1]!

private structure ExportHash where
  arts : UInt64
  metaArts : UInt64
  allArts : UInt64
  publicTransitive : UInt64
  metaTransitive : UInt64
  allTransitive : UInt64
  transitive : UInt64

private initialize regionIndex : EnvExtension
    (Option (Array CompactedRegion × Std.HashMap String (Option CompactedRegion))) ←
  registerEnvExtension (pure none)

private def loadedRegion (env : Environment) (path : System.FilePath) : CoreM CompactedRegion := do
  let cached := regionIndex.getState (← getEnv)
  let index ← match cached with
    | some (regions, index) =>
      unless (unsafe ptrEq regions env.header.regions) do
        throwError "incomplete_closure:E7.native_regions"
      pure index
    | none =>
      let mut index : Std.HashMap String (Option CompactedRegion) := {}
      for region in env.header.regions do
        let key := region.filePath.toString
        index := index.insert key (if index.contains key then none else some region)
      modifyEnv fun current => regionIndex.setState current (some (env.header.regions, index))
      pure index
  let some (some region) := index[path.toString]?
    | throwError "incomplete_closure:E7.native_mapping:{path}"
  return region

private def moduleFile (env : Environment) (name : Name) : CoreM System.FilePath := do
  let path ← findOLean name
  if repositoryModule name then discard <| loadedRegion env path
  return path

private structure Cache where
  snapshots : Std.HashMap Name Snapshot := {}
  closures : Std.HashMap Name (Array Name) := {}
  exports : Std.HashMap Name ExportHash := {}
  deriving Inhabited

private initialize checked : EnvExtension Cache ← registerEnvExtension (pure {})

private initialize observedInputs : EnvExtension (Array String) ← registerEnvExtension (pure #[])

/-- Read-only observation of the files rechecked by the latest selected validation. -/
def lastInputs (env : Environment) : Array String := observedInputs.getState env

/-- The pinned Lake import modifiers select both transitive and artifact traces. -/
private def importHashes (value : ExportHash) (nonModule : Bool) (imported : Import) :
    String × UInt64 × String × UInt64 :=
  if nonModule then ("legacy", value.transitive, "importAllArts", value.allArts)
  else if imported.importAll then ("all", value.allTransitive, "importAllArts", value.allArts)
  else if imported.isMeta then ("meta", value.metaTransitive, "importArts (meta)", value.metaArts)
  else ("public", value.publicTransitive, "importArts", value.arts)

/-- Reproduce Lake.Module.computeExportInfo's four import hash relations.
Compiler-owned imports have no Lake package trace and are pinned by the Lean
version input. Package traces remain trusted upstream build metadata. -/
private partial def exports (env : Environment) (name : Name)
    (memo : Std.HashMap Name ExportHash) : CoreM (Option ExportHash × Std.HashMap Name ExportHash) := do
  if let some value := memo[name]? then return (some value, memo)
  let artifact ← moduleFile env name
  let tracePath := artifact.withExtension "trace"
  if !(← tracePath.pathExists) then
    let lib ← getLibDir (← getBuildDir)
    unless (← IO.FS.realPath artifact).toString.startsWith ((← IO.FS.realPath lib).toString ++ "/") do
      throwError "incomplete_closure:E7.native_trace_missing:{name}"
    return (none, memo)
  let trace ← ofExcept <| Json.parse (← IO.FS.readFile tracePath)
  unless trace.getObjValAs? String "schemaVersion" == .ok "2025-09-10" do
    throwError "incomplete_closure:E7.native_trace_version:{name}"
  let output ← field trace "outputs"
  let oleans ← ofExcept <| output.getObjValAs? (Array String) "o"
  let isModule ← ofExcept <| output.getObjValAs? Bool "m"
  unless oleans.size == (if isModule then 3 else 1) do
    throwError "incomplete_closure:E7.native_trace_outputs:{name}"
  let mut parts := oleans
  if isModule then
    parts := parts.push (← ofExcept <| output.getObjValAs? String "rs")
    parts := parts.push (← ofExcept <| output.getObjValAs? String "r")
  let mut allArts := 1723
  for part in parts do
    allArts := mixHash allArts (← ofExcept <| parseHash (part.take 16).toString)
  let arts := mixHash 1723 (← ofExcept <| parseHash (oleans[0]!.take 16).toString)
  let mut metaArts := arts
  if isModule then
    for part in parts.extract 3 5 do
      metaArts := mixHash metaArts (← ofExcept <| parseHash (part.take 16).toString)
  let some index := env.getModuleIdx? name | throwError "incomplete_closure:E7.native_module:{name}"
  let data := env.header.moduleData[index.toNat]!
  let mut memo := memo
  let mut transitive := 1723
  let mut publicTransitive := 1723
  let mut metaTransitive := 1723
  let mut allTransitive := 1723
  for imported in data.imports do
    let (dependency, next) ← exports env imported.module memo
    memo := next
    if let some dependency := dependency then
      transitive := mixHash (mixHash transitive dependency.transitive) dependency.allArts
      metaTransitive := mixHash (mixHash metaTransitive dependency.metaTransitive) dependency.metaArts
      let (_, selected, _, selectedArts) := importHashes dependency false imported
      allTransitive := mixHash (mixHash allTransitive selected) selectedArts
      if imported.isExported then
        let selected := if imported.isMeta then dependency.metaTransitive
          else dependency.publicTransitive
        let selectedArts := if imported.isMeta then dependency.metaArts else dependency.arts
        publicTransitive := mixHash (mixHash publicTransitive selected) selectedArts
  let value : ExportHash := {
    arts := arts
    metaArts := metaArts
    allArts := allArts
    publicTransitive := publicTransitive
    metaTransitive := metaTransitive
    allTransitive := allTransitive
    transitive := transitive }
  return (some value, memo.insert name value)

private def fileHashes (paths : Array String) : IO (Array String) := do
  let result ← IO.Process.output { cmd := "python3", args := #["-I", "-c",
    "import hashlib,pathlib,sys; [print(hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()) for p in sys.argv[1:]]"] ++ paths }
  unless result.exitCode == 0 do throw <| IO.userError "incomplete_closure:E7.native_hash"
  let hashes := result.stdout.trimAscii.toString.splitOn "\n" |>.toArray
  unless hashes.size == paths.size && hashes.all (fun hash => hash.length == 64 &&
      hash.toList.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f'))) do
    throw <| IO.userError "incomplete_closure:E7.native_hash"
  return hashes

private def unchanged (inputs : Array SourceInput) : IO Bool := do
  if inputs.isEmpty then return true
  let hashes ← fileHashes (inputs.map (·.path))
  return (inputs.zip hashes).all fun (input, hash) => input.sha256 == hash

private def loadedIdentity (name : Name) (data : ModuleData) (bytes : ByteArray) : IO String :=
  IO.FS.withTempFile fun _ path => do
    saveModuleData path name data
    unless (← IO.FS.readBinFile path) == bytes do
      throw <| IO.userError s!"incomplete_closure:E7.loaded_native:{name}"
    -- Hash the independently serialized loaded image, never re-open the mutable
    -- input path to decide which bytes were actually loaded into this Environment.
    return (← fileHashes #[path.toString])[0]!

/-- Exact runtime layout of the pinned compiler's CompactedRegion. Its private
root is a boxed ModuleData for the engine-loaded olean/IR parts selected below.
This cast never reads a fresh disk image or interprets a content-owned value. -/
private structure RegionLayout where
  filePath : System.FilePath
  size : USize
  isMemoryMapped : Bool
  baseAddr : USize
  bufferOffset : USize
  root : NonScalar

private unsafe def loadedPart (region : CompactedRegion) : ModuleData :=
  unsafeCast (unsafeCast region : RegionLayout).root

/-- Re-serialize the original loaded chains, including their cross-part sharing.
Missing private/server/IR regions remain incomplete; disk-only hashes cannot
substitute for a part that was not loaded into this Environment. -/
private def loadedModuleParts (env : Environment) (name : Name) (artifact : System.FilePath) :
    CoreM (Array SourceInput × Array UInt64) := do
  let mut inputs := #[]
  let mut hashes := #[]
  for (key, paths) in #[(name, #[artifact, artifact.addExtension "server",
      artifact.addExtension "private"]),
      (name ++ `ir, #[artifact.withExtension "ir.sig", artifact.withExtension "ir"])] do
    let mut parts : Array ModuleData := #[]
    for path in paths do
      let region ← loadedRegion env path
      parts := parts.push (unsafe loadedPart region)
    let (partInputs, partHashes) ← IO.FS.withTempDir (m := IO) fun temp => do
      let outputs := parts.mapIdx fun i data => (temp / s!"part{i}", data)
      saveModuleDataParts key outputs
      let identities ← fileHashes (outputs.map (·.1.toString))
      let mut inputs := #[]
      let mut hashes := #[]
      for ((input, output), identity) in (paths.zip (outputs.map (·.1))).zip identities do
        let bytes ← IO.FS.readBinFile input
        unless (← IO.FS.readBinFile output) == bytes do
          throw <| IO.userError s!"incomplete_closure:E7.loaded_native:{name}"
        inputs := inputs.push { path := input.toString, sha256 := identity : SourceInput }
        hashes := hashes.push (binaryHash bytes)
      return (inputs, hashes)
    inputs := inputs ++ partInputs
    hashes := hashes ++ partHashes
  return (inputs, hashes)

private def verifyImported (env : Environment) (name : Name)
    (hashes : Std.HashMap Name ExportHash) : CoreM Snapshot := do
  let some index := env.getModuleIdx? name | throwError "incomplete_closure:E7.native_module:{name}"
  let data := env.header.moduleData[index.toNat]!
  let artifact ← moduleFile env name
  let tracePath := artifact.withExtension "trace"
  let source := sourcePath name
  let sourceBytes ← IO.FS.readBinFile source
  let sourceText ← IO.FS.readFile source
  let traceBytes ← IO.FS.readBinFile tracePath
  let trace ← ofExcept <| Json.parse (← IO.FS.readFile tracePath)
  unless trace.getObjValAs? String "schemaVersion" == .ok "2025-09-10" &&
      trace.getObjValAs? Bool "synthetic" == .ok false do
    throwError "incomplete_closure:E7.native_trace_version:{name}"
  let inputs ← field trace "inputs"
  let compiler ← child inputs s!"Lean {Lean.versionStringCore}, commit {Lean.githash}"
  unless (← ofExcept <| traceHash compiler) == textHash Lean.githash do
    throwError "incomplete_closure:E7.native_compiler:{name}"
  let top ← ofExcept <| inputs.getArr?
  let candidates := top.filter fun input =>
    (((input.getArr?).toOption.bind (·[0]?)).bind (·.getStr?.toOption)).any fun caption =>
      caption == source || caption.endsWith ("/" ++ source)
  unless candidates.size == 1 do throwError "incomplete_closure:E7.native_source_input:{name}"
  let pair ← ofExcept <| candidates[0]!.getArr?
  unless pair.size == 2 && (← ofExcept <| traceHash pair[1]!) == textHash sourceText do
    throwError "incomplete_closure:E7.native_source:{name}"
  unless (← ofExcept <| traceHash inputs) ==
      (← ofExcept <| parseHash (← ofExcept <| trace.getObjValAs? String "depHash")) do
    throwError "incomplete_closure:E7.native_trace_integrity:{name}"
  let imports ← child (← child inputs "deps") "imports"
  -- Compare both the captions and hash values against the actual imported DAG;
  -- implementation must retain the ordered caption/value list, not only a count.
  let mut expectedImports : Array (String × UInt64) := #[]
  for imported in data.imports do
    if let some dependency := hashes[imported.module]? then
      let (caption, transitive, artCaption, arts) := importHashes dependency (!data.isModule) imported
      expectedImports := expectedImports.push
        (s!"{imported.module} transitive imports ({caption})", transitive)
      expectedImports := expectedImports.push (s!"{imported.module}:{artCaption}", arts)
  if expectedImports.isEmpty then
    unless (← ofExcept <| traceHash imports) == 1723 do
      throwError "incomplete_closure:E7.native_dependencies:{name}"
  else
    let rows ← ofExcept <| imports.getArr?
    unless rows.size == expectedImports.size do
      throwError "incomplete_closure:E7.native_dependencies:{name}"
    for (row, (caption, hash)) in rows.zip expectedImports do
      let pair ← ofExcept <| row.getArr?
      unless pair.size == 2 && pair[0]!.getStr? == .ok caption &&
          (← ofExcept <| traceHash pair[1]!) == hash do
        throwError "incomplete_closure:E7.native_dependency:{name}:{caption}"
  let (nativeInputs, nativeHashes) ← if data.isModule then loadedModuleParts env name artifact else do
    let bytes ← IO.FS.readBinFile artifact
    let nativeIdentity ← loadedIdentity name data bytes
    pure (#[{path := artifact.toString, sha256 := nativeIdentity}], #[binaryHash bytes])
  let output ← field trace "outputs"
  let mut parts ← ofExcept <| output.getObjValAs? (Array String) "o"
  unless output.getObjValAs? Bool "m" == .ok data.isModule &&
      parts.size == (if data.isModule then 3 else 1) do
    throwError "incomplete_closure:E7.native_output:{name}"
  if data.isModule then
    parts := parts.push (← ofExcept <| output.getObjValAs? String "rs")
    parts := parts.push (← ofExcept <| output.getObjValAs? String "r")
  for (part, hash) in parts.zip nativeHashes do
    unless (← ofExcept <| parseHash (part.take 16).toString) == hash do
      throwError "incomplete_closure:E7.native_output:{name}"
  let result : Snapshot := { data, inputs := #[
    {path := source, sha256 := Sha256.hex sourceBytes},
    {path := tracePath.toString, sha256 := Sha256.hex traceBytes}] ++ nativeInputs }
  -- Close source/artifact replacement during verification itself.
  unless ← unchanged result.inputs do
    throwError "incomplete_closure:E7.native_input_changed:{name}"
  return result

/-- Subsequent uses compare the immutable snapshot; they never issue a new
snapshot around a changed input in an already-loaded Environment. -/
private partial def collect (env : Environment) (root : Name) (seen : NameSet)
    (names : Array Name) : CoreM (NameSet × Array Name) := do
  if seen.contains root || !repositoryModule root then return (seen, names)
  let seen := seen.insert root
  if root == env.header.mainModule then return (seen, names.push root)
  let imports ← do
    let some index := env.getModuleIdx? root | throwError "incomplete_closure:E7.native_module:{root}"
    pure env.header.moduleData[index.toNat]!.imports
  let mut seen := seen
  let mut names := names
  for imported in imports do
    let (nextSeen, nextNames) ← collect env imported.module seen names
    seen := nextSeen
    names := nextNames
  return (seen, names.push root)

/-- Validate selected source/native input closures. The current module is bound
by its parser input; only explicitly supplied imported owners are traversed.
Cached snapshots cannot be renewed around changed bytes in the same environment. -/
def validate (roots : Array Name) : CoreM Unit := do
  let env ← getEnv
  let mut cache := checked.getState env
  let mut names : NameSet := {}
  for root in roots do
    let closure ← if let some closure := cache.closures[root]? then pure closure else do
      let (_, closure) ← collect env root {} #[]
      pure closure
    cache := { cache with closures := cache.closures.insert root closure }
    for name in closure do names := names.insert name
  let mut retainedInputs : Array SourceInput := #[]
  for name in names do
    if name == env.header.mainModule then
      unless (← IO.FS.readFile (sourcePath name)) == (← getFileMap).source do
        throwError "incomplete_closure:E7.current_source:{name}"
      continue
    if let some snapshot := cache.snapshots[name]? then
      let some index := env.getModuleIdx? name
        | throwError "incomplete_closure:E7.native_module:{name}"
      unless (unsafe ptrEq snapshot.data env.header.moduleData[index.toNat]!) do
        throwError "incomplete_closure:E7.native_environment:{name}"
    else
      let (_, next) ← exports env name cache.exports
      cache := { cache with exports := next }
      let snapshot ← verifyImported env name cache.exports
      cache := { cache with snapshots := cache.snapshots.insert name snapshot }
    let some snapshot := cache.snapshots[name]?
      | throwError "incomplete_closure:E7.native_snapshot:{name}"
    retainedInputs := retainedInputs ++ snapshot.inputs
  unless ← unchanged retainedInputs do
    throwError "incomplete_closure:E7.native_input_changed"
  modifyEnv fun current => observedInputs.setState (checked.setState current cache)
    (retainedInputs.map (·.path))

end NativeCoherence

private def sourceInputs (env : Environment) (dependencies : Array DependencyIdentity) : CoreM (Array SourceInput) := do
  let policyOwners := #[`LeanInformationAudit.RegistryTypes, `LeanInformationAudit.Registry,
    `LeanInformationAudit.ReadoutProvenance, `LeanInformationAudit.Syntax]
    |>.filter (fun name => (env.getModuleIdx? name).isSome)
  NativeCoherence.validate (#[env.header.mainModule] ++ policyOwners ++ dependencies.map (·.owner))
  let mut paths := policyPaths.push (sourcePath env.header.mainModule)
  for dep in dependencies do
    if dep.owner.toString.startsWith "D5." || dep.owner.toString.startsWith "LeanInformationAudit." then
      let path := sourcePath dep.owner
      unless paths.contains path do paths := paths.push path
  (paths.qsort (· < ·)).mapM readSourceInput

private def sourceIdentity (inputs : Array SourceInput) : String :=
  Sha256.hex (Json.arr (inputs.map fun input => Json.arr #[Json.str input.path, Json.str input.sha256])).compress.toUTF8

/-- Compare retained bytes; never refresh a stale plan by wrapping old olean
contents with hashes from the current source tree. -/
def validateSourceInputs (inputs : Array SourceInput) : CoreM Unit := do
  for input in inputs do
    unless (← readSourceInput input.path) == input do
      throwError "incomplete_closure:E7.stale_source:{input.path}"

end LeanInformationAudit.TemplateAudit

namespace LeanInformationAudit.TemplateAudit
open Lean Meta

/-- A byte-radix tree. Each node has at most 256 sorted outgoing byte edges;
lookup visits only the selected key's path, never the collection of templates. -/
inductive TemplateTrie where
  | node (value : Option TemplatePlanData) (edges : Array (UInt8 × TemplateTrie))
  deriving Inhabited

namespace TemplateTrie
private partial def insertAt (tree : TemplateTrie) (key : ByteArray) (offset : Nat)
    (value : TemplatePlanData) : TemplateTrie := Id.run do
  let .node old edges := tree
  if offset == key.size then return .node (some value) edges
  let byte := key[offset]!
  let mut found := false
  let mut next := edges.map fun (b, child) =>
    if b == byte then
      (b, insertAt child key (offset + 1) value)
    else (b, child)
  for (b, _) in edges do if b == byte then found := true
  if !found then
    next := next.push (byte, insertAt (.node none #[]) key (offset + 1) value)
  return .node old (next.qsort fun a b => a.1 < b.1)

/-- The callback observes actual node/edge visits. It cannot change the lookup. -/
private partial def lookupAt [Monad m] (tree : TemplateTrie) (key : ByteArray)
    (offset : Nat) (observe : m Unit) : m (Option TemplatePlanData) := do
  observe
  let .node value edges := tree
  if offset == key.size then return value
  let byte := key[offset]!
  for (b, child) in edges do
    observe
    if b == byte then return ← lookupAt child key (offset + 1) observe
    if b > byte then return none
  return none

end TemplateTrie

/-- The only persistent enrollment entry: byte buffers and a fixed digest.
No decoded expression, plan, universe list or dependency graph is deserialized
by Lean on behalf of this extension. Lean's general olean loading is separate. -/
structure TemplatePlanFrame where
  key : ByteArray
  payload : ByteArray
  identity : String
  deriving Inhabited

def TemplatePlanFrame.retainedBytes (frame : TemplatePlanFrame) : Nat :=
  frame.key.size + frame.payload.size + frame.identity.utf8ByteSize + 16

structure TemplateIndex where
  private trie : TemplateTrie := .node none #[]
  bytes : Nat := 0
  error : Option String := none
  decodeAttempts : Nat := 0
  decodedAllocationBytes : Nat := 0
  private localFrames : Array TemplatePlanFrame := #[]
  deriving Inhabited

private def TemplateIndex.insertChecked (index : TemplateIndex) (plan : TemplatePlanData)
    (retained : Nat) : TemplateIndex := Id.run do
  let key := plan.name.toString.toUTF8
  let duplicate := (TemplateTrie.lookupAt index.trie key 0 (pure () : Id Unit)).isSome
  if duplicate then return { index with error := some "unclassified_form:E7.duplicate_enrollment" }
  return { index with
    trie := TemplateTrie.insertAt index.trie key 0 plan
    bytes := index.bytes + retained }

/-- Both limits are checked before decoding or allocating a single plan node.
After the first failure, the importer stops consuming the remaining stream. -/
def TemplateIndex.addFrame (index : TemplateIndex) (frame : TemplatePlanFrame)
    (env : Environment) (importOwner : Name) : TemplateIndex := Id.run do
  if index.error.isSome then return index
  if frame.key.size == 0 || frame.key.size > 1024 || frame.payload.size == 0 ||
      frame.identity.utf8ByteSize != 64 || frame.retainedBytes > 65536 then
    return { index with error := some "incomplete_closure:E8.import_framing" }
  if index.bytes + frame.retainedBytes > 8388608 then
    return { index with error := some "incomplete_closure:E8.import_bytes" }
  unless Sha256.hex frame.payload == frame.identity do
    return { index with error := some "incomplete_closure:E7.import_identity" }
  let index := { index with decodeAttempts := index.decodeAttempts + 1 }
  let .ok (decoded, allocated) := PlanDecoder.decode frame.payload (32 * frame.payload.size)
    | return { index with error := some "incomplete_closure:E7.import_encoding" }
  let plan := { decoded with planIdentity := frame.identity }
  if plan.name.isAnonymous || plan.definitionOwner.isAnonymous || plan.enrollmentOwner.isAnonymous ||
      plan.name.toString.toUTF8 != frame.key || plan.compiler != Lean.versionString ||
      plan.toolchain != Lean.versionString then
    return { index with error := some "incomplete_closure:E8.import_framing" }
  let actualOwner := (RegistrationReifier.declaringModuleOf env plan.name).getD env.header.mainModule
  unless env.contains plan.name && plan.enrollmentOwner == importOwner &&
      plan.definitionOwner == actualOwner do
    return { index with error := some "incomplete_closure:E7.import_owner" }
  return { (index.insertChecked plan frame.retainedBytes) with
    decodedAllocationBytes := index.decodedAllocationBytes + allocated }

def TemplateIndex.lookup [Monad m] (index : TemplateIndex) (name : Name)
    (observe : m Unit) : m (Except String TemplatePlanData) := do
  if let some error := index.error then return .error error
  let key := name.toString.toUTF8
  if key.size > 1024 then return .error "incomplete_closure:E8.name_bytes"
  match ← TemplateTrie.lookupAt index.trie key 0 observe with
  | some plan => return .ok plan
  | none => return .error "unclassified_form:dtr.unregistered_template"

private structure CheckedTemplatePlan where
  data : TemplatePlanData
  frame : TemplatePlanFrame

private initialize templateIndexExt : PersistentEnvExtension TemplatePlanFrame CheckedTemplatePlan TemplateIndex ←
  registerPersistentEnvExtension {
    -- A new entry layout must not reinterpret an old olean extension payload.
    name := `LeanInformationAudit.TemplateAudit.checkedPlanFramesV2
    mkInitial := pure {}
    addEntryFn := fun index checked =>
      { (index.insertChecked checked.data checked.frame.retainedBytes) with
        localFrames := index.localFrames.push checked.frame }
    addImportedFn := fun modules => do
      let env := (← read).env
      let mut index : TemplateIndex := {}
      for i in [:modules.size] do
        if index.error.isSome then break
        let some owner := env.header.moduleNames[i]? | return { index with error := some "incomplete_closure:E7.import_owner" }
        for frame in modules[i]! do
          if index.error.isSome then break
          index := index.addFrame frame env owner
      return index
    exportEntriesFn := fun index => index.localFrames
  }

/-- Read-only observation of actual query operations in the environment's
imported index. The observer cannot supply a plan or affect admission. -/
def observeSelectedPlan [Monad m] (env : Environment) (name : Name)
    (observe : m Unit) : m (Except String TemplatePlanData) :=
  (templateIndexExt.getState env).lookup name observe

/-- Imported checked summaries are the sole lookup source. -/
def selectedPlan (env : Environment) (name : Name) : Except String TemplatePlanData :=
  observeSelectedPlan env name (pure () : Id Unit)

/-- Serialized bytes retained by the actual imported index, including keys. -/
def importedSummaryBytes (env : Environment) : Nat := (templateIndexExt.getState env).bytes

end LeanInformationAudit.TemplateAudit

namespace LeanInformationAudit.TemplateAudit
open Lean Meta

private structure CompileState where
  remaining : Nat := 524288
  dependencies : Array DependencyIdentity := #[]
  rules : Array String := #[]
  constructorTypes : NameSet := {}
  /-- Only original AST parameters and direct constructor fields carry descent
  authority. An arbitrary local with the same type does not. -/
  astVariables : FVarIdSet := {}

private abbrev CompileM := StateT CompileState MetaM

private def charge (work : Nat := 1) : CompileM Unit := do
  Core.checkMaxHeartbeats "template construction"
  unless work ≤ (← get).remaining do throwError "incomplete_closure:E8.work"
  modify fun s => { s with remaining := s.remaining - work }

/-- Pure construction shares the caller's remaining quota. The transformer
fails before allocation when its quota or structural depth is exhausted. -/
private def construct (action : Nat → Except String (α × Nat)) : CompileM α := do
  let (result, work) ← match action (← get).remaining with
    | .ok value => pure value
    | .error reason => throwError reason
  charge work
  return result

private def instantiate (body argument : Expr) : CompileM Expr :=
  construct (fun fuel => PlanTransform.substituteExpr body argument 0 fuel)

private def abstractPlan (body : PlanNode) (x : Expr) : CompileM PlanNode :=
  construct (fun fuel => PlanTransform.abstractPlan body x.fvarId! fuel)

private partial def sameLevel (a b : Level) : CompileM Bool := do
  charge
  match a, b with
  | .zero, .zero => return true
  | .param a, .param b => return a == b
  | .succ a, .succ b => sameLevel a b
  | .max a b, .max c d | .imax a b, .imax c d =>
    return (← sameLevel a c) && (← sameLevel b d)
  | _, _ => return false

private partial def sameRaw (a b : Expr) : CompileM Bool := do
  charge
  if hash a != hash b then return false
  match a, b with
  | .bvar a, .bvar b => return a == b
  | .fvar a, .fvar b => return a == b
  | .sort a, .sort b => sameLevel a b
  | .const a us, .const b vs =>
    if a != b || us.length != vs.length then return false
    for (u, v) in us.zip vs do unless ← sameLevel u v do return false
    return true
  | .lit a, .lit b => return a == b
  | .app f a, .app g b => return (← sameRaw f g) && (← sameRaw a b)
  | .lam n t b bi, .lam m u c ci | .forallE n t b bi, .forallE m u c ci =>
    return n == m && bi == ci && (← sameRaw t u) && (← sameRaw b c)
  | .letE n t v b nd, .letE m u w c md =>
    return n == m && nd == md && (← sameRaw t u) && (← sameRaw v w) && (← sameRaw b c)
  | .proj n i b, .proj m j c => return n == m && i == j && (← sameRaw b c)
  -- Metadata never receives a deduplication shortcut; it remains retained.
  | _, _ => return false

private partial def samePlan (a b : PlanNode) : CompileM Bool := do
  charge
  match a, b with
  | .atom a, .atom b => sameRaw a b
  | .typeNode a, .typeNode b => samePlan a b
  | .proofLeaf t a, .proofLeaf u b => return (← sameRaw t u) && (← sameRaw a b)
  | .expanded a p, .expanded b q => return (← sameRaw a b) && (← samePlan p q)
  | .app a b, .app c d | .audit a b, .audit c d =>
    return (← samePlan a c) && (← samePlan b d)
  | .lam t b bi, .lam u c ci | .forallE t b bi, .forallE u c ci =>
    return bi == ci && (← samePlan t u) && (← samePlan b c)
  | .letE t v b nd, .letE u w c md =>
    return nd == md && (← samePlan t u) && (← samePlan v w) && (← samePlan b c)
  | .proj n i b, .proj m j c => return n == m && i == j && (← samePlan b c)
  | _, _ => return false

/-- An identical checked subtree already carries the same obligations. Search
only nodes visited without prior substitution, never raw expansion/proof syntax.
Inputs have no loose variables at this compilation boundary; external locals
keep their unique fvar identities. Every search/comparison step is charged. -/
private partial def containsInput (tree input : PlanNode) : CompileM Bool := do
  charge
  if ← samePlan tree input then return true
  let child := fun p => containsInput p input
  let rec arguments : PlanNode → CompileM Bool
    | .app f a => do
      charge
      if ← child a then return true
      arguments f
    | _ => pure false
  match tree with
  | .audit a b | .lam a b _ | .forallE a b _ =>
    return (← child a) || (← child b)
  -- A function or let body can change context before its obligations are read.
  | .app .. => arguments tree
  | .letE t v _ _ => return (← child t) || (← child v)
  | .expanded _ b | .typeNode b | .mdata _ b | .proj _ _ b => child b
  | _ => return false

private def rule (name : String) : CompileM Unit := do
  charge
  unless (← get).rules.contains name do
    modify fun s => { s with rules := s.rules.push name }

private def binder (name : Name) (bi : BinderInfo) (type : Expr)
    (body : Expr → CompileM α) : CompileM α := fun state =>
  withLocalDecl name bi type fun x => (body x).run state

private def ownerOf (env : Environment) (name : Name) : Option Name :=
  if env.contains name then
    some ((RegistrationReifier.declaringModuleOf env name).getD env.header.mainModule)
  else none

private def dependency (info : ConstantInfo) : CompileM Unit := do
  let state ← get
  if state.dependencies.any (·.name == info.name) then return
  if state.dependencies.size ≥ 4096 then throwError "incomplete_closure:E8.definition_constants"
  let some owner := ownerOf (← getEnv) info.name | throwError "incomplete_closure:E7.owner"
  let .ok (typeId, typeBytes) := rawIdentity info.levelParams info.type state.remaining
    | throwError "incomplete_closure:E7.type_identity"
  charge typeBytes
  let (bodyId, bodyBytes) ← if ← isProp info.type then pure ("", 0) else match info.value? with
    | some body =>
      let .ok pair := rawIdentity info.levelParams body (← get).remaining
        | throwError "incomplete_closure:E7.body_identity"
      pure pair
    | none => pure ("", 0)
  charge bodyBytes
  modify fun s => { s with dependencies := s.dependencies.push {
    name := info.name, owner, typeIdentity := typeId, bodyIdentity := bodyId } }

-- These names describe the finite grammar, never individual template families.
private def interfaceTypes : Array Name := #[
  `D5.S3.ConceptDynamics.InformationEscape.Arena,
  `D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature,
  `D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization,
  `D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis,
  `D5.S3.ConceptDynamics.InformationEscape.StructuralArena,
  `LeanInformationAudit.StructuralPrimitiveSignature,
  `LeanInformationAudit.StructuralPrimitiveRealization]

private def dataTypes : Array Name :=
  #[`Unit, `PUnit, `Bool, `Nat, `Fin, `Prod, `Sum, `Option, `Subtype]

private def propTypes : Array Name := #[`Eq, `True, `False, `And, `Or, `Not, `Iff, `Exists, `Nat.lt]
private def dictionaryTypes : Array Name := #[`Fintype, `DecidableEq, `Decidable, `DecidablePred, `DecidableRel]

private def interfaceProjection (env : Environment) (name : Name) : Bool :=
  match env.getProjectionFnInfo? name with
  | some p => interfaceTypes.contains p.ctorName.getPrefix &&
      #["State", "Index", "Output", "AnchorIndex", "indexFintype", "indexDecidableEq",
        "outputDecidableEq", "anchorFintype", "anchorDecidableEq", "axis", "readout", "anchor"].contains
          name.getString!
  | none => false

/-- The checked primitive reference is retained by the judge's own module. It is
not a content callback or an enrollment claim. Every use compares the reflected
Name, universe telescope, raw type/body identities and actual declaring module. -/
private structure PrimitivePin where
  identity : DependencyIdentity
  levelCount : Nat
  deriving Inhabited

private initialize primitivePins : SimplePersistentEnvExtension PrimitivePin (Array PrimitivePin) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun modules => modules.foldl (· ++ ·) #[] }

private def constructiveDictionaryNames : Array Name := #[
  `Unit.fintype, `PUnit.fintype, `Bool.fintype, `Fin.fintype, `instFintypeProd,
  `Sum.instFintype, `Option.instFintype, `Subtype.fintype,
  `instDecidableEqUnit, `instDecidableEqPUnit, `instDecidableEqBool,
  `instDecidableEqFin, `Prod.instDecidableEq, `Sum.instDecidableEq,
  `Option.instDecidableEq, `Subtype.instDecidableEq]

private def checkedDictionary (info : ConstantInfo) : CompileM Bool := do
  unless constructiveDictionaryNames.contains info.name do return false
  let some pin := (primitivePins.getState (← getEnv)).find? (·.identity.name == info.name)
    | throwError "incomplete_closure:E2.dictionary_pin"
  dependency info
  let some current := (← get).dependencies.find? (·.name == info.name)
    | throwError "incomplete_closure:E2.dictionary_identity"
  unless current.owner == pin.identity.owner && current.typeIdentity == pin.identity.typeIdentity &&
      current.bodyIdentity == pin.identity.bodyIdentity && info.levelParams.length == pin.levelCount do
    throwError "unclassified_form:E2.dictionary_identity"
  rule "E2.dictionary"
  return true

private def staticIdentity (e : Expr) : CompileM Unit := do
  let env ← getEnv
  let name := e.getAppFn.constName?.getD .anonymous
  let projected := match e.getAppFn with
    | .proj typeName _ _ => RegistrationGates.isJudgeProjection typeName
    | _ => false
  if projected || (!name.isAnonymous && (InformationRegistry.hasTheorem env name ||
      isCompanionName name || RegistrationGates.isJudgeIdentity env name)) then
    throwError "forbidden_dependency:E6.registered_identity"
  if #[`Classical.choice, `Classical.propDecidable, `of_decide_eq_true, `Lean.Expr,
      `Lean.Name, `String].contains name then
    throwError "forbidden_dependency:E6.closed_identity"

mutual
private partial def compileExpr (e : Expr) (depth : Nat := 0)
    (typePosition : Bool := false) (templateBinders : Nat := 0) : CompileM PlanNode := do
  let checked ← compileNode e depth typePosition templateBinders
  if ← isType e then
    rule "E7.type_obligation"
    return .typeNode checked
  return checked

private partial def compileNode (e : Expr) (depth : Nat)
    (typePosition : Bool) (templateBinders : Nat) : CompileM PlanNode := do
  charge
  if depth > 256 then throwError "incomplete_closure:E8.depth"
  if e.hasMVar then throwError "incomplete_closure:E7.metavariable"
  staticIdentity e
  -- Prop *values* are erased only after their entire proposition is classified.
  -- A proposition expression itself is not a proof value.
  if (← isProof e) then
    let type ← inferType e
    let checkedType ← compileExpr type (depth + 1) true
    if let some name := e.getAppFn.constName? then dependency (← getConstInfo name)
    rule "E5.proof_leaf"
    return .audit checkedType (.proofLeaf type e)
  let child := fun value => compileExpr value (depth + 1) typePosition
  match e with
  | .fvar _ => rule "E3.variable"; return .atom e
  | .bvar _ => throwError "incomplete_closure:E3.loose_binder"
  | .mvar _ => throwError "incomplete_closure:E7.metavariable"
  | .sort _ => rule "E2.sort"; return .atom e
  | .lit (.natVal _) =>
    unless typePosition do throwError "unclassified_form:E3.nonindex_literal"
    rule "E3.index_literal"; return .atom e
  | .lit (.strVal _) => throwError "unclassified_form:E3.string_literal"
  | .lam n t b bi =>
    let tp ← compileExpr t (depth + 1) true
    rule "E3.lambda"
    binder n bi t fun x => do
      if templateBinders > 0 &&
          (← get).constructorTypes.contains (t.getAppFn.constName?.getD .anonymous) then
        modify fun s => { s with astVariables := s.astVariables.insert x.fvarId! }
      let body ← compileExpr (← instantiate b x) (depth + 1) typePosition (templateBinders - 1)
      return .lam tp (← abstractPlan body x) bi
  | .forallE n t b bi =>
    let tp ← compileExpr t (depth + 1) true
    binder n bi t fun x => do
      let bp ← compileExpr (← instantiate b x) (depth + 1) true
      rule "E2.pi"
      return .forallE tp (← abstractPlan bp x) bi
  | .letE n t v b nd =>
    -- A known raw source is forbidden even when its function type has no E2
    -- rule. This check does not enter the value's implementation or erase it.
    charge
    staticIdentity v
    let tp ← compileExpr t (depth + 1) true
    let vp ← compileExpr v (depth + 1) false
    binder n .default t fun x => do
      let bp ← child (← instantiate b x)
      rule "E3.let"
      return .letE tp vp (← abstractPlan bp x) nd
  | .mdata m b => rule "E3.metadata"; return .mdata m (← child b)
  | .proj n i b =>
    unless interfaceTypes.contains n || #[`Prod, `Subtype].contains n do
      throwError "unclassified_form:E3.projection"
    rule "E3.projection"; return .proj n i (← child b)
  | .app .. | .const .. =>
    let head := e.getAppFn
    let args := e.getAppArgs
    if head.isFVar || head.isLambda then
      let mut plan ← child head
      for arg in args do plan := .app plan (← child arg)
      rule "E3.application"
      return plan
    let .const name levels := head | throwError "unclassified_form:E3.application_head"
    let info ← getConstInfo name
    if name == `OfNat.ofNat then
      unless typePosition && args.size == 3 && args[0]!.isConstOf `Nat &&
          args[2]!.isAppOfArity `instOfNatNat 1 && args[2]!.getAppArgs[0]!.equal args[1]! do
        throwError "unclassified_form:E3.index_encoding:OfNat.ofNat"
      dependency info
      dependency (← getConstInfo `instOfNatNat)
      rule "E3.nat_index_encoding"
      return .expanded e (← compileExpr args[1]! (depth + 1) true)
    if info.isUnsafe then throwError "unclassified_form:E1.unsafe_definition"
    let fixedType := dataTypes.contains name || propTypes.contains name ||
      dictionaryTypes.contains name || interfaceTypes.contains name ||
      (← get).constructorTypes.contains name
    let constructorTypes := (← get).constructorTypes
    let fixedCtor := match info with
      | .ctorInfo c => dataTypes.contains c.induct || interfaceTypes.contains c.induct ||
          constructorTypes.contains c.induct
      | _ => false
    let recursiveCase := match info with
      | .recInfo r => constructorTypes.contains (r.all.headD .anonymous)
      | _ => false
    if recursiveCase then
      let .recInfo r := info | throwError "unclassified_form:E4c.recursor"
      unless r.numMotives == 1 && r.numIndices == 0 && r.all.length == 1 &&
          args.size > r.getMajorIdx && args[r.getMajorIdx]!.isFVar &&
          (← get).astVariables.contains args[r.getMajorIdx]!.fvarId! do
        throwError "unclassified_form:E4c.structural_descent"
      rule "E4c.constructor_recursion_v1"
      dependency info
      let mut plan := PlanNode.atom head
      for index in [:args.size] do
        let arg := args[index]!
        if index ≥ r.numParams + r.numMotives && index < r.getMajorIdx then
          let some description := r.rules[index - r.numParams - r.numMotives]?
            | throwError "incomplete_closure:E4c.branch_description"
          -- The kernel minor premise has constructor fields first, followed by
          -- induction hypotheses. Only direct AST fields are strict subterms.
          plan := .app plan (← compileBranch arg description.nfields (depth + 1) typePosition)
        else
          plan := .app plan (← child arg)
      return plan
    let fixedCase := match info with
      | .recInfo r => #[`Unit, `PUnit, `Bool, `Option, `Sum, `Prod, `Subtype].contains
          (r.all.headD .anonymous)
      | _ => false
    let fixedProjection := interfaceProjection (← getEnv) name || #[`Prod.fst, `Prod.snd, `Subtype.val].contains name
    let dictionary ← checkedDictionary info
    if fixedType || fixedCtor || fixedCase || recursiveCase || fixedProjection || dictionary || name == `Fin.elim0 then
      dependency info
      let mut plan := PlanNode.atom head
      for arg in args do plan := .app plan (← compileExpr arg (depth + 1) (typePosition || fixedType || #[`Fin.fintype, `instDecidableEqFin].contains name))
      rule (if fixedCase then "E4.cases" else if fixedType then "E2.type" else "E3.constructor")
      return plan
    if name == ``decide then
      unless args.size == 2 && args[0]!.hasFVar && args[1]!.hasFVar do
        throwError "forbidden_dependency:E6.closed_decision"
      let mut plan := PlanNode.atom head
      for arg in args do plan := .app plan (← child arg)
      rule "E3.symbolic_decide"
      return plan
    match info with
    | .thmInfo _ => throwError "forbidden_dependency:E6.executable_theorem:{name}"
    | .recInfo _ => throwError "unclassified_form:E4.recursion:{name}"
    | .defnInfo defn =>
      -- The fixed E2 proposition constructors were handled above. A closed
      -- proposition name cannot acquire a rule by spelling an admitted formula
      -- in its body, even if that body is available and reducible.
      if (← isProp e) && !e.hasFVar then
        throwError "unclassified_form:E2.closed_proposition"
      -- Nesting independent calls is not a definition dependency cycle. Lean's
      -- declaration metadata identifies source recursion before substitution.
      if (← isRecursiveDefinition name) || defn.all.length > 1 then
        throwError "unclassified_form:E5.recursive_definition"
      dependency info
      -- Check every raw argument before capture-avoiding expansion, including
      -- arguments unused by the definition body.
      let mut inputs ← args.mapM child
      let mut value ← construct (fun fuel => PlanTransform.instantiateExpr defn.value defn.levelParams levels fuel)
      let mut type ← construct (fun fuel => PlanTransform.instantiateExpr defn.type defn.levelParams levels fuel)
      for arg in args do
        let .lam _ bodyDomain body _ := value
          | throwError "unclassified_form:E5.unsaturated_definition:{name}"
        let .forallE _ domain tail _ := type
          | throwError "unclassified_form:E5.unsaturated_definition:{name}"
        inputs := inputs.push (← compileExpr domain (depth + 1) true)
        inputs := inputs.push (← compileExpr bodyDomain (depth + 1) true)
        charge
        type ← instantiate tail arg
        value ← instantiate body arg
      if value.isLambda then throwError "unclassified_form:E5.unsaturated_definition:{name}"
      inputs := inputs.push (← compileExpr type (depth + 1) true)
      let mut plan ← child value
      for input in inputs.reverse do
        unless ← containsInput plan input do plan := .audit input plan
      rule "E5.definition"
      return .expanded e plan
    | .opaqueInfo _ => throwError "unclassified_form:E5.opaque_definition"
    | _ => throwError "unclassified_form:E2.unknown_constant:{name}"

private partial def compileBranch (expression : Expr) (fields depth : Nat)
    (typePosition : Bool) : CompileM PlanNode := do
  if fields == 0 then return ← compileExpr expression depth typePosition
  charge
  if depth > 256 then throwError "incomplete_closure:E8.depth"
  let .lam n type body bi := expression
    | throwError "unclassified_form:E4c.branch_lambda"
  let domain ← compileExpr type (depth + 1) true
  binder n bi type fun x => do
    if (← get).constructorTypes.contains (type.getAppFn.constName?.getD .anonymous) then
      modify fun s => { s with astVariables := s.astVariables.insert x.fvarId! }
    let checked ← compileBranch (← instantiate body x) (fields - 1) (depth + 1) typePosition
    return .lam domain (← abstractPlan checked x) bi
end

end LeanInformationAudit.TemplateAudit

namespace LeanInformationAudit.TemplateAudit
open Lean Meta Elab Command

-- Capture standard dictionary references in the trusted judge module, following
-- P1's reflected-provider pattern. An unavailable pin stays unavailable; import
-- of an arbitrary same-typed instance cannot supply one later.
def initializeGrammarPins : CommandElabM Unit := do
  unless (← getEnv).header.mainModule == `LeanInformationAudit.Syntax do
    throwError "incomplete_closure:E2.pin_producer_owner"
  for name in constructiveDictionaryNames do
    if let some info := (← getEnv).find? name then
      let some owner := ownerOf (← getEnv) name | throwError "DTR primitive owner missing"
      let .ok (typeId, _) := rawIdentity info.levelParams info.type
        | throwError "DTR primitive type exceeds identity bound: {name}"
      let .ok (bodyId, _) := rawIdentity info.levelParams (info.value?.getD info.type)
        | throwError "DTR primitive body exceeds identity bound: {name}"
      modifyEnv fun env => primitivePins.addEntry env {
        identity := { name, owner, typeIdentity := typeId, bodyIdentity := bodyId }
        levelCount := info.levelParams.length }

private partial def checkTelescope (type : Expr) (depth : Nat := 0) : CompileM (Array Slot) := do
  if depth > 64 then throwError "incomplete_closure:E8.slots"
  match type with
  | .forallE n domain body bi =>
    if domain == mkSort .zero then throwError "unclassified_form:E1.proposition_slot"
    if bi == .instImplicit && !domain.isForall &&
        !dictionaryTypes.contains (domain.getAppFn.constName?.getD .anonymous) then
      throwError "unclassified_form:E1.instance_slot"
    let _ ← compileExpr domain 0 true
    -- These exact standard aliases describe indexed dictionaries. Classify
    -- their Pi telescope too; an alias must not bypass the family obligation.
    let shape ← if #[`DecidablePred, `DecidableRel].contains
        (domain.getAppFn.constName?.getD .anonymous) then whnf domain else pure domain
    let kind ← match domain with
      | .sort (.succ _) => pure SlotKind.carrier
      | .sort _ => throwError "unclassified_form:E1.carrier_universe"
      | _ =>
        if (← isProp domain) then pure .proof
        else if shape.isForall then
          forallTelescope shape fun fields result => do
            if result.isAppOf `Decidable then
              -- Typing normalization is confined to the dependency test. The
              -- raw domain was checked above and remains in the retained plan.
              -- In particular, a beta/let wrapper cannot manufacture an index.
              let proposition ← whnf result.getAppArgs[0]!
              unless fields.any (fun x => (proposition.find? (· == x)).isSome) do
                throwError "unclassified_form:E1.unindexed_decision_family"
              pure .dictionary
            else pure (if result == mkSort .zero then .predicate else .function)
        else if dictionaryTypes.contains (domain.getAppFn.constName?.getD .anonymous) then
          if domain.isAppOf `Decidable then
            throwError "unclassified_form:E1.closed_decision_slot"
          pure .dictionary
        else if interfaceTypes.contains (domain.getAppFn.constName?.getD .anonymous) then pure .interface
        else pure .data
    if bi == .instImplicit && kind != .dictionary then
      throwError "unclassified_form:E1.instance_slot"
    binder n bi domain fun x => do
      let tail ← checkTelescope (← instantiate body x) (depth + 1)
      -- Stored domains use de Bruijn indices relative to earlier slots.
      let tail ← tail.mapIdxM fun index slot => do
        let type ← construct (fun fuel => PlanTransform.abstractExpr slot.type x.fvarId! index fuel)
        return { slot with type }
      return #[{ kind, binderInfo := bi, type := domain }] ++ tail
  | _ =>
    let name := type.getAppFn.constName?.getD .anonymous
    unless #[`D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization,
        `LeanInformationAudit.StructuralPrimitiveRealization].contains name do
      throwError "unclassified_form:E1.return_interface"
    discard <| compileExpr type 0 true
    return #[]

/-- Version 1 permits one non-mutual, unindexed inductive with only direct
strictly positive recursive fields. Nested recursion and function-valued
recursive fields have no rule. The kernel recursor supplies structural descent. -/
private def checkConstructorType (name : Name) : CompileM Unit := do
  let .inductInfo ind ← getConstInfo name
    | throwError "unclassified_form:E4c.inductive_description"
  if ind.all.length != 1 || ind.numIndices != 0 || dataTypes.contains name ||
      ind.isUnsafe || ind.ctors.isEmpty then
    throwError "unclassified_form:E4c.inductive_description"
  forallTelescope ind.type fun _ result => do
    if result == mkSort .zero then throwError "unclassified_form:E4c.proof_inductive"
  dependency (.inductInfo ind)
  modify fun s => { s with constructorTypes := s.constructorTypes.insert name }
  for ctor in ind.ctors do
    let .ctorInfo ci ← getConstInfo ctor
      | throwError "incomplete_closure:E4c.constructor_description"
    dependency (.ctorInfo ci)
    let inspect : CompileM Unit := fun state =>
      forallTelescope ci.type fun fields _ => do
        let mut current := state
        for i in [:fields.size] do
          let domain ← inferType fields[i]!
          if i ≥ ind.numParams then
            if domain.isAppOf name then
              unless domain.getAppArgs.size == ind.numParams &&
                  (domain.getAppArgs.zip (fields.extract 0 ind.numParams)).all
                    (fun (a, b) => a.equal b) do
                throwError "unclassified_form:E4c.recursive_parameters"
            else
              if (domain.find? fun e => e.isConstOf name).isSome then
                throwError "unclassified_form:E4c.nested_recursion"
              let (_, next) ← (compileExpr domain 0 true).run current
              current := next
        return ((), current)
    inspect
  rule "E4c.description_v1"

/-- Finite enrollment. The constructor is private and only its checked output
can enter the persistent extension; public query data never grants insertion. -/
private def compileTemplate (name : Name) (constructors : Array Name) : MetaM CheckedTemplatePlan := do
  let env ← getEnv
  let .defnInfo info ← getConstInfo name | throwError "unclassified_form:E1.definition_kind"
  if info.safety != .safe || info.all.length > 1 || (← isRecursiveDefinition name) then
    throwError "unclassified_form:E1.recursive_definition"
  let some owner := ownerOf env name | throwError "incomplete_closure:E7.owner"
  if name.toString.utf8ByteSize > 1024 then throwError "incomplete_closure:E8.name_bytes"
  let limit := min 524288 (informationTemplate.work.get (← getOptions))
  let action : CompileM (Array Slot × PlanNode × PlanNode) := do
    dependency (.defnInfo info)
    for ast in constructors do checkConstructorType ast
    let slots ← checkTelescope info.type
    let typePlan ← compileExpr info.type 0 true
    let plan ← compileExpr info.value 0 false slots.size
    return (slots, typePlan, plan)
  let ((slots, typePlan, plan), state) ← action.run { remaining := limit }
  let .ok (typeIdentity, typeBytes) := rawIdentity info.levelParams info.type state.remaining
    | throwError "incomplete_closure:E7.type_identity"
  let .ok (bodyIdentity, bodyBytes) := rawIdentity info.levelParams info.value (state.remaining - typeBytes)
    | throwError "incomplete_closure:E7.body_identity"
  let inputs ← sourceInputs env state.dependencies
  let policyIdentity := sourceIdentity (inputs.filter fun input => policyPaths.contains input.path)
  let data : TemplatePlanData := {
    compiler := Lean.versionString, toolchain := Lean.versionString,
    policyIdentity, sourceInputs := inputs,
    name, definitionOwner := owner, enrollmentOwner := env.header.mainModule,
    levelParams := info.levelParams, slots,
    typeIdentity, bodyIdentity, planIdentity := "", dependencies := state.dependencies,
    plan, typePlan, rules := state.rules,
    chargedWork := limit - state.remaining + typeBytes + bodyBytes, serializedBytes := 0 }
  let available := state.remaining - typeBytes - bodyBytes
  let (_, firstWork) ← match planEncodingWithWork data available with
    | .ok result => pure result
    | .error reason => throwError reason
  -- Two serialization passes are both charged; the counter is fixed-width.
  let data := { data with chargedWork := data.chargedWork + 2 * firstWork }
  let (bytes, secondWork) ← match planEncodingWithWork data (available - firstWork) with
    | .ok result => pure result
    | .error reason => throwError reason
  unless firstWork == secondWork do throwError "incomplete_closure:E8.serialization"
  let frame : TemplatePlanFrame := { key := name.toString.toUTF8, payload := bytes, identity := Sha256.hex bytes }
  if frame.retainedBytes > 65536 then throwError "incomplete_closure:E8.plan_bytes"
  return { data := { data with planIdentity := frame.identity, serializedBytes := bytes.size }, frame }

def diagnosticFields (message : String) : String :=
  match message.splitOn ":" with
  | reason :: rule :: site =>
    "reason=" ++ reason ++ " rule=" ++ rule ++ " site=" ++
      (Json.str (String.intercalate ":" site)).compress
  | _ => "reason=incomplete_closure rule=E8.exception site=" ++ (Json.str message).compress

/-- Nested Meta boundaries may use their own initial heartbeat count. The
outer boundary still settles all elapsed work, including the final subcall. -/
def withCumulativeBudget (action : MetaM α) : MetaM α :=
  withCurrHeartbeats <| withOptions (fun options =>
    let configured := maxHeartbeats.get options
    options.set `maxHeartbeats (if configured == 0 then 100000 else min 100000 configured)) do
    let limit := Core.getMaxHeartbeats (← getOptions)
    -- withOptions changes options/maxRecDepth, not Core's heartbeat field.
    controlAt CoreM fun runInBase => withReader (fun context : Core.Context =>
      { context with maxHeartbeats :=
          if context.maxHeartbeats == 0 then limit else min limit context.maxHeartbeats }) do
      let result ← runInBase action
      Core.checkMaxHeartbeats "template cumulative budget"
      return result

/-- Unsupported enrollment leaves no summary. All budgets are lower-only. -/
def enroll (name : Name) (constructors : Array Name := #[]) : CommandElabM (Except String Unit) := do
  let saved ← getEnv
  let answer ← liftTermElabM <| tryCatchRuntimeEx
    (withCumulativeBudget do
      let checkedPlan ← compileTemplate name constructors
      let current := templateIndexExt.getState (← getEnv)
      match current.lookup name (pure () : Id Unit) with
      | .ok _ => throwError "unclassified_form:E7.duplicate_enrollment"
      | .error _ => pure ()
      if let some error := current.error then throwError error
      if current.bytes + checkedPlan.frame.retainedBytes > 8388608 then
        throwError "incomplete_closure:E8.import_bytes"
      modifyEnv fun env => templateIndexExt.addEntry env checkedPlan
      pure (.ok ()))
    (fun error => do
      let message ← error.toMessageData.toString
      pure (.error (if message.startsWith "unclassified_form:" ||
          message.startsWith "forbidden_dependency:" || message.startsWith "incomplete_closure:"
        then message else "incomplete_closure:E8.elaboration:" ++ message)))
  if answer matches .error _ then setEnv saved
  return answer

/-- Extraction helper types satisfy the same E2/E6 judgment. This examines a
helper's type, not the selected template body, and returns its actual work debit. -/
def checkExtractionType (type : Expr) (available : Nat) :
    MetaM (Array DependencyIdentity × Nat) := do
  let limit := min 524288 available
  let (_, state) ← (compileExpr type 0 true).run { remaining := limit }
  return (state.dependencies, limit - state.remaining)

end LeanInformationAudit.TemplateAudit

namespace LeanInformationAudit.TemplateBinding
open Lean Meta TemplateAudit

private structure CompareState where
  remaining : Nat
  extractionNames : NameSet := {}

private abbrev CompareM := StateT CompareState MetaM
private def debit (n : Nat := 1) : CompareM Unit := do
  Core.checkMaxHeartbeats "template comparison"
  unless n ≤ (← get).remaining do throwError "incomplete_closure:E8.comparison_work"
  modify fun state => { state with remaining := state.remaining - n }

private def construct (action : Nat → Except String (α × Nat)) : CompareM α := do
  let (result, work) ← match action (← get).remaining with
    | .ok value => pure value
    | .error reason => throwError reason
  debit work
  return result

private def materialize (plan : PlanNode) : CompareM Expr :=
  construct (fun fuel => PlanTransform.toExpr plan fuel)

private partial def alpha (e : Expr) (depth : Nat := 0) : CompareM Expr := do
  debit
  if depth > 256 then throwError "incomplete_closure:E8.comparison_depth"
  let child := fun x => alpha x (depth + 1)
  match e with
  | .app f a => return .app (← child f) (← child a)
  | .lam _ t b bi => return .lam .anonymous (← child t) (← child b) bi
  | .forallE _ t b bi => return .forallE .anonymous (← child t) (← child b) bi
  | .letE _ t v b nd => return .letE .anonymous (← child t) (← child v) (← child b) nd
  | .mdata m b => return .mdata m (← child b)
  | .proj n i b => return .proj n i (← child b)
  | .mvar _ | .fvar _ => throwError "incomplete_closure:dtr.open_comparison"
  | _ => return e

private def equalRaw (a b : Expr) : CompareM Bool := do
  return (← alpha a).equal (← alpha b)

private def rawSubstitute (body argument : Expr) (cutoff : Nat) : CompareM Expr :=
  construct (fun fuel => PlanTransform.substituteExpr body argument cutoff fuel)

private def substitute (body argument : PlanNode) : CompareM PlanNode :=
  construct (fun fuel => PlanTransform.substitutePlan body argument fuel)

private def levels (params : List Name) (values : List Level) (plan : PlanNode) : CompareM PlanNode :=
  construct (fun fuel => PlanTransform.instantiatePlan plan params values fuel)

private partial def applyPlan (plan : PlanNode) (arg : PlanNode) : CompareM PlanNode := do
  debit
  match plan with
  | .expanded _ body | .typeNode body => applyPlan body arg
  | .audit input body => return .audit input (← applyPlan body arg)
  | .lam domain body _ => return .audit (.typeNode domain) (← substitute body arg)
  | _ => throwError "unclassified_form:dtr.unsaturated_plan"

private def isRealizationType (type : Expr) : Bool :=
  #[`D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization,
    `LeanInformationAudit.StructuralPrimitiveRealization].contains (type.getAppFn.constName?.getD .anonymous)

/-- Expose only a saturated forwarding spine. The parameter vector must contain
every lambda variable exactly once, in its original order, as a whole argument.
No beta reduction is performed inside an actual supplied argument. -/
private def forwardActual (theoremName selected : Name) (initial : Expr) : CompareM Expr := do
  let mut actual := initial
  let mut visited : NameSet := {}
  for _ in [:256] do
    debit
    let .const name universeArgs := actual.getAppFn | return actual
    if name == selected then return actual
    let some (.defnInfo info) := (← getEnv).find? name | return actual
    unless isRealizationType info.type.getForallBody do return actual
    if visited.contains name || info.safety != .safe ||
        (← isRecursiveDefinition name) || info.all.length > 1 ||
        ((← getEnv).getProjectionFnInfo? name).isSome ||
        (Compiler.getImplementedBy? (← getEnv) name).isSome ||
        (getExternAttrData? (← getEnv) name).isSome then
      throwError "unclassified_form:dtr.extraction_kind"
    let arguments := actual.getAppArgs
    if actual.hasFVar || actual.hasLooseBVars || actual.hasMVar ||
        universeArgs.length != info.levelParams.length then
      throwError "incomplete_closure:dtr.extraction_open"
    let mut body := info.value
    let mut arity := 0
    while let .lam _ _ tail _ := body do
      debit
      arity := arity + 1
      body := tail
    unless body.getAppFn.isConst && arity == arguments.size do return actual
    let mut forwarded : Array Nat := #[]
    for argument in body.getAppArgs do
      debit
      if argument.hasLooseBVars then
        let .bvar index := argument | return actual
        forwarded := forwarded.push index
    unless forwarded == (List.range arity).reverse.toArray do return actual
    let (dependencies, typeWork) ← checkExtractionType info.type (← get).remaining
    debit typeWork
    let (argumentNames, argumentWork) ← match ←
        RegistrationGates.templateArgumentsCurrent theoremName arguments (← get).remaining with
      | .ok result => pure result
      | .error diagnostic => throwError diagnostic
    debit argumentWork
    let names := dependencies.map (·.name) ++ argumentNames
    modify fun state =>
      let extracted := names.foldl (fun found n => found.insert n)
        (state.extractionNames.insert name)
      { state with extractionNames := extracted }
    let .ok (_, bodyWork) := rawIdentity info.levelParams info.value (← get).remaining
      | throwError "incomplete_closure:E8.extraction_body"
    debit bodyWork
    let mut value ← construct (fun fuel => PlanTransform.instantiateExpr info.value info.levelParams universeArgs fuel)
    for argument in arguments do
      let .lam _ _ tail _ := value | throwError "incomplete_closure:dtr.extraction_telescope"
      value ← rawSubstitute tail argument 0
    visited := visited.insert name
    actual := value
  throwError "incomplete_closure:E8.extraction_depth"

private def planSpine (plan : PlanNode) : PlanNode × Array PlanNode := Id.run do
  let mut head := plan
  let mut arguments := #[]
  while let .app f a := head do
    head := f
    arguments := arguments.push a
  return (head, arguments.reverse)

/-- Only checked template lambda sites have administrative beta reduction.
Arguments and constructor fields keep their original nodes and origins. -/
private partial def checkedHead (plan : PlanNode) (depth : Nat := 0) : CompareM PlanNode := do
  debit
  if depth > 256 then throwError "incomplete_closure:E8.extraction_depth"
  match plan with
  | .expanded _ body | .typeNode body | .audit _ body => checkedHead body (depth + 1)
  | .app f a =>
    let f ← checkedHead f (depth + 1)
    match f with
    | .lam _ body _ => checkedHead (← substitute body a) (depth + 1)
    | _ => return .app f a
  | _ => return plan

mutual
/-- Read already checked type/proof-leaf nodes after slot substitution. Plan
lambda applications expose their instantiated obligations; supplied nodes are
never inspected or normalized by this consumer. -/
private partial def retainedTypes (plan : PlanNode) (context : Array Expr := #[])
    (depth : Nat := 0) : CompareM (Array (Expr × Array Expr)) := do
  debit
  if depth > 256 then throwError "incomplete_closure:E8.type_obligation_depth"
  let child := fun p => retainedTypes p context (depth + 1)
  let obligation := fun type : Expr => (type, if type.hasLooseBVars then context else #[])
  match plan with
  | .atom _ | .supplied _ => return #[]
  | .proofLeaf type _ => return #[obligation type]
  | .typeNode checked => return #[obligation (← materialize checked)] ++ (← child checked)
  | .expanded _ checked => child checked
  | .audit input body => return (← child input) ++ (← child body)
  | .app f a =>
    let (head, pending) ← retainedHead f context (depth + 1)
    if let .lam domain body _ := head then
      return pending ++ #[obligation (← materialize domain)] ++ (← child domain) ++
        (← child a) ++ (← child (← substitute body a))
    return pending ++ (← child head) ++ (← child a)
  | .lam domain body bi | .forallE domain body bi =>
    let type ← materialize domain
    let binder := Expr.forallE .anonymous type (.bvar 0) bi
    return #[obligation type] ++ (← child domain) ++
      (← retainedTypes body (context.push binder) (depth + 1))
  | .letE type value body _ =>
    -- Substitution here discharges dependent type obligations only. The
    -- comparator still retains the original let/value/body without zeta.
    return #[obligation (← materialize type)] ++ (← child type) ++ (← child value) ++
      (← child (← substitute body value))
  | .mdata _ body | .proj _ _ body => child body

/-- Expose a plan-created lambda while retaining obligations from every
intermediate application. Do not inspect an uninstantiated lambda body or
normalize a supplied node to discover a function head. -/
private partial def retainedHead (plan : PlanNode) (context : Array Expr)
    (depth : Nat) : CompareM (PlanNode × Array (Expr × Array Expr)) := do
  debit
  if depth > 256 then throwError "incomplete_closure:E8.type_obligation_depth"
  let child := fun p => retainedHead p context (depth + 1)
  let types := fun p => retainedTypes p context (depth + 1)
  let obligation := fun type : Expr => (type, if type.hasLooseBVars then context else #[])
  match plan with
  | .expanded _ body => child body
  | .audit input body =>
    let pending ← types input
    let (head, rest) ← child body
    return (head, pending ++ rest)
  | .typeNode checked =>
    let (head, rest) ← child checked
    return (head, #[obligation (← materialize checked)] ++ rest)
  | .app f a =>
    let (head, pending) ← child f
    if let .lam domain body _ := head then
      let inputs := #[obligation (← materialize domain)] ++ (← types domain) ++ (← types a)
      let (result, rest) ← child (← substitute body a)
      return (result, pending ++ inputs ++ rest)
    return (.app head a, pending)
  | _ => return (plan, #[])
end

private structure MatchContext where
  theoremName : Name
  selected : Name
  descriptor : Expr
  body : PlanNode

private structure FixedProjection where
  typeName : Name
  index : Nat
  base : Expr
  parameters : Array Expr := #[]
  universeArgs : Option (List Level) := none

private def fixedProjection (actual : Expr) : MetaM (Option FixedProjection) := do
  match actual with
  | .proj typeName index base => return some { typeName, index, base }
  | _ =>
    let .const name universeArgs := actual.getAppFn | return none
    let some projection := (← getEnv).getProjectionFnInfo? name | return none
    let arguments := actual.getAppArgs
    unless arguments.size == projection.numParams + 1 do return none
    return some {
      typeName := projection.ctorName.getPrefix
      index := projection.i
      base := arguments[projection.numParams]!
      parameters := arguments.extract 0 projection.numParams
      universeArgs := some universeArgs }

private def realizationInterfaces : Array Name := #[
  `D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization,
  `LeanInformationAudit.StructuralPrimitiveRealization]

private partial def matchesPlan (context : MatchContext) (plan : PlanNode) (actual : Expr)
    (depth : Nat := 0) : CompareM Bool := do
  debit
  if depth > 256 then throwError "incomplete_closure:E8.match_depth"
  let child := fun p e => matchesPlan context p e (depth + 1)
  -- A supplied argument is an immutable comparison leaf. In particular, an
  -- apparent projection or forwarding application inside it is not reduced.
  if let .typeNode checked := plan then return ← child checked actual
  if let .audit _ checked := plan then return ← child checked actual
  if let .supplied raw := plan then return ← equalRaw raw actual
  if let some projection ← fixedProjection actual then
    if realizationInterfaces.contains projection.typeName then
      let base ← forwardActual context.theoremName context.selected projection.base
      if ← equalRaw base context.descriptor then
        let record ← checkedHead context.body
        let (head, fields) := planSpine record
        if let .atom (.const ctor universeArgs) := head then
          if let some (.ctorInfo info) := (← getEnv).find? ctor then
            if info.induct == projection.typeName && info.numParams + projection.index < fields.size &&
                (projection.parameters.isEmpty || projection.parameters.size == info.numParams) &&
                (projection.universeArgs.isNone || projection.universeArgs == some universeArgs) then
              let mut parametersMatch := true
              for i in [:projection.parameters.size] do
                unless ← child fields[i]! projection.parameters[i]! do parametersMatch := false
              if parametersMatch then
                return ← child plan (← materialize fields[info.numParams + projection.index]!)
      else if let .const ctor universeArgs := base.getAppFn then
        if let some (.ctorInfo info) := (← getEnv).find? ctor then
          let fields := base.getAppArgs
          if info.induct == projection.typeName && fields.size == info.numParams + info.numFields &&
              projection.index < info.numFields &&
              (projection.parameters.isEmpty || projection.parameters.size == info.numParams) &&
              (projection.universeArgs.isNone || projection.universeArgs == some universeArgs) then
            -- Audit the entire literal receiver before selecting a field. An
            -- unused anchor or signature parameter is still an extraction input.
            let (names, work) ← match ← RegistrationGates.templateArgumentsCurrent
                context.theoremName (fields ++ projection.parameters) (← get).remaining with
              | .ok result => pure result
              | .error diagnostic => throwError diagnostic
            debit work
            modify fun state =>
              let extracted := names.foldl (fun found name => found.insert name)
                (state.extractionNames.insert ctor)
              { state with extractionNames := extracted }
            let mut parametersMatch := true
            for i in [:projection.parameters.size] do
              unless ← equalRaw fields[i]! projection.parameters[i]! do parametersMatch := false
            if parametersMatch then return ← child plan fields[info.numParams + projection.index]!
  match plan with
  | .typeNode checked => child checked actual
  | .audit _ checked => child checked actual
  | .expanded raw body =>
    if ← equalRaw raw actual then return true
    child body actual
  | .atom raw | .supplied raw | .proofLeaf _ raw => equalRaw raw actual
  | .app (.lam _ body _) arg => child (← substitute body arg) actual
  | .app f a =>
    match actual with
    | .app g b => return (← child f g) && (← child a b)
    | _ => return false
  | .lam t b bi =>
    match actual with
    | .lam _ u c bj => return bi == bj && (← child t u) && (← child b c)
    | _ => return false
  | .forallE t b bi =>
    match actual with
    | .forallE _ u c bj => return bi == bj && (← child t u) && (← child b c)
    | _ => return false
  | .letE t v b nd =>
    match actual with
    | .letE _ u w c ne => return nd == ne && (← child t u) && (← child v w) && (← child b c)
    | _ => return false
  | .mdata m b =>
    match actual with
    | .mdata n c => return (Expr.mdata m (.bvar 0)).equal (.mdata n (.bvar 0)) && (← child b c)
    | _ => return false
  | .proj n i b =>
    match actual with
    | .proj k j c => return n == k && i == j && (← child b c)
    | _ => return false

private def extract (event : TemplateOccurrenceEvent) : CompareM Expr := do
  debit
  let name := event.realizationName
  let info ← getConstInfo name
  let raw ← if info.type.isAppOfArity
      `D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization 3 then
    pure info.type.getAppArgs[2]!
  else if isRealizationType info.type then
    match info with
    | .defnInfo defn =>
      if defn.safety != .safe || (← isRecursiveDefinition name) || defn.all.length > 1 ||
          (Compiler.getImplementedBy? (← getEnv) name).isSome ||
          (getExternAttrData? (← getEnv) name).isSome then
        throwError "unclassified_form:dtr.extraction_kind"
      pure defn.value
    | _ => throwError "unclassified_form:dtr.extraction_kind"
  else throwError "unclassified_form:dtr.extraction_interface"
  -- The named realization is used at the occurrence's rigid universe telescope.
  -- Renaming its binders is permitted; permutation or arity guessing is not.
  if info.levelParams.isEmpty then return raw
  unless info.levelParams.length == event.levelParams.length do
    throwError "unclassified_form:dtr.extraction_universes"
  construct fun fuel => PlanTransform.instantiateExpr raw info.levelParams
    (event.levelParams.map Level.param) fuel

private def closed (e : Expr) : MetaM Unit := do
  if e.hasMVar || e.hasFVar || e.hasLooseBVars then
    throwError "incomplete_closure:dtr.descriptor_open"

private def inputIdentity (name : Name) : CompareM DependencyIdentity := do
  debit
  let info ← getConstInfo name
  let owner := (RegistrationReifier.declaringModuleOf (← getEnv) name).getD (← getEnv).header.mainModule
  let .ok (typeIdentity, typeWork) := TemplateAudit.rawIdentity info.levelParams info.type (← get).remaining
    | throwError "incomplete_closure:dtr.input_identity"
  debit typeWork
  -- A proof input retains its raw occurrence and full type identity. Its
  -- implementation is outside the provenance/evidence boundary.
  let bodyIdentity ← if ← isProp info.type then pure "" else match info.value? with
    | none => pure ""
    | some value =>
      let .ok (identity, bodyWork) := TemplateAudit.rawIdentity info.levelParams value (← get).remaining
        | throwError "incomplete_closure:dtr.input_identity"
      debit bodyWork
      pure identity
  return { name, owner, typeIdentity, bodyIdentity }

private def dependencyJson (input : TemplateAudit.DependencyIdentity) : Json := Json.mkObj [
  ("name", toJson input.name.toString), ("owner", toJson input.owner.toString),
  ("type_identity", toJson input.typeIdentity), ("body_identity", toJson input.bodyIdentity)]

private def failureSite (reason : String) : String :=
  String.intercalate ":" ((reason.splitOn ":").drop 2)

private def failureRule (reason : String) : String :=
  (reason.splitOn ":")[1]?.getD "E8.exception"

private def diagnosticMessage (key : TemplateOccurrenceKey) (reason : String)
    (provenance : Json) : String :=
  s!"IE-C050 ClosedTruthReadout key={key.root}/{key.catalog}/{key.theoremName} " ++
    TemplateAudit.diagnosticFields reason ++ " readout=" ++ (toJson (failureSite reason)).compress ++
    " provenance=" ++ provenance.compress

/-- No descriptor means no supplied argument or extraction audit inputs. This
diagnostic records the missing declaration and grants no provenance certificate. -/
def missingDeclarationDiagnostic (key : TemplateOccurrenceKey) : String :=
  diagnosticMessage key "unclassified_form:dtr.missing_declaration" <| Json.mkObj [
    ("argument_inputs", Json.arr #[]), ("extraction_inputs", Json.arr #[]),
    ("plan_identity", Json.null), ("rule", toJson "dtr.missing_declaration"),
    ("site", toJson ""), ("template_key", Json.null)]

/-- Failure provenance names the raw supplied input roots and the native
extraction declaration. These identities describe the failing inputs, not an
admitted closure. A missing identity or exhausted diagnostic walk yields null.
The selected template's executable body is never scanned for this diagnostic. -/
private def diagnosticProvenance (event : TemplateOccurrenceEvent)
    (claim : TemplateBindingClaim) (reason : String) : MetaM Json := do
  if reason.startsWith "incomplete_closure:" then return Json.null
  try
    let env ← getEnv
    let descriptor := claim.descriptor
    let name := descriptor.bind fun e => e.getAppFn.constName?
    let plan := name.bind fun name => (selectedPlan env name).toOption
    let action : CompareM Json := do
      let mut names : NameSet := {}
      for argument in descriptor.map Expr.getAppArgs |>.getD #[] do
        for name in argument.getUsedConstants do names := names.insert name
      let arguments ← (names.toArray.qsort Name.quickLt).mapM inputIdentity
      let extraction ← inputIdentity event.realizationName
      return Json.mkObj [
        ("argument_inputs", Json.arr (arguments.map dependencyJson)),
        ("extraction_inputs", Json.arr #[dependencyJson extraction]),
        ("plan_identity", plan.map (toJson ∘ TemplatePlanData.planIdentity) |>.getD Json.null),
        ("rule", toJson (failureRule reason)), ("site", toJson (failureSite reason)),
        ("template_key", name.map (toJson ∘ Name.toString) |>.getD Json.null)]
    let (provenance, _) ← withCumulativeBudget <| action.run {
      remaining := min 524288 (TemplateAudit.informationTemplate.work.get (← getOptions)) }
    return provenance
  catch _ => return Json.null

private def validate (event : TemplateOccurrenceEvent) (descriptor : Expr)
    (bindingOwner : Name) : MetaM TemplateBindingCertificate := do
  closed descriptor
  let .const name universeArgs := descriptor.getAppFn
    | throwError "unclassified_form:dtr.descriptor_head"
  let plan ← match selectedPlan (← getEnv) name with
    | .ok plan => pure plan
    | .error reason => throwError reason
  let env ← getEnv
  validateSourceInputs plan.sourceInputs
  unless env.contains name do throwError "incomplete_closure:dtr.template_owner"
  let owner := (RegistrationReifier.declaringModuleOf env name).getD env.header.mainModule
  unless owner == plan.definitionOwner && universeArgs.length == plan.levelParams.length &&
      descriptor.getAppArgs.size == plan.slots.size do
    throwError "unclassified_form:dtr.descriptor_telescope"
  let arguments := descriptor.getAppArgs
  let budget := min 524288 (TemplateAudit.informationTemplate.work.get (← getOptions))
  let (argumentNames, argumentWork) ← match ← RegistrationGates.templateArgumentsCurrent event.key.theoremName arguments budget with
    | .ok result => pure result
    | .error reason => throwError reason
  let compare : CompareM TemplateBindingCertificate := do
    debit plan.serializedBytes
    let actual ← extract event
    closed actual
    let mut body ← levels plan.levelParams universeArgs plan.plan
    let mut type ← levels plan.levelParams universeArgs plan.typePlan
    let mut obligations : Array (Expr × Array Expr) := #[]
    for argument in arguments do
      body ← applyPlan body (.supplied argument)
      match ← checkedHead type with
      | .forallE domain tail _ =>
        obligations := obligations.push ((← materialize domain), #[])
        obligations := obligations ++ (← retainedTypes domain)
        type ← substitute tail (.supplied argument)
      | _ => throwError "unclassified_form:dtr.descriptor_telescope"
    obligations := obligations.push ((← materialize type), #[])
    obligations := obligations ++ (← retainedTypes type) ++ (← retainedTypes body)
    let typeWork ← match ← RegistrationGates.templateTypesCurrent event.key.theoremName
        obligations (← get).remaining with
      | .ok work => pure work
      | .error diagnostic => throwError diagnostic
    debit typeWork
    let context : MatchContext := {
      theoremName := event.key.theoremName
      selected := name
      descriptor
      body }
    let actualType ← inferType actual
    unless ← matchesPlan context type actualType do throwError "unclassified_form:dtr.signature_mismatch"
    let exposed ← forwardActual event.key.theoremName name actual
    if !(← equalRaw descriptor exposed) && !(← matchesPlan context body exposed) then
      throwError "unclassified_form:dtr.realization_mismatch"
    let .ok (descriptorIdentity, descriptorWork) := TemplateAudit.rawIdentity event.levelParams descriptor (← get).remaining
      | throwError "incomplete_closure:dtr.descriptor_identity"
    debit descriptorWork
    let .ok (actualIdentity, actualWork) := TemplateAudit.rawIdentity event.levelParams actual (← get).remaining
      | throwError "incomplete_closure:dtr.actual_identity"
    debit actualWork
    let argumentInputs ← argumentNames.mapM inputIdentity
    let extractionNames := ((← get).extractionNames.insert event.realizationName).toArray
    let extractionInputs ← extractionNames.mapM inputIdentity
    let certificate : TemplateBindingCertificate := {
      evidenceRef := "", key := event.key, planIdentity := plan.planIdentity,
      descriptorIdentity, actualIdentity, argumentInputs, extractionInputs }
    let .ok (evidenceRef, evidenceWork) := bindingIdentity event.statementIdentity certificate (← get).remaining
      | throwError "incomplete_closure:E8.evidence_identity"
    debit evidenceWork
    return { certificate with evidenceRef }
  let (certificate, _) ← compare.run { remaining := budget - argumentWork }
  NativeCoherence.validate (#[plan.definitionOwner, plan.enrollmentOwner,
    event.key.registrationModule, bindingOwner] ++
    (plan.dependencies ++ certificate.argumentInputs ++ certificate.extractionInputs).map (·.owner))
  return certificate

private initialize assessmentEvents : EnvExtension (Array TemplateOccurrenceKey) ←
  registerEnvExtension (pure #[])

/-- Read-only observations of actual occurrence assessments in this environment. -/
def observedAssessments (env : Environment) : Array TemplateOccurrenceKey :=
  assessmentEvents.getState env

/-- Registration and final joined assessment share this function. Failure of a
new binding check is retained metadata, never a module elaboration failure. -/
private def assessUncached (event : TemplateOccurrenceEvent) (claim : Option TemplateBindingClaim) : MetaM BindingRecord := do
  modifyEnv fun env => assessmentEvents.modifyState env (·.push event.key)
  match claim with
  | none => return { occurrence := event, descriptor := none, bindingOwner := none, result := .undeclared }
  | some claim =>
    let result ← tryCatchRuntimeEx
      (withCumulativeBudget do
        unless claim.key == event.key && claim.arena.equal event.arena do
          throwError "unclassified_form:dtr.claim_occurrence"
        if let some diagnostic := claim.resolutionDiagnostic then throwError diagnostic
        let some descriptor := claim.descriptor
          | throwError "unclassified_form:dtr.missing_template"
        let certificate ← validate event descriptor claim.owner
        pure <| TemplateBindingResult.declaredValidated certificate)
      (fun error => do
        let message ← error.toMessageData.toString
        let reason := if message.startsWith "unclassified_form:" || message.startsWith "forbidden_dependency:"
            || message.startsWith "incomplete_closure:" then message else "incomplete_closure:E8.assessment:" ++ message
        let provenance ← diagnosticProvenance event claim reason
        return .declaredUnresolved (diagnosticMessage event.key reason provenance))
    return { occurrence := event, descriptor := claim.descriptor, bindingOwner := some claim.owner, result }

private abbrev CacheSemantics := Bool × ReducibilityStatus × Option Name × Bool ×
  Option (Name × Nat × Nat × Bool)

private def cacheSemantics (env : Environment) (name : Name) : CacheSemantics :=
  (Lean.isClass env name, getReducibilityStatusCore env name,
    Compiler.getImplementedBy? env name, (getExternAttrData? env name).isSome,
    (env.getProjectionFnInfo? name).map fun p => (p.ctorName, p.numParams, p.i, p.fromClass))

/-- An immutable occurrence result and the exact inputs it consumed. This cache
is local to an Environment and is never serialized as certification authority. -/
private structure CachedAssessment where
  record : BindingRecord
  claim : TemplateBindingClaim
  options : Options
  registry : Array InformationRegistryEntry
  planName : Name
  planIdentity : String
  constants : Array (Name × ConstantInfo × Name × CacheSemantics)
  inputs : Array SourceInput

private initialize assessmentCache : EnvExtension (Std.HashMap TemplateOccurrenceKey CachedAssessment) ←
  registerEnvExtension (pure {})

private def sameCacheObject (a b : α) : Bool := unsafe ptrEq a b

private def sameCacheEvent (a b : TemplateOccurrenceEvent) : Bool :=
  a.key == b.key && a.unitName == b.unitName && a.realizationName == b.realizationName &&
  a.statement.equal b.statement && a.levelParams == b.levelParams &&
  a.statementIdentity == b.statementIdentity && a.arena.equal b.arena &&
  a.registrationSource == b.registrationSource &&
  a.registrationSourceIdentity == b.registrationSourceIdentity

private def sameCacheClaim (a b : TemplateBindingClaim) : Bool :=
  a.key == b.key && a.owner == b.owner && a.arena.equal b.arena &&
  a.resolutionDiagnostic == b.resolutionDiagnostic && (match a.descriptor, b.descriptor with
    | none, none => true
    | some a, some b => a.equal b
    | _, _ => false)

private def cacheCurrent (cached : CachedAssessment) (event : TemplateOccurrenceEvent)
    (claim : TemplateBindingClaim) : MetaM Bool := do
  unless sameCacheEvent cached.record.occurrence event do return false
  unless sameCacheClaim cached.claim claim do return false
  let env ← getEnv
  unless sameCacheObject cached.options (← getOptions) &&
      sameCacheObject cached.registry (InformationRegistry.entries env) do return false
  let .ok plan := selectedPlan env cached.planName | return false
  unless plan.planIdentity == cached.planIdentity do return false
  for (name, info, owner, semantics) in cached.constants do
    let some current := env.find? name | return false
    unless sameCacheObject info current && cacheSemantics env name == semantics &&
        (RegistrationReifier.declaringModuleOf env name).getD env.header.mainModule == owner do
      return false
  try
    validateSourceInputs cached.inputs
    NativeCoherence.validate (#[claim.owner, event.key.registrationModule] ++
      cached.constants.map (fun (_, _, owner, _) => owner))
    return true
  catch _ => return false

private def retainAssessment (record : BindingRecord) (claim : TemplateBindingClaim)
    (certificate : TemplateBindingCertificate) : MetaM Unit := do
  let some descriptor := claim.descriptor | return
  let .const name _ := descriptor.getAppFn | return
  let env ← getEnv
  let .ok plan := selectedPlan env name | return
  let mut names : NameSet := {}
  for dependency in plan.dependencies ++ certificate.argumentInputs ++ certificate.extractionInputs do
    names := names.insert dependency.name
  for name in #[plan.name, record.occurrence.key.theoremName, record.occurrence.unitName,
      record.occurrence.realizationName, record.occurrence.key.objectArena] do
    names := names.insert name
  let mut paths := plan.sourceInputs.map (·.path)
  for path in #[record.occurrence.registrationSource, TemplateAudit.sourcePath claim.owner] do
    unless paths.contains path do paths := paths.push path
  let mut constants := #[]
  for name in names do
    let info ← getConstInfo name
    let owner := (RegistrationReifier.declaringModuleOf env name).getD env.header.mainModule
    constants := constants.push (name, info, owner, cacheSemantics env name)
    if owner.toString.startsWith "D5." || owner.toString.startsWith "LeanInformationAudit." then
      let path := TemplateAudit.sourcePath owner
      unless paths.contains path do paths := paths.push path
  let inputs ← (paths.qsort (· < ·)).mapM fun path => readSourceInput path
  let cached : CachedAssessment := {
    record, claim, constants, inputs, options := ← getOptions,
    registry := InformationRegistry.entries env, planName := name, planIdentity := plan.planIdentity }
  modifyEnv fun env => assessmentCache.modifyState env (·.insert record.occurrence.key cached)

/-- Every caller uses the same assessment. A hit requires exact occurrence,
claim, selected plan, options, native dependencies and current source bytes.
The authoritative caller still validates the complete native join first. -/
def assess (event : TemplateOccurrenceEvent) (claim : Option TemplateBindingClaim) : MetaM BindingRecord := do
  if let some claim := claim then
    if let some cached := (assessmentCache.getState (← getEnv))[event.key]? then
      if ← cacheCurrent cached event claim then return cached.record
  let record ← assessUncached event claim
  if let (some claim, .declaredValidated certificate) := (claim, record.result) then
    try
      retainAssessment record claim certificate
    catch error =>
      let diagnostic := diagnosticMessage event.key
        ("incomplete_closure:dtr.cache_inputs:" ++ (← error.toMessageData.toString)) Json.null
      return { record with result := .declaredUnresolved diagnostic }
  return record

private initialize occurrenceInventory : SimplePersistentEnvExtension TemplateOccurrenceEvent (Array TemplateOccurrenceEvent) ←
  registerSimplePersistentEnvExtension { addEntryFn := Array.push, addImportedFn := fun arrays => arrays.foldl (· ++ ·) #[] }
private initialize bindingRecords : SimplePersistentEnvExtension BindingRecord (Array BindingRecord) ←
  registerSimplePersistentEnvExtension { addEntryFn := Array.push, addImportedFn := fun arrays => arrays.foldl (· ++ ·) #[] }
private initialize bindingClaims : SimplePersistentEnvExtension TemplateBindingClaim (Array TemplateBindingClaim) ←
  registerSimplePersistentEnvExtension { addEntryFn := Array.push, addImportedFn := fun arrays => arrays.foldl (· ++ ·) #[] }

structure ResolvedDeclaration where
  theoremName : Name
  arena : Name
  descriptor : Option Expr
  diagnostic : Option String := none

private initialize pendingDeclaration : EnvExtension (Option ResolvedDeclaration) ←
  registerEnvExtension (pure none)

/-- Scoped syntax input, never enrollment or certification authority. The
registration transaction owns rollback; the inner scope always clears itself. -/
def withDeclaration (declaration : ResolvedDeclaration)
    (action : Elab.Command.CommandElabM Unit) : Elab.Command.CommandElabM Unit := do
  let previous := pendingDeclaration.getState (← getEnv)
  if previous.isSome then throwError "unclassified_form:dtr.nested_declaration"
  modifyEnv (pendingDeclaration.setState · (some declaration))
  try action
  finally modifyEnv (pendingDeclaration.setState · previous)

def inventory (env : Environment) : Array TemplateOccurrenceEvent := occurrenceInventory.getState env
def records (env : Environment) : Array BindingRecord := bindingRecords.getState env

/-- Origin labels come from the native extension container, separately from
the owner asserted in a claim. Local claims have the current module as origin. -/
private def ownedClaims (env : Environment) : Array (Name × TemplateBindingClaim) := Id.run do
  let mut result := #[]
  for index in [:env.header.moduleNames.size] do
    let owner := env.header.moduleNames[index]!
    for claim in bindingClaims.getModuleEntries env index do
      result := result.push (owner, claim)
  for claim in bindingClaims.getEntries env do
    result := result.push (env.header.mainModule, claim)
  return result

private def ownedEvents (env : Environment) : Array (Name × TemplateOccurrenceEvent) := Id.run do
  let mut result := #[]
  for index in [:env.header.moduleNames.size] do
    let owner := env.header.moduleNames[index]!
    for event in occurrenceInventory.getModuleEntries env index do
      result := result.push (owner, event)
  for event in (occurrenceInventory.getEntries env).reverse do
    result := result.push (env.header.mainModule, event)
  return result

/-- Pure join validation grants no insertion or certification capability.
Both publication and authoritative assessment consume this same relation. -/
def joinClaims (events : Array (Name × TemplateOccurrenceEvent))
    (claims : Array (Name × TemplateBindingClaim)) :
    Except String (Array (TemplateOccurrenceEvent × Option TemplateBindingClaim)) := do
  let mut indexed : Std.HashMap TemplateOccurrenceKey TemplateOccurrenceEvent := {}
  for (producer, event) in events do
    unless producer == event.key.registrationModule do throw "incomplete_closure:dtr.event_owner"
    if indexed.contains event.key then throw "incomplete_closure:dtr.duplicate_occurrence"
    indexed := indexed.insert event.key event
  let mut selected : Std.HashMap TemplateOccurrenceKey TemplateBindingClaim := {}
  for (producer, claim) in claims do
    unless producer == claim.owner do throw "incomplete_closure:dtr.claim_owner"
    unless indexed.contains claim.key do throw "unclassified_form:dtr.dangling_claim"
    if selected.contains claim.key then throw "unclassified_form:dtr.duplicate_claim"
    if let some event := indexed[claim.key]? then
      unless claim.arena.equal event.arena do throw "unclassified_form:dtr.claim_occurrence"
    selected := selected.insert claim.key claim
  return events.map fun (_, event) => (event, selected[event.key]?)

/-- Reuse producer-issued results for mathematical publication in this immutable
environment. This join issues no certificate and makes no claim about subsequent
filesystem changes. The authoritative report rechecks source inputs and assesses
the full join through `assessJoined` before admission can consume its evidence. -/
def cachedJoinedRecords (env : Environment) : Except String (Array BindingRecord) := do
  let joined ← joinClaims (ownedEvents env) (ownedClaims env)
  let retained := records env
  for index in [:env.header.moduleNames.size] do
    let owner := env.header.moduleNames[index]!
    for record in bindingRecords.getModuleEntries env index do
      unless record.bindingOwner.getD record.occurrence.key.registrationModule == owner do
        throw "incomplete_closure:dtr.cached_record_owner"
  joined.mapM fun (event, claim) => do
    let owner := claim.map (·.owner)
    let candidates := retained.filter fun record =>
      record.occurrence.key == event.key && record.bindingOwner == owner
    unless candidates.size == 1 do throw "incomplete_closure:dtr.cached_record_missing"
    let record := candidates[0]!
    let occurrence := record.occurrence
    unless occurrence.statementIdentity == event.statementIdentity &&
        occurrence.statement.equal event.statement && occurrence.levelParams == event.levelParams &&
        occurrence.arena.equal event.arena && occurrence.unitName == event.unitName &&
        occurrence.realizationName == event.realizationName &&
        occurrence.registrationSource == event.registrationSource &&
        occurrence.registrationSourceIdentity == event.registrationSourceIdentity do
      throw "incomplete_closure:dtr.cached_record_inputs"
    match claim, record.descriptor with
    | none, none =>
      unless record.result matches .undeclared do
        throw "incomplete_closure:dtr.cached_undeclared"
    | some claim, descriptor =>
      unless claim.arena.equal event.arena && (match claim.descriptor, descriptor with
        | none, none => true
        | some a, some b => a.equal b
        | _, _ => false) do
        throw "incomplete_closure:dtr.cached_descriptor"
      if let .declaredValidated certificate := record.result then
        unless certificate.key == event.key && claim.resolutionDiagnostic.isNone && descriptor.isSome do
          throw "incomplete_closure:dtr.cached_certificate"
      if record.result matches .undeclared then
        throw "incomplete_closure:dtr.cached_declared"
    | _, _ => throw "incomplete_closure:dtr.cached_descriptor"
    return record

def sourcePath := TemplateAudit.sourcePath

def publishRegistration (entry : InformationRegistryEntry) : Elab.Command.CommandElabM Unit := do
  let info ← getConstInfo entry.theoremName
  let statementIdentity := match TemplateAudit.rawIdentity info.levelParams info.type with
    | .ok (identity, _) => identity
    | .error _ => ""
  let path := sourcePath entry.registrationModuleName
  let sourceIdentity ← try pure (Sha256.hex (← IO.FS.readBinFile path)) catch _ => pure ""
  let event : TemplateOccurrenceEvent := {
    key := {
      root := entry.registrationModuleName
      registrationModule := entry.registrationModuleName
      theoremName := entry.theoremName
      objectArena := entry.canonicalObjectArenaName
      catalog := entry.effectiveCatalogId }

    unitName := entry.unitName, realizationName := entry.realizationName,
    statement := info.type, levelParams := info.levelParams, statementIdentity,
    arena := mkConst entry.canonicalObjectArenaName,
    registrationSource := path, registrationSourceIdentity := sourceIdentity }
  let claim ← match pendingDeclaration.getState (← getEnv) with
    | none => pure none
    | some declaration =>
      unless declaration.theoremName == event.key.theoremName && declaration.arena == event.key.objectArena do
        throwError "unclassified_form:dtr.inline_occurrence"
      pure <| some {
        key := event.key, arena := event.arena, descriptor := declaration.descriptor,
        resolutionDiagnostic := declaration.diagnostic, owner := (← getEnv).header.mainModule : TemplateBindingClaim }
  let record ← Elab.Command.liftTermElabM <| assess event claim
  modifyEnv fun current => bindingRecords.addEntry (occurrenceInventory.addEntry current event) record
  if let some claim := claim then modifyEnv (bindingClaims.addEntry · claim)
  if record.result matches .undeclared then logWarning (missingDeclarationDiagnostic event.key)
  if let .declaredUnresolved diagnostic := record.result then logWarning diagnostic

/-- Claims join by their exact occurrence identity before authoritative assessment.
An overlay retains the original registration owner and cannot replace an inline claim. -/
def declareSidecar (theoremName arena : Name) (catalog : Option Name)
    (descriptor : Option Expr) (resolutionDiagnostic : Option String) : Elab.Command.CommandElabM Unit := do
  let env ← getEnv
  let matching := (inventory env).filter fun event => event.key.theoremName == theoremName &&
    event.key.objectArena == arena && (catalog.isNone || catalog == some event.key.catalog)
  unless matching.size == 1 do throwError "unclassified_form:dtr.sidecar_occurrence"
  let event := matching[0]!
  if (bindingClaims.getState env).any (·.key == event.key) then
    throwError "unclassified_form:dtr.duplicate_claim"
  let claim : TemplateBindingClaim := {
    key := event.key, arena := event.arena, descriptor, resolutionDiagnostic,
    owner := env.header.mainModule }
  let record ← Elab.Command.liftTermElabM <| assess event (some claim)
  modifyEnv fun current => bindingRecords.addEntry (bindingClaims.addEntry current claim) record
  if let .declaredUnresolved diagnostic := record.result then logWarning diagnostic

/-- A replayed event cannot acquire current source or statement identities by
being exported from a new root. Check the original owner and retained bytes. -/
private def validateEvent (event : TemplateOccurrenceEvent) : MetaM Unit := do
  let env ← getEnv
  unless event.registrationSource == sourcePath event.key.registrationModule &&
      event.key.root == event.key.registrationModule do
    throwError "incomplete_closure:dtr.event_owner"
  let input ← TemplateAudit.readSourceInput event.registrationSource
  unless input.sha256 == event.registrationSourceIdentity do
    throwError "incomplete_closure:dtr.event_source"
  let info ← getConstInfo event.key.theoremName
  let .ok (identity, _) := TemplateAudit.rawIdentity info.levelParams info.type
    | throwError "incomplete_closure:dtr.event_statement"
  unless identity == event.statementIdentity && info.levelParams == event.levelParams &&
      info.type.equal event.statement do
    throwError "incomplete_closure:dtr.event_statement"
  for name in #[event.unitName, event.realizationName] do
    unless env.contains name &&
        (RegistrationReifier.declaringModuleOf env name).getD env.header.mainModule ==
          event.key.registrationModule do
      throwError "incomplete_closure:dtr.event_unit_owner"

/-- Snapshot for the complete imported join. Original provisional records are
retained only for transport to the C# join; selected contains one final result. -/
structure JoinedRecords where
  selected : Array BindingRecord
  originals : Array BindingRecord

/-- Shared final assessment after the full imported claim set has been joined.
Callers must establish complete governed sidecar inputs before claiming coverage. -/
def assessJoined : MetaM (Array BindingRecord) := do
  let env ← getEnv
  let joined ← match joinClaims (ownedEvents env) (ownedClaims env) with
    | .ok joined => pure joined
    | .error reason => throwError reason
  for (event, _) in joined do validateEvent event
  joined.mapM fun (event, claim) => assess event claim

/-- Export always starts by joining the entire loaded declaration universe. -/
def exportSnapshot : MetaM JoinedRecords := do
  let selected ← assessJoined
  let originals ← (inventory (← getEnv)).mapM fun event => do
    let some original := (records (← getEnv)).find? (·.occurrence.key == event.key)
      | throwError "incomplete_closure:dtr.original_inventory"
    return original
  return { selected, originals }

def keyJson (key : TemplateOccurrenceKey) : Json := Json.mkObj [
  ("root", toJson key.root.toString), ("registration_module", toJson key.registrationModule.toString),
  ("theorem", toJson key.theoremName.toString), ("object_arena", toJson key.objectArena.toString),
  ("catalog", toJson key.catalog.toString)]

private def certificateJson (certificate : TemplateBindingCertificate) : Json := Json.mkObj [
  ("key", keyJson certificate.key), ("evidence_ref", toJson certificate.evidenceRef),
  ("plan_identity", toJson certificate.planIdentity),
  ("descriptor_identity", toJson certificate.descriptorIdentity),
  ("actual_identity", toJson certificate.actualIdentity),
  ("argument_inputs", Json.arr (certificate.argumentInputs.map dependencyJson)),
  ("extraction_inputs", Json.arr (certificate.extractionInputs.map dependencyJson))]

private def isRepositoryModule (name : Name) : Bool :=
  name.toString.startsWith "D5." || name.toString.startsWith "LeanInformationAudit." ||
    name == `Trureturing

/-- Complete source inputs for this module, independent of registry membership.
A missing imported source is incomplete rather than an empty declaration set. -/
def moduleInputs (env : Environment) (root : Name) : CoreM (Array TemplateAudit.SourceInput) := do
  TemplateAudit.NativeCoherence.validate (#[root] ++
    (if root == env.header.mainModule then env.header.imports.map (·.module) else #[]))
  let mut seen : NameSet := {}
  let mut pending := [root]
  let mut paths := TemplateAudit.policyPaths
  while let name :: rest := pending do
    pending := rest
    if seen.contains name then continue
    seen := seen.insert name
    if !isRepositoryModule name then continue
    let path := sourcePath name
    unless paths.contains path do paths := paths.push path
    let imports ← if name == env.header.mainModule then pure env.header.imports else do
      let some index := env.getModuleIdx? name
        | throwError "incomplete_closure:dtr.module_input:{name}"
      pure env.header.moduleData[index.toNat]!.imports
    pending := imports.toList.map (·.module) ++ pending
  (paths.qsort (· < ·)).mapM TemplateAudit.readSourceInput

/-- Content touches follow actual constant dependencies, including complete
arena/realization types, while theorem proof implementations are never entered. -/
private def contentInputs (record : BindingRecord) : MetaM (Array TemplateAudit.SourceInput) := do
  let env ← getEnv
  let mut pending := [record.occurrence.key.theoremName, record.occurrence.unitName,
    record.occurrence.realizationName, record.occurrence.key.objectArena]
  if let some descriptor := record.descriptor then
    pending := descriptor.getUsedConstants.toList ++ pending
  let mut seen : NameSet := {}
  let mut paths := #[record.occurrence.registrationSource]
  if let some owner := record.bindingOwner then paths := paths.push (sourcePath owner)
  let mut remaining := 524288
  while let name :: rest := pending do
    pending := rest
    if seen.contains name then continue
    if remaining == 0 then throwError "incomplete_closure:dtr.content_inputs"
    remaining := remaining - 1
    seen := seen.insert name
    let info ← getConstInfo name
    let owner := (RegistrationReifier.declaringModuleOf env name).getD env.header.mainModule
    if isRepositoryModule owner then
      let path := sourcePath owner
      unless paths.contains path || path.startsWith "tools/" do paths := paths.push path
    pending := info.type.getUsedConstants.toList ++ pending
    if !info.isTheorem then
      if let some value := info.value? then pending := value.getUsedConstants.toList ++ pending
  (paths.toList.eraseDups.toArray.qsort (· < ·)).mapM fun path => TemplateAudit.readSourceInput path

private def inputJson (input : TemplateAudit.SourceInput) : Json := Json.mkObj [
  ("path", toJson input.path), ("sha256", toJson input.sha256)]

/-- Shared record wire for the inspector and census authoritative snapshots. -/
def recordJson (record : BindingRecord) : MetaM Json := do
  let (state, diagnostic, certificate) := match record.result with
    | .undeclared => ("undeclared", toJson (missingDeclarationDiagnostic record.occurrence.key), Json.null)
    | .declaredUnresolved diagnostic => ("declared_unresolved", toJson diagnostic, Json.null)
    | .declaredValidated certificate => ("declared_validated", Json.null, certificateJson certificate)
  return Json.mkObj [
    ("key", keyJson record.occurrence.key),
    ("registration_source_path", toJson record.occurrence.registrationSource),
    ("statement_identity", toJson record.occurrence.statementIdentity),
    ("unit_name", toJson record.occurrence.unitName.toString),
    ("realization_name", toJson record.occurrence.realizationName.toString),
    ("content_inputs", Json.arr ((← contentInputs record).map inputJson)),
    ("binding_source_path", record.bindingOwner.map (toJson ∘ sourcePath) |>.getD Json.null),
    ("state", toJson state), ("diagnostic", diagnostic), ("certificate", certificate)]

/-- Records are partitioned by their actual producing module. An original
undeclared row and a sidecar overlay remain distinguishable until the final join. -/
def moduleJson (snapshot : JoinedRecords) (moduleName : Name)
    (registered : Array TemplateOccurrenceKey) : MetaM Json := do
  let env ← getEnv
  let originals := snapshot.originals.filter (·.occurrence.key.registrationModule == moduleName)
  let overlays := snapshot.selected.filter fun row => row.bindingOwner == some moduleName &&
    row.occurrence.key.registrationModule != moduleName
  let rows ← (originals ++ overlays).mapM fun row => do
    let some selected := snapshot.selected.find? (·.occurrence.key == row.occurrence.key)
      | throwError "incomplete_closure:dtr.final_record"
    recordJson (if selected.bindingOwner == some moduleName then selected else row)
  return Json.mkObj [
    ("schema_version", toJson (1 : Nat)), ("compatibility_version", toJson (4 : Nat)),
    ("inventory", Json.arr ((inventory env).filter
      (·.key.registrationModule == moduleName) |>.map (keyJson ∘ TemplateOccurrenceEvent.key))),
    ("registered", Json.arr (registered.map keyJson)), ("records", Json.arr rows),
    ("inputs", Json.arr ((← moduleInputs env moduleName).map inputJson))]

end LeanInformationAudit.TemplateBinding

namespace LeanInformationAudit
open Lean Meta

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
    TemplateBinding.publishRegistration entry
  | .error message => throwError message

end LeanInformationAudit

namespace LeanInformationAudit
open Lean Meta

/-- Fixed finite producer for environments that have no structural registry.
The standalone inspector requires this owner-bound API whenever Registry occurs
in the actual import closure, including roots with an empty inventory. -/
def finiteInformationTemplateReportDriver : InformationTemplateReportDriver := fun moduleNames => do
  let env ← getEnv
  let snapshot ← TemplateBinding.exportSnapshot
  moduleNames.mapM fun moduleName => do
    let registered := (InformationRegistry.entries env).filter
      (·.registrationModuleName == moduleName) |>.map fun entry => {
        root := moduleName, registrationModule := moduleName, theoremName := entry.theoremName,
        objectArena := entry.canonicalObjectArenaName, «catalog» := entry.effectiveCatalogId :
          TemplateOccurrenceKey }
    TemplateBinding.moduleJson snapshot moduleName registered

end LeanInformationAudit
