import LeanInformationAudit.RegistrationGates
import LeanInformationAudit.ReifierTemplates

namespace LeanInformationAudit.RegistrationReifier
open Lean Meta D5.S3.ConceptDynamics.InformationEscape
open PointwiseRegistrationTemplates

register_option informationReifier.fuel : Nat := {
  defValue := 65536
  descr := "Lower-only expression traversal budget for the P1 reifier" }

/-- Every exception, including heartbeat/recursion exhaustion, fails certification. -/
def bounded (action : MetaM α) : MetaM α := do
  try RegistrationGates.budget action
  catch e =>
    if (← e.toMessageData.toString).startsWith "P1." then throw e
    throwError "P1.IncompleteCheck: {e.toMessageData}"

def closed (e : Expr) : MetaM Unit := do
  if e.hasMVar || e.hasFVar || e.hasLooseBVars then
    throwError "P1.UnresolvedMetavariables: {e}"

private partial def canonical (e : Expr) : StateT Nat (Except String) Expr := do
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

private def normalizeNames (e : Expr) : MetaM Expr := do
  match (canonical e).run (min 65536 (informationReifier.fuel.get (← getOptions))) with
  | .ok (e, _) => return e
  | .error reason => throwError reason

private partial def difference (a b : Expr) (path := "type") : String := Id.run do
  if a.equal b then return ""
  let children := match a, b with
    | .app f x, .app g y => #[(".fn", f, g), (".arg", x, y)]
    | .forallE _ t x bi, .forallE _ u y bj
    | .lam _ t x bi, .lam _ u y bj =>
      if bi == bj then #[(".domain", t, u), (".body", x, y)] else #[]
    | .letE _ t v x nd, .letE _ u w y ne =>
      if nd == ne then #[(".type", t, u), (".value", v, w), (".body", x, y)] else #[]
    | .proj n i x, .proj m j y =>
      if n == m && i == j then #[(".value", x, y)] else #[]
    | .mdata m x, .mdata n y =>
      if (Expr.mdata m (mkBVar 0)).equal (.mdata n (mkBVar 0)) then
        #[(".body", x, y)] else #[]
    | _, _ => #[]
  for (suffix, x, y) in children do
    if !x.equal y then return difference x y (path ++ suffix)
  return path

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

/-- Only descriptor-created application sites beta-substitute a supplied lambda. -/
private def sourceSite (e : Expr) : Expr :=
  match e with
  | .app (.lam _ _ body _) arg => body.instantiate1 arg
  | _ => e

/-- Extract the actual applied bridge triple, never an unspecialized telescope. -/
def semanticSource (descriptor : Expr) : MetaM (Expr × Expr × Expr) := do
  closed descriptor
  unless descriptor.isAppOfArity ``ReifierTemplates.pointwise 7 do
    throwError "P1.UnsupportedDescriptor: expected fully applied ReifierTemplates.pointwise"
  let type ← inferType descriptor
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
    if e.isAppOf ``pointwiseEqArena then return e
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
  let sensitivityValue := mkAppN (mkConst ``ReifierTemplates.sensitivity)
    (params ++ #[nontrivial, ← rigid nd])
  declaration sensitivity (← mkAppM ``FiniteSlotSensitivity #[arena]) sensitivityValue
  let variation := e.unitName.str "__variation"
  let variationValue ← mkAppM ``ReifierTemplates.variation #[arena, mkConst ``Bool.false, ← rigid sensitivity]
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

/-- Restricted closed-truth exclusion: uniform source plus real variation/provenance.
This does not attempt to decide general semantic truth or arbitrary source fidelity. -/
def closedTruthExcluded (entry : InformationRegistryEntry) : MetaM Unit := do
  let some cert := entry.derivedCertificate | throwError "P1.MissingEvidence: uniform source"
  discard <| exactUse entry.theoremName cert.arena cert.descriptor
  if let some diagnostic ← RegistrationGates.validateFinite entry then throwError "P1.SemanticRejected: {diagnostic}"

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
  requireExact "UnitBindingMismatch" value (← unitValue entry)
  for name in #[entry.realizationName, entry.unitName, entry.variationWitness,
      entry.sensitivityWitness, cert.nondegenerate] do
    unless (← getConstInfo name).levelParams.isEmpty do throwError "P1.RigidUniverseMismatch: {name}"
  let ndType ← mkAppM ``Arena.Nondegenerate #[← mkAppM ``PrimitiveLawArena.toArena #[cert.arena]]
  unless ← RegistrationGates.checked cert.nondegenerate ndType do throwError "P1.MissingEvidence: nondegenerate"
  let sensitivity ← getConstInfo entry.sensitivityWitness
  let some value := sensitivity.value? (allowOpaque := true)
    | throwError "P1.WitnessBindingMismatch: missing sensitivity"
  requireExact "WitnessBindingMismatch" value
    (mkAppN (mkConst ``ReifierTemplates.sensitivity)
      (cert.descriptor.getAppArgs.extract 0 5 ++ #[cert.outputEvidence, ← rigid cert.nondegenerate]))
  let variation ← getConstInfo entry.variationWitness
  let some value := variation.value? (allowOpaque := true)
    | throwError "P1.WitnessBindingMismatch: missing variation"
  requireExact "WitnessBindingMismatch" value
    (← mkAppM ``ReifierTemplates.variation #[cert.arena, mkConst ``Bool.false, ← rigid entry.sensitivityWitness])
  closedTruthExcluded entry
  lawSensitive entry cert.arena

end LeanInformationAudit.RegistrationReifier
