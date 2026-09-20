import LeanInformationAudit.RegistryTypes
import LeanInformationAudit.ReadoutProvenance
import D5.S3.ConceptDynamics.RegistrationWitnesses

namespace LeanInformationAudit.RegistrationGates
open Lean Meta
open D5.S3.ConceptDynamics.InformationEscape

initialize registerTraceClass `InformationRegistration.check

/-- Zero proof synthesis and no realization enumeration. Each obligation,
including type construction, has a fresh fixed elaboration budget. -/
def budget (action : MetaM α) : MetaM α :=
  withCurrHeartbeats <| withOptions
    (fun o => (o.set `maxHeartbeats (200000 : Nat)).set `maxRecDepth (1024 : Nat)) action

def attempt (action : MetaM α) : MetaM (Option α) := do
  try budget (some <$> action)
  catch _ => return none

def bounded (action : MetaM Bool) : MetaM Bool := do
  return (← attempt action).getD false

def checked (name : Name) (expected : Expr) : MetaM Bool := do
  if name.isAnonymous then return false
  let info ← getConstInfo name
  if info.isUnsafe then return false
  let axioms ← collectAxioms name
  unless axioms.all (#[`propext, `Classical.choice, `Quot.sound].contains ·) do return false
  let proof ← mkConstWithFreshMVarLevels name
  unless ← isDefEq (← inferType proof) expected do return false
  let proof ← instantiateMVars proof
  if proof.hasMVar then return false
  checkWithKernel proof
  return true

def witnessArenaName : Name :=
  `D5.S3.ConceptDynamics.InformationEscape.CounterexampleRecord.WitnessArena

def witnessBridgeName : Name :=
  `D5.S3.ConceptDynamics.InformationEscape.CounterexampleRecord.WitnessPrimitiveRealization

/-- Keep the author's arena for ownership and bridge identity. Only the derived
law arena and its finite carrier are used for signature and catalog checks. -/
structure NormalizedArena where
  original : Expr
  law : Expr
  finite : Expr
  witness : Bool

def normalizeArena (arena : Expr) : MetaM NormalizedArena := do
  let type ← whnfR (← inferType arena)
  let witness := type.isConstOf witnessArenaName
  let law ← if witness then mkAppM (witnessArenaName.str "toPrimitiveLawArena") #[arena]
    else pure arena
  let finite ← if witness || type.isConstOf ``PrimitiveLawArena then
      mkAppM ``PrimitiveLawArena.toArena #[law]
    else if type.isConstOf ``Arena then pure arena
    else throwError "IE-C003 ArenaResolutionFailed: {arena}"
  return { original := arena, law, finite, witness }

private def closedExpression (e : Expr) : Bool :=
  !e.hasFVar && !e.hasMVar && !e.hasLooseBVars

/-- Inspect the bridge's named claim, not its proof. The theorem may spell the
same universal literally; the bridge must retain the closed assertion name. -/
def witnessStatement (arena statement : Expr) (theoremName : Name) : MetaM Name := budget do
  let fail {α : Type} : MetaM α := throwError "unclassified_form:dtr.witness_statement_identity"
  unless statement.isAppOfArity ``Not 1 do fail
  let .const claimName [] := statement.appArg! | fail
  let .defnInfo claim ← getConstInfo claimName | fail
  let .thmInfo result ← getConstInfo theoremName | fail
  unless claim.levelParams.isEmpty && result.levelParams.isEmpty &&
      #[claim.type, claim.value, result.type, result.value].all closedExpression &&
      (← isDefEq claim.type (mkSort .zero)) do fail
  let domain ← mkAppM (witnessArenaName.str "Domain") #[arena]
  let predicate ← mkAppM (witnessArenaName.str "predicate") #[arena]
  let universal ← withLocalDeclD `d domain fun d => mkForallFVars #[d] (mkApp predicate d)
  unless (← isDefEq (mkConst claimName) universal) &&
      (← isDefEq result.type (mkNot universal)) &&
      (← isDefEq (← inferType result.value) (mkNot (mkConst claimName))) &&
      (← checked theoremName (mkNot (mkConst claimName))) do fail
  return claimName

/-- The pair must concern the selected actual and the fixed true comparison.
No existential variation over unrelated realizations establishes this contract. -/
def witnessEvidence (arena actual : Expr) (variation sensitivity : Name) :
    MetaM (Option String) := do
  let normalized ← normalizeArena arena
  let positive ← mkAppM ``PrimitiveLawArena.Law #[normalized.law, actual]
  let constantTrue ← mkAppM (witnessArenaName.str "constantTrue") #[arena]
  let negative := mkNot (← mkAppM ``PrimitiveLawArena.Law #[normalized.law, constantTrue])
  let pair ← attempt do
    let .thmInfo info ← getConstInfo variation | throwError "expected theorem"
    let type ← whnfR info.type
    unless type.isAppOfArity ``And 2 do throwError "expected pair"
    return type
  unless ← bounded (do
      let some pair := pair | return false
      let selected := pair.getAppArgs[0]!
      unless selected.isAppOfArity ``PrimitiveLawArena.Law 2 ||
          selected.isAppOfArity (witnessArenaName.str "Law") 2 do return false
      return (← isDefEq selected.appArg! actual) && (← isDefEq selected positive)) do
    return some "unclassified_form:dtr.witness_bridge_requires_positive_variation"
  unless ← bounded (do
      let some pair := pair | return false
      let rejected := pair.getAppArgs[1]!
      unless rejected.isAppOfArity ``Not 1 do return false
      let rejected := rejected.appArg!
      unless rejected.isAppOfArity ``PrimitiveLawArena.Law 2 ||
          rejected.isAppOfArity (witnessArenaName.str "Law") 2 do return false
      return (← isDefEq rejected.appArg! constantTrue) &&
        (← isDefEq pair.getAppArgs[1]! negative) &&
        (← checked variation (mkAnd positive negative))) do
    return some "unclassified_form:dtr.witness_bridge_requires_negative_variation"
  unless ← bounded (checked sensitivity (← mkAppM ``FiniteSlotSensitivity #[normalized.law])) do
    return some "unclassified_form:dtr.witness_bridge_requires_sensitivity"
  return none

def variationError (root catalog theoremName arena : Name)
    (domain reason : String) : String :=
  s!"IE-C048 RealizationIgnoredByLaw key={root}/{catalog}/{theoremName} \
    law_arena={arena} signature={arena}.signature domain={domain} reason={reason}"

/-- Identify slots in the signature's finite enumeration order. Only indices are
reflected, never realizations, states, outputs or Law truth tables. -/
private def indices (indexType fintype : Expr) : MetaM (Array Expr) := do
  let elems ← mkAppOptM ``Fintype.elems #[some indexType, some fintype]
  let multiset ← whnf (← mkAppM ``Finset.val #[elems])
  unless multiset.isAppOfArity ``Quot.mk 3 do
    throwError "cannot reflect registration signature indices"
  let mut remaining := multiset.getArg! 2
  let mut result := #[]
  repeat
    remaining ← whnf remaining
    if remaining.isAppOfArity ``List.nil 1 then break
    unless remaining.isAppOfArity ``List.cons 3 do
      throwError "cannot reflect registration signature index list"
    result := result.push (remaining.getArg! 1)
    remaining := remaining.getArg! 2
  return result

def witness? (name : Name) : MetaM (Option Expr) := do
  if name.isAnonymous then return none
  attempt do
    let value ← mkConstWithFreshMVarLevels name
    unless ← checked name (← inferType value) do throwError "invalid witness"
    return value

private def projection? (name : Name) (proof : Option Expr) : MetaM (Option Expr) := do
  try
    let some proof := proof | return none
    return some (← mkAppM name #[proof])
  catch _ => return none

def slotSupport (kind : String) (indexType fintype expected : Expr)
    (witness : Option Expr) : MetaM (Array (String × Bool)) := do
  let slots ← indices indexType fintype
  let expected ← whnf expected
  let .forallE _ _ body _ := expected | throwError "invalid slot sensitivity contract"
  slots.mapIdxM fun ordinal slot => do
    let valid ← bounded do
      let some witness := witness | return false
      let proof := mkApp witness slot
      unless ← isDefEq (← inferType proof) (body.instantiate1 slot) do return false
      let proof ← instantiateMVars proof
      if proof.hasMVar then return false
      checkWithKernel proof
      return true
    return (s!"{kind}[{ordinal}]", valid)

/-- `support` lists precisely the slots with kernel-checked sensitivity evidence;
the identified primitive is the first failed obligation (readouts, then anchors).
Absence of evidence does not assert a proof of semantic independence. -/
def sensitivityError (root catalog theoremName arena : Name)
    (slots : Array (String × Bool)) : Option String := do
  let failed ← slots.find? (! ·.2)
  let support := Json.arr (((slots.filter (·.2)).map (·.1)).qsort (· < ·) |>.map Json.str)
  return s!"IE-C049 UnusedPrimitiveInBundle key={root}/{catalog}/{theoremName} \
    signature={arena}.signature primitive={failed.1} support={support.compress}"

/-- Accept an existential witness or the specified pair form `Law r ∧ ¬Law r'`.
The fresh realizations must be solved at the registered signature. -/
private def finiteVariation (arena : Expr) (name : Name) : MetaM Bool := do
  if name.isAnonymous then return false
  let expected ← mkAppM ``FiniteLawVariation #[arena]
  if ← bounded (checked name expected) then return true
  try
    let proof ← mkConstWithFreshMVarLevels name
    let type ← whnfR (← inferType proof)
    unless type.isAppOfArity ``And 2 do return false
    let positive := type.getAppArgs[0]!
    let negative := type.getAppArgs[1]!
    unless negative.isAppOfArity ``Not 1 do return false
    let negative := negative.getAppArgs[0]!
    unless positive.isAppOfArity ``PrimitiveLawArena.Law 2 &&
        negative.isAppOfArity ``PrimitiveLawArena.Law 2 do return false
    let r := positive.getAppArgs[1]!
    let r' := negative.getAppArgs[1]!
    let sig ← mkAppM ``PrimitiveLawArena.signature #[arena]
    let realizationType ← mkAppM ``PrimitiveRealization #[sig]
    unless (← isDefEq (← inferType r) realizationType) &&
        (← isDefEq (← inferType r') realizationType) do return false
    let law ← mkAppM ``PrimitiveLawArena.Law #[arena, r]
    let law' ← mkAppM ``PrimitiveLawArena.Law #[arena, r']
    checked name (mkAnd law (mkNot law'))
  catch _ => return false

/-- Pure evidence validation. The source-bound report carries the result; the
protected-base consumer owns delta membership, never an olean or an environment
variable captured during compilation. C048 has strict precedence over C049. -/
def validateFinite (entry : InformationRegistryEntry) : MetaM (Option String) := budget do
  -- P1 retains its independent semantic contract on every raw reifier argument.
  -- Declared-template assessment owns the readout plan and its argument audit;
  -- witness validation never expands a whole realization as a fallback.
  if let some certificate := entry.derivedCertificate then
    if let .error diagnostic ← providerArgumentsCurrent entry.theoremName
        certificate.descriptor.getAppArgs 524288 then
      let parts := diagnostic.splitOn ":"
      let reason := parts.head!
      let rule := parts[1]?.getD "dtr.argument_audit"
      return some s!"IE-C050 ClosedTruthReadout \
        key={entry.registrationModuleName}/{entry.effectiveCatalogId}/{entry.theoremName} \
        reason={reason} rule={rule} site=\"p1.arguments\""
  let bridgeType := (← getConstInfo entry.realizationName).type
  if bridgeType.isAppOfArity witnessBridgeName 3 then
    return ← witnessEvidence (← mkConstWithFreshMVarLevels entry.arenaName)
      bridgeType.getAppArgs[2]! entry.variationWitness entry.sensitivityWitness
  if entry.variationWitness.isAnonymous then
    return some <| variationError entry.registrationModuleName entry.effectiveCatalogId
      entry.theoremName entry.arenaName "all" "missing_witness"
  trace[InformationRegistration.check] "finite witness obligations: {entry.theoremName}"
  let arena := (← normalizeArena (← mkConstWithFreshMVarLevels entry.arenaName)).law
  unless ← bounded (finiteVariation arena entry.variationWitness) do
    return some <| variationError entry.registrationModuleName entry.effectiveCatalogId
      entry.theoremName entry.arenaName "all" "invalid_witness"
  if ← bounded (do
      checked entry.sensitivityWitness (← mkAppM ``FiniteSlotSensitivity #[arena])) then
    return none
  let witness ← witness? entry.sensitivityWitness
  let sig ← mkAppM ``PrimitiveLawArena.signature #[arena]
  let expected ← whnf (← mkAppM ``FiniteSlotSensitivity #[arena])
  let readouts ← slotSupport "readout"
    (← mkAppM ``PrimitiveSignature.Index #[sig])
    (← mkAppM ``PrimitiveSignature.indexFintype #[sig]) expected.getAppArgs[0]!
    (← projection? ``And.left witness)
  let anchors ← slotSupport "anchor"
    (← mkAppM ``PrimitiveSignature.AnchorIndex #[sig])
    (← mkAppM ``PrimitiveSignature.anchorFintype #[sig]) expected.getAppArgs[1]!
    (← projection? ``And.right witness)
  return sensitivityError entry.registrationModuleName entry.effectiveCatalogId
    entry.theoremName entry.arenaName (readouts ++ anchors)

/-- Distinct modules can register the same imported unit; metadata must not
collide before the existing seal-level collision diagnostic can run. -/
def diagnosticName (unitName registrationModule : Name) : Name :=
  (unitName.str registrationModule.toString).str "__information_registration_diagnostic"

/-- Registration diagnostics are source-bound metadata, excluded by Inspector
from statement identity. Their value is a literal, not executable report logic. -/
def publishDiagnostic (unitName : Name) (diagnostic : Option String) : MetaM Unit := do
  let name := diagnosticName unitName (← getEnv).header.mainModule
  if (← getEnv).contains name then throwError "registration diagnostic already exists: {name}"
  addDecl <| .defnDecl {
    name, levelParams := [], type := mkConst ``String
    value := mkStrLit (diagnostic.getD ""), hints := .abbrev, safety := .safe }

end LeanInformationAudit.RegistrationGates
