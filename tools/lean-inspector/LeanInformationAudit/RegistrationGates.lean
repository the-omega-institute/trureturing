import LeanInformationAudit.RegistryTypes
import LeanInformationAudit.ReadoutProvenance
import LeanInformationAudit.RegistrationWitnesses

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
  if let some error ← provenanceErrorCurrent entry.registrationModuleName
      entry.effectiveCatalogId entry.theoremName entry.realizationName then return some error
  if entry.variationWitness.isAnonymous then
    return some <| variationError entry.registrationModuleName entry.effectiveCatalogId
      entry.theoremName entry.arenaName "all" "missing_witness"
  trace[InformationRegistration.check] "finite witness obligations: {entry.theoremName}"
  let arena ← mkConstWithFreshMVarLevels entry.arenaName
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
