import LeanInformationAudit.RegistryTypes
import LeanInformationAudit.RegistrationWitnesses

namespace LeanInformationAudit.RegistrationGates
open Lean Meta
open D5.S3.ConceptDynamics.InformationEscape

/-- Zero proof synthesis and no realization enumeration. Each obligation,
including type construction, has a fresh fixed elaboration budget. -/
private def bounded (action : MetaM Bool) : MetaM Bool := do
  try
    withCurrHeartbeats <| withOptions
      (fun o => (o.set `maxHeartbeats (200000 : Nat)).set `maxRecDepth (1024 : Nat)) action
  catch _ => return false

private def checked (name : Name) (expected : Expr) : MetaM Bool := do
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

private def variationError (root catalog theoremName arena : Name) (domain reason : String) : String :=
  s!"IE-C048 RealizationIgnoredByLaw key={root}/{catalog}/{theoremName} \
    law_arena={arena} signature={arena}.signature domain={domain} reason={reason}"

private def sensitivityError (root catalog theoremName arena : Name) : String :=
  s!"IE-C049 UnusedPrimitiveInBundle key={root}/{catalog}/{theoremName} \
    signature={arena}.signature primitive=null support=null"

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
def validateFinite (entry : InformationRegistryEntry) : MetaM (Option String) := do
  let arena ← mkConstWithFreshMVarLevels entry.arenaName
  unless ← bounded (finiteVariation arena entry.variationWitness) do
    return some <| variationError entry.registrationModuleName entry.effectiveCatalogId
      entry.theoremName entry.arenaName "all"
      (if entry.variationWitness.isAnonymous then "missing_witness" else "invalid_witness")
  unless ← bounded (do
      checked entry.sensitivityWitness (← mkAppM ``FiniteSlotSensitivity #[arena])) do
    return some <| sensitivityError entry.registrationModuleName entry.effectiveCatalogId
      entry.theoremName entry.arenaName
  return none

def validateStructural (entry : DispositionCensus.StructuralProvenanceEntry) :
    MetaM (Option String) := do
  let arena ← mkConstWithFreshMVarLevels entry.lawArenaConst
  let domain := if entry.domainName.isAnonymous then "all" else entry.domainName.toString
  let validVariation ← bounded do
    let variation ← if entry.domainName.isAnonymous then
        mkAppM ``StructuralPrimitiveLawArena.Nondegenerate #[arena]
      else
        let declaredDomain ← mkConstWithFreshMVarLevels entry.domainName
        mkAppM ``StructuralDomainVariation #[arena, declaredDomain]
    checked entry.certificateName variation
  unless validVariation do
    return some <| variationError entry.registrationModule entry.canonicalArena
      entry.theoremName entry.lawArenaConst domain
      (if entry.certificateName.isAnonymous then "missing_witness"
       else if entry.domainName.isAnonymous then "invalid_witness" else "outside_domain")
  let validSensitivity ← bounded do
    let sensitivity ← if entry.domainName.isAnonymous then
        mkAppM ``StructuralSlotSensitivity #[arena]
      else
        let declaredDomain ← mkConstWithFreshMVarLevels entry.domainName
        mkAppM ``StructuralDomainSlotSensitivity #[arena, declaredDomain]
    checked entry.sensitivityWitness sensitivity
  unless validSensitivity do
    return some <| sensitivityError entry.registrationModule entry.canonicalArena
      entry.theoremName entry.lawArenaConst
  return none
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
