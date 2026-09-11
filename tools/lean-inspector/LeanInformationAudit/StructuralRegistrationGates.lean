import LeanInformationAudit.RegistrationGates
import LeanInformationAudit.StructuralRealization

/- Structural obligations stay on the structural consumer's import path.
Finite roots need neither this realization layer nor its proof dependencies. -/
namespace LeanInformationAudit
open Lean Meta
open D5.S3.ConceptDynamics.InformationEscape
universe u v w

/-- A restricted intervention domain is a subtype of the same realizations. -/
def StructuralDomainVariation {arena : StructuralArena.{u}}
    (A : StructuralPrimitiveLawArena.{u, v, w} arena)
    (domain : StructuralPrimitiveRealization arena A.signature → Prop) : Prop :=
  ∃ r r' : {r : StructuralPrimitiveRealization arena A.signature // domain r},
    A.Law r.val ∧ ¬ A.Law r'.val

/-- Forgetting the checked membership proofs preserves Law variation. -/
theorem StructuralDomainVariation.nondegenerate {arena : StructuralArena.{u}}
    {A : StructuralPrimitiveLawArena.{u, v, w} arena}
    {domain : StructuralPrimitiveRealization arena A.signature → Prop}
    (witness : StructuralDomainVariation A domain) : A.Nondegenerate := by
  obtain ⟨r, r', yes, no⟩ := witness
  exact ⟨r.val, r'.val, yes, no⟩

def StructuralSlotSensitivity {arena : StructuralArena.{u}}
    (A : StructuralPrimitiveLawArena.{u, v, w} arena) : Prop :=
  ∀ i : A.signature.Index, ∃ r r' : StructuralPrimitiveRealization arena A.signature,
    (∀ j, j ≠ i → r.readout j = r'.readout j) ∧ (A.Law r ↔ ¬ A.Law r')

def StructuralDomainSlotSensitivity {arena : StructuralArena.{u}}
    (A : StructuralPrimitiveLawArena.{u, v, w} arena)
    (domain : StructuralPrimitiveRealization arena A.signature → Prop) : Prop :=
  ∀ i : A.signature.Index,
    ∃ r r' : {r : StructuralPrimitiveRealization arena A.signature // domain r},
      (∀ j, j ≠ i → r.val.readout j = r'.val.readout j) ∧ (A.Law r.val ↔ ¬ A.Law r'.val)

namespace RegistrationGates

/-- One certificate type contract for registration and disposition consumers. -/
def structuralVariationType (entry : DispositionCensus.StructuralProvenanceEntry)
    (arena : Expr) : MetaM Expr := do
  if entry.domainName.isAnonymous then
    mkAppM ``StructuralPrimitiveLawArena.Nondegenerate #[arena]
  else
    let declaredDomain ← mkConstWithFreshMVarLevels entry.domainName
    mkAppM ``StructuralDomainVariation #[arena, declaredDomain]

/-- Check the declared contract before forgetting any subtype membership evidence.
The returned proof always has the canonical unrestricted Nondegenerate type. -/
def structuralNondegenerate? (entry : DispositionCensus.StructuralProvenanceEntry)
    (arena : Expr) : MetaM (Option Expr) := do
  attempt do
    unless ← checked entry.certificateName (← structuralVariationType entry arena) do
      throwError "invalid structural variation"
    let witness ← mkConstWithFreshMVarLevels entry.certificateName
    let canonical ← if entry.domainName.isAnonymous then pure witness else
      mkAppM ``StructuralDomainVariation.nondegenerate #[witness]
    unless ← isDefEq (← inferType canonical)
        (← mkAppM ``StructuralPrimitiveLawArena.Nondegenerate #[arena]) do
      throwError "invalid canonical nondegeneracy"
    let canonical ← instantiateMVars canonical
    if canonical.hasMVar then throwError "unresolved canonical nondegeneracy"
    checkWithKernel canonical
    return canonical

def validateStructural (entry : DispositionCensus.StructuralProvenanceEntry) :
    MetaM (Option String) := budget do
  if let some error ← provenanceErrorCurrent entry.registrationModule
      entry.canonicalArena entry.theoremName entry.realizationConst then return some error
  let domain := if entry.domainName.isAnonymous then "all" else entry.domainName.toString
  if entry.certificateName.isAnonymous then
    return some <| variationError entry.registrationModule entry.canonicalArena
      entry.theoremName entry.lawArenaConst domain "missing_witness"
  trace[InformationRegistration.check] "structural witness obligations: {entry.theoremName}"
  let arena ← mkConstWithLevelParams entry.lawArenaConst
  let validVariation := (← structuralNondegenerate? entry arena).isSome
  unless validVariation do
    return some <| variationError entry.registrationModule entry.canonicalArena
      entry.theoremName entry.lawArenaConst domain "invalid_witness"
  let sensitivity ← if entry.domainName.isAnonymous then
      mkAppM ``StructuralSlotSensitivity #[arena]
    else
      let declaredDomain ← mkConstWithFreshMVarLevels entry.domainName
      mkAppM ``StructuralDomainSlotSensitivity #[arena, declaredDomain]
  let validSensitivity ← bounded (checked entry.sensitivityWitness sensitivity)
  if validSensitivity then return none
  let sig ← mkAppM ``StructuralPrimitiveLawArena.signature #[arena]
  let slots ← slotSupport "readout"
    (← mkAppM ``StructuralPrimitiveSignature.Index #[sig])
    (← mkAppM ``StructuralPrimitiveSignature.indexFintype #[sig]) sensitivity
    (← witness? entry.sensitivityWitness)
  return sensitivityError entry.registrationModule entry.canonicalArena
    entry.theoremName entry.lawArenaConst slots

end RegistrationGates
end LeanInformationAudit
