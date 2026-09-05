import LeanInformationAudit.Tests.Census.Evidence

open Lean LeanInformationAudit DispositionCensus
open Lean.Elab.Command

namespace LeanInformationAudit.Tests.Census.Evidence

private def alterFinite (f : {key : StatementKey} → FiniteOccurrenceDisposition key →
    FiniteOccurrenceDisposition key) : DispositionInventory :=
  { inventory with entries := inventory.entries.map fun ⟨key, disposition⟩ =>
      ⟨key, match disposition with
        | .finiteOccurrence value => .finiteOccurrence (f value)
        | value => value⟩ }

/-- error: IE-C037 DispositionClassMismatch theorem=LeanInformationAudit.Tests.SealSuccess.idTheorem class=finite_occurrence invalid=state_enumeration_certificate -/
#guard_msgs in
run_cmd liftTermElabM do
  validateEvidence `LeanInformationAudit.Tests.SealSuccess
    (alterFinite fun value => { value with stateEnumerationCertificate := `Missing })

/-- error: IE-C037 DispositionClassMismatch theorem=LeanInformationAudit.Tests.SealSuccess.idTheorem class=finite_occurrence invalid=nondegeneracy_certificate -/
#guard_msgs in
run_cmd liftTermElabM do
  validateEvidence `LeanInformationAudit.Tests.SealSuccess
    (alterFinite fun value => { value with nondegeneracyCertificate := ``closedNumerical })

private def alterStructural (f : {key : StatementKey} → StructuralOccurrenceDisposition key →
    StructuralOccurrenceDisposition key) : DispositionInventory :=
  { inventory with entries := inventory.entries.map fun ⟨key, disposition⟩ =>
      ⟨key, match disposition with
        | .structuralOccurrence value => .structuralOccurrence (f value)
        | value => value⟩ }

/-- error: IE-C038 MissingStructuralWitness theorem=LeanInformationAudit.Tests.Census.Evidence.structuralTheorem arena=LeanInformationAudit.Tests.Census.Evidence.infiniteArena missing=witness_certificate -/
#guard_msgs in
run_cmd liftTermElabM do
  validateEvidence `LeanInformationAudit.Tests.SealSuccess
    (alterStructural fun value => { value with witnessCertificate := `Missing })

/-- error: IE-C038 MissingStructuralWitness theorem=LeanInformationAudit.Tests.Census.Evidence.structuralTheorem arena=LeanInformationAudit.Tests.Census.Evidence.infiniteArena missing=witness_certificate -/
#guard_msgs in
run_cmd liftTermElabM do
  validateEvidence `LeanInformationAudit.Tests.SealSuccess
    (alterStructural fun value => { value with witnessCertificate := ``closedNumerical })

abbrev aliasArena := infiniteArena

/-- error: IE-C036 DispositionIdentityMismatch theorem=LeanInformationAudit.Tests.Census.Evidence.structuralTheorem component=canonical_arena expected=LeanInformationAudit.Tests.Census.Evidence.infiniteArena actual=LeanInformationAudit.Tests.Census.Evidence.aliasArena -/
#guard_msgs in
run_cmd liftTermElabM do
  validateEvidence `LeanInformationAudit.Tests.SealSuccess
    (alterStructural fun value => { value with canonicalArena := ``aliasArena })

private def alterBounded (f : {key : StatementKey} → BoundedFiniteTruncationDisposition key →
    BoundedFiniteTruncationDisposition key) : DispositionInventory :=
  { inventory with entries := inventory.entries.map fun ⟨key, disposition⟩ =>
      ⟨key, match disposition with
        | .boundedFiniteTruncation value => .boundedFiniteTruncation (f value)
        | value => value⟩ }

/-- error: IE-C037 DispositionClassMismatch theorem=LeanInformationAudit.Tests.Census.Evidence.boundedTheorem class=bounded_finite_truncation invalid=comparison_statement -/
#guard_msgs in
run_cmd liftTermElabM do
  validateEvidence `LeanInformationAudit.Tests.SealSuccess
    (alterBounded fun value => { value with bound := 13 })

/-- error: IE-C037 DispositionClassMismatch theorem=LeanInformationAudit.Tests.Census.Evidence.boundedTheorem class=bounded_finite_truncation invalid=transfer_theorem -/
#guard_msgs in
run_cmd liftTermElabM do
  validateEvidence `LeanInformationAudit.Tests.SealSuccess
    (alterBounded fun value => { value with certification := .transferred ``closedNumerical })

run_cmd liftTermElabM do
  validateEvidence `LeanInformationAudit.Tests.SealSuccess
    (alterBounded fun value => { value with certification := .transferred ``transfer })

/-- error: IE-C037 DispositionClassMismatch theorem=LeanInformationAudit.Tests.Census.Evidence.closedNumerical class=unreachable invalid=reason -/
#guard_msgs in
run_cmd liftTermElabM do
  validateEvidence `LeanInformationAudit.Tests.SealSuccess {
    inventory with entries := inventory.entries.map fun ⟨key, disposition⟩ =>
      ⟨key, match disposition with
        | .unreachable value => .unreachable { value with reason := .noFinitePrimitiveBundle }
        | value => value⟩ }

#print axioms aliasArena

end LeanInformationAudit.Tests.Census.Evidence
