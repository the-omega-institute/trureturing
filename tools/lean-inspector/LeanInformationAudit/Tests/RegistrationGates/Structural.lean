import LeanInformationAudit.DispositionEvidence
import LeanInformationAudit.RegistrationGates

open Lean LeanInformationAudit DispositionCensus
open D5.S3.ConceptDynamics.InformationEscape
namespace RegistrationStructural
abbrev arena : StructuralArena := ⟨Nat⟩
def law : StructuralPrimitiveLawArena arena where
  signature := ⟨Unit, inferInstance, fun _ => Nat⟩
  Law r := r.readout () 0 = 0
def good : StructuralPrimitiveRealization arena law.signature := ⟨fun _ n => n⟩
def bad : StructuralPrimitiveRealization arena law.signature := ⟨fun (_ : Unit) (_ : Nat) => (1 : Nat)⟩
theorem lawVariation : law.Nondegenerate := ⟨good, bad, rfl, Nat.one_ne_zero⟩
theorem slotSensitivity : StructuralSlotSensitivity law := by
  intro i
  refine ⟨good, bad, ?_, ?_⟩
  · intro j ne; cases i; cases j; exact (ne rfl).elim
  · exact ⟨fun _ => Nat.one_ne_zero, fun _ => rfl⟩
structural_theorem positive in law realization good nondegeneracy lawVariation
  sensitivity slotSensitivity := rfl

run_cmd Elab.Command.liftTermElabM do
  let some entry := (structuralProvenanceEntries (← getEnv)).find? (·.theoremName == ``positive)
    | throwError "StructuralPresent: missing registration"
  if let some message ← RegistrationGates.validateStructural entry then throwError "{message}"

structural_theorem absent in law realization good := rfl

/-- info: IE-C048 -/
#guard_msgs in
run_cmd Elab.Command.liftTermElabM do
  let entry := ((structuralProvenanceEntries (← getEnv)).find? (·.theoremName == ``absent)).get!
  let some message ← RegistrationGates.validateStructural entry
    | throwError "StructuralAbsent: missing Nondegenerate accepted"
  unless message.endsWith "reason=missing_witness" do throwError "{message}"
  let name := RegistrationGates.diagnosticName entry.unitConst entry.registrationModule
  unless ((← getConstInfo name).value? == some (mkStrLit message)) do
    throwError "StructuralAbsent: wrong diagnostic metadata"
  logInfo "IE-C048"

/-- info: IE-C049 -/
#guard_msgs in
run_cmd Elab.Command.liftTermElabM do
  let entry := ((structuralProvenanceEntries (← getEnv)).find? (·.theoremName == ``positive)).get!
  let candidate := { entry with sensitivityWitness := .anonymous }
  let some message ← RegistrationGates.validateStructural candidate
    | throwError "StructuralUnused: missing slot sensitivity accepted"
  unless message.startsWith "IE-C049 " do throwError "{message}"
  logInfo "IE-C049"

-- A restricted Γ uses the subtype as the realization domain; an unrestricted
-- Nondegenerate theorem cannot justify a restricted-domain lawVariation.
def restrictedDomain (r : StructuralPrimitiveRealization arena law.signature) : Prop := law.Law r
/-- info: IE-C048 -/
#guard_msgs in
run_cmd Elab.Command.liftTermElabM do
  let entry := ((structuralProvenanceEntries (← getEnv)).find? (·.theoremName == ``positive)).get!
  let candidate := { entry with domainName := ``restrictedDomain }
  let some message ← RegistrationGates.validateStructural candidate
    | throwError "StructuralOutsideDomain: unrestricted witness accepted"
  unless message.endsWith "reason=outside_domain" do throwError "{message}"
  logInfo "IE-C048"
-- Both witnesses inhabit the declared subtype, including its domain proof.
def fullDomain (_ : StructuralPrimitiveRealization arena law.signature) : Prop := True
theorem domainVariation : StructuralDomainVariation law fullDomain :=
  ⟨⟨good, trivial⟩, ⟨bad, trivial⟩, rfl, Nat.one_ne_zero⟩
theorem domainSensitivity : StructuralDomainSlotSensitivity law fullDomain := by
  intro i
  refine ⟨⟨good, trivial⟩, ⟨bad, trivial⟩, ?_, ?_⟩
  · intro j ne; cases i; cases j; exact (ne rfl).elim
  · exact ⟨fun _ => Nat.one_ne_zero, fun _ => rfl⟩
structural_theorem domainPositive in law realization good nondegeneracy domainVariation
  domain fullDomain sensitivity domainSensitivity := rfl
run_cmd Elab.Command.liftTermElabM do
  let entry := ((structuralProvenanceEntries (← getEnv)).find?
    (·.theoremName == ``domainPositive)).get!
  if let some message ← RegistrationGates.validateStructural entry then throwError "{message}"

/-- info: IE-C048 -/
#guard_msgs in
run_cmd Elab.Command.liftTermElabM do
  let entry := ((structuralProvenanceEntries (← getEnv)).find?
    (·.theoremName == ``domainPositive)).get!
  let some message ← RegistrationGates.validateStructural { entry with domainName := ``Nat }
    | throwError "MalformedDomain: invalid domain accepted"
  unless message.startsWith "IE-C048 " do throwError "{message}"
  logInfo "IE-C048"
end RegistrationStructural
