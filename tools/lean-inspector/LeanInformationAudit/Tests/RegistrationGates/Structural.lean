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
def bad : StructuralPrimitiveRealization arena law.signature := ⟨fun _ _ => 1⟩
theorem variation : law.Nondegenerate := ⟨good, bad, rfl, Nat.one_ne_zero⟩
theorem sensitivity : StructuralSlotSensitivity law := by
  intro i
  refine ⟨good, bad, ?_, ?_⟩
  · intro j ne; exact (ne (Subsingleton.elim _ _)).elim
  · exact ⟨fun _ => Nat.one_ne_zero, fun _ => rfl⟩
structural_theorem positive in law realization good nondegeneracy variation
  sensitivity sensitivity := rfl

run_cmd Elab.Command.liftTermElabM do
  let some entry := (structuralProvenanceEntries (← getEnv)).find? (·.theoremName == ``positive)
    | throwError "StructuralPresent: missing registration"
  if let some message ← RegistrationGates.validateStructural entry then throwError "{message}"

/-- info: IE-C048 -/
#guard_msgs in
run_cmd Elab.Command.liftTermElabM do
  let entry := ((structuralProvenanceEntries (← getEnv)).find? (·.theoremName == ``positive)).get!
  let some message ← RegistrationGates.validateStructural { entry with certificateName := .anonymous }
    | throwError "StructuralAbsent: missing Nondegenerate accepted"
  unless message.endsWith "reason=missing_witness" do throwError "{message}"
  logInfo "IE-C048"

-- A restricted Γ uses the subtype as the realization domain; an unrestricted
-- Nondegenerate theorem cannot justify a restricted-domain variation.
def domain (r : StructuralPrimitiveRealization arena law.signature) : Prop := law.Law r
/-- info: IE-C048 -/
#guard_msgs in
run_cmd Elab.Command.liftTermElabM do
  let entry := ((structuralProvenanceEntries (← getEnv)).find? (·.theoremName == ``positive)).get!
  let some message ← RegistrationGates.validateStructural { entry with domainName := ``domain }
    | throwError "StructuralOutsideDomain: unrestricted witness accepted"
  unless message.endsWith "reason=outside_domain" do throwError "{message}"
  logInfo "IE-C048"
end RegistrationStructural
