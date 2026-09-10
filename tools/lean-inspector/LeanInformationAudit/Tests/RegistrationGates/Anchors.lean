import LeanInformationAudit.Tests.RegistrationGates.Positive

open Lean LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape
namespace RegistrationAnchors

def arena : PrimitiveLawArena.{0,0,0} where
  toArena := Arena.ofFintype Bool
  signature := {
    Index := Fin 0, indexFintype := inferInstance, indexDecidableEq := inferInstance
    Output := fun _ => Bool, outputDecidableEq := fun _ => inferInstance
    axis := fun _ => .cut, readoutAxisNotAnchor := by simp
    AnchorIndex := Unit, anchorFintype := inferInstance, anchorDecidableEq := inferInstance }
  Law r := r.anchor () = false

def good : PrimitiveRealization arena.signature := ⟨fun i => Fin.elim0 i, fun _ => false⟩
def bad : PrimitiveRealization arena.signature := ⟨fun i => Fin.elim0 i, fun _ => true⟩
theorem lawVariation : FiniteLawVariation arena := ⟨good, bad, rfl, Bool.noConfusion⟩
theorem slotSensitivity : FiniteSlotSensitivity arena := by
  constructor
  · intro i; exact Fin.elim0 i
  · intro i
    refine ⟨good, bad, ?_, ?_, ?_⟩
    · intro j; exact Fin.elim0 j
    · intro j ne; cases i; cases j; exact (ne rfl).elim
    · exact ⟨fun _ => Bool.noConfusion, fun _ => rfl⟩

local instance : DecidableEq arena.State := arena.toArena.stateDecidableEq
information_theorem positive in arena primitives good
  variation lawVariation sensitivity slotSensitivity : arena.Law good := rfl
run_cmd Elab.Command.liftTermElabM do
  let some entry := InformationRegistry.find? (← getEnv) ``positive
    | throwError "AnchorPositive: missing registration"
  if let some message ← RegistrationGates.validateFinite entry then throwError "{message}"

/-- info: IE-C049 -/
#guard_msgs in
run_cmd Elab.Command.liftTermElabM do
  let some entry := InformationRegistry.find? (← getEnv) ``positive
    | throwError "missing registration"
  let candidate := { entry with sensitivityWitness := ``RegistrationPositive.slotSensitivity }
  let some message ← RegistrationGates.validateFinite candidate
    | throwError "AnchorSupport: a readout-only family omits the anchor obligation"
  unless message.startsWith "IE-C049 " do throwError "{message}"
  logInfo "IE-C049"

/-- info: IE-C048 -/
#guard_msgs in
run_cmd Elab.Command.liftTermElabM do
  let some entry := InformationRegistry.find? (← getEnv) ``positive
    | throwError "missing registration"
  let candidate := { entry with variationWitness := ``RegistrationPositive.lawVariation }
  let some message ← RegistrationGates.validateFinite candidate
    | throwError "SignatureMismatch: witness from another signature accepted"
  unless message.startsWith "IE-C048 " do throwError "{message}"
  logInfo "IE-C048"
end RegistrationAnchors
