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
  unless message.endsWith "primitive=anchor[0] support=[]" do throwError "{message}"
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
namespace Partial

def arena : PrimitiveLawArena.{0,0,0} where
  toArena := Arena.ofFintype Bool
  signature := {
    Index := Unit, indexFintype := inferInstance, indexDecidableEq := inferInstance
    Output := fun _ => Bool, outputDecidableEq := fun _ => inferInstance
    axis := fun _ => .cut, readoutAxisNotAnchor := by simp
    AnchorIndex := Unit, anchorFintype := inferInstance, anchorDecidableEq := inferInstance }
  Law r := r.readout () false = false ∧ r.anchor () = false

def good : PrimitiveRealization arena.signature := ⟨fun _ x => x, fun _ => false⟩
def bad : PrimitiveRealization arena.signature := ⟨fun _ _ => true, fun _ => false⟩
theorem lawVariation : FiniteLawVariation arena :=
  ⟨good, bad, ⟨rfl, rfl⟩, fun h => Bool.noConfusion h.1⟩
-- Valid readout family, absent anchor family: the payload retains checked support.
theorem partialSensitivity :
    (∀ i : arena.signature.Index, ∃ r r' : PrimitiveRealization arena.signature,
      (∀ j, j ≠ i → r.readout j = r'.readout j) ∧
      (∀ j, r.anchor j = r'.anchor j) ∧ (arena.Law r ↔ ¬ arena.Law r')) ∧ True := by
  constructor
  · intro i
    refine ⟨good, bad, ?_, ?_, ?_⟩
    · intro j ne; cases i; cases j; exact (ne rfl).elim
    · intro j; rfl
    · exact ⟨fun _ h => Bool.noConfusion h.1, fun _ => ⟨rfl, rfl⟩⟩
  · trivial

local instance : DecidableEq arena.State := arena.toArena.stateDecidableEq
information_theorem positive in arena primitives good
  variation lawVariation sensitivity partialSensitivity : arena.Law good := ⟨rfl, rfl⟩
run_cmd Elab.Command.liftTermElabM do
  let some entry := InformationRegistry.find? (← getEnv) ``positive
    | throwError "PartialAnchor: missing registration"
  let some message ← RegistrationGates.validateFinite entry
    | throwError "PartialAnchor: missing anchor sensitivity accepted"
  unless message.endsWith "primitive=anchor[0] support=[\"readout[0]\"]" do
    throwError "{message}"
end Partial
end RegistrationAnchors
