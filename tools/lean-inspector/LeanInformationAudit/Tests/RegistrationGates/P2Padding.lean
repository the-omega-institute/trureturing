import LeanInformationAudit.RegistrationGates
open D5.S3.ConceptDynamics.InformationEscape
namespace P2Padding
abbrev arena : PrimitiveLawArena.{0,0,0} where
  toArena := Arena.ofFintype (Bool × Bool)
  signature :=
    { Index := Fin 2
      indexFintype := inferInstance
      indexDecidableEq := inferInstance
      Output := fun _ => Bool
      outputDecidableEq := fun _ => inferInstance
      axis := fun _ => .cut
      readoutAxisNotAnchor := by simp
      AnchorIndex := Fin 0
      anchorFintype := inferInstance
      anchorDecidableEq := inferInstance }
  Law := fun r => ∀ x, r.readout 0 x = x.1
local instance : DecidableEq arena.State := arena.toArena.stateDecidableEq
def readouts : PrimitiveRealization arena.signature where
  readout := fun i x => if i = 0 then x.1 else x.2
  anchor := Fin.elim0
theorem source : ∀ x : Bool × Bool, x.1 = x.1 := fun _ => rfl
theorem bridge : LegacyPrimitiveRealization arena (∀ x : Bool × Bool, x.1 = x.1) readouts where
  equivalence := Iff.rfl
register_information_theorem source in arena
  primitives readouts.toPrimitiveBundle realization bridge
def cat : Catalog arena.toArena := Catalog.ofVector ![source.__information_unit]
example : arena.toArena.Nondegenerate := by decide
example : cat.uniqueCaptureCount (0 : Fin 1) = 12 := by decide
def unpadded : PrimitiveRealization arena.signature where
  readout := fun i x => if i = 0 then x.1 else false
  anchor := Fin.elim0
def bad : PrimitiveRealization arena.signature where
  readout := fun _ _ => true
  anchor := Fin.elim0
theorem variation : arena.Law readouts ∧ ¬arena.Law bad := by
  constructor
  · intro x; rfl
  · intro h
    have h0 := h (false,false)
    exact Bool.noConfusion h0
example : arena.Law readouts ↔ arena.Law unpadded := Iff.rfl
example : ¬readouts.toPrimitiveBundle.agrees (false,false) (false,true) := by
  intro h
  have h1 := ((PrimitiveRealization.toPrimitiveBundle_agrees_iff readouts _ _).mp h).1 (1 : Fin 2)
  exact Bool.noConfusion h1
example : unpadded.toPrimitiveBundle.agrees (false,false) (false,true) := by
  apply (PrimitiveRealization.toPrimitiveBundle_agrees_iff unpadded _ _).mpr
  exact ⟨fun _ => rfl, fun j => Fin.elim0 j⟩
def unpaddedUnit : TheoremUnit arena.toArena where
  «primitives» := unpadded.toPrimitiveBundle
  Statement := ∀ x : Bool × Bool, x.1 = x.1
  proof := source
example : (Catalog.ofVector ![unpaddedUnit]).uniqueCaptureCount (0 : Fin 1) = 8 := by decide

-- #6818 probe: the original bundle and Law retain their mathematical behavior.
-- The delta consumer rejects the registration with IE-C049.
/-- info: IE-C049 -/
#guard_msgs in
run_cmd Lean.Elab.Command.liftTermElabM do
  let some entry := InformationRegistry.find? (← Lean.getEnv) ``source
    | throwError "missing probe registration"
  let entry := { entry with variationWitness := ``variation }
  let some message ← RegistrationGates.validateFinite entry
    | throwError "P2Padding: missing expected IE-C049"
  unless message.startsWith "IE-C049 " do throwError "unexpected verdict: {message}"
  Lean.logInfo "IE-C049"
end P2Padding
