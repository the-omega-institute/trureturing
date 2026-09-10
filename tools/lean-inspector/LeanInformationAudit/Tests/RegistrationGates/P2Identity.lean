import LeanInformationAudit.RegistrationGates
import LeanInformationAudit.SealCommand
open LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape
namespace P2Identity
def arena : PrimitiveLawArena.{0,0,0} where
  toArena := Arena.ofFintype Bool
  signature :=
    { Index := Fin 1
      indexFintype := inferInstance
      indexDecidableEq := inferInstance
      Output := fun _ => Bool
      outputDecidableEq := fun _ => inferInstance
      axis := fun _ => .cut
      readoutAxisNotAnchor := by simp
      AnchorIndex := Fin 0
      anchorFintype := inferInstance
      anchorDecidableEq := inferInstance }
  Law := fun _ => (1 + 1 : Nat) = 2
local instance : DecidableEq arena.State := arena.toArena.stateDecidableEq
def readouts : PrimitiveRealization arena.signature where
  readout := fun _ x => x
  anchor := Fin.elim0
theorem source : (1 + 1 : Nat) = 2 := by decide
theorem bridge : LegacyPrimitiveRealization arena ((1 + 1 : Nat) = 2) readouts where
  equivalence := Iff.rfl
register_information_theorem source in arena
  primitives readouts.toPrimitiveBundle realization bridge
def cat : Catalog arena.toArena := Catalog.ofVector ![source.__information_unit]
example : arena.toArena.Nondegenerate := by decide
example : cat.uniqueCaptureCount (0 : Fin 1) = 2 := by decide

-- #6818 probe: the original bundle and Law retain their mathematical behavior.
-- The delta consumer rejects the registration with IE-C048.
/-- info: IE-C048 -/
#guard_msgs in
run_cmd Lean.Elab.Command.liftTermElabM do
  let some entry := InformationRegistry.find? (← Lean.getEnv) ``source
    | throwError "missing probe registration"
  let entry := { entry with variationWitness := .anonymous }
  let some message ← RegistrationGates.validateFinite entry
    | throwError "P2Identity: missing expected IE-C048"
  unless message.startsWith "IE-C048 " do throwError "unexpected verdict: {message}"
  let diagnosticName := RegistrationGates.diagnosticName
    entry.unitName entry.registrationModuleName
  let some info := (← Lean.getEnv).find? diagnosticName
    | throwError "DiagnosticPublication: missing registration metadata"
  unless info.value? == some (Lean.mkStrLit message) do
    throwError "DiagnosticPublication: expected {message}, actual {info.value?}"
  Lean.logInfo "IE-C048"
end P2Identity
