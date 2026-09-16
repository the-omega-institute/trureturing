import LeanInformationAudit.RegistrationGates
import LeanInformationAudit.Syntax

open Lean LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape

namespace RegistrationPositive

def arena : PrimitiveLawArena.{0,0,0} where
  toArena := Arena.ofFintype Bool
  signature := {
    Index := Unit, indexFintype := inferInstance, indexDecidableEq := inferInstance
    Output := fun _ => Bool, outputDecidableEq := fun _ => inferInstance
    axis := fun _ => .cut, readoutAxisNotAnchor := by simp
    AnchorIndex := Fin 0, anchorFintype := inferInstance, anchorDecidableEq := inferInstance }
  Law r := r.readout () false = false

def good : PrimitiveRealization arena.signature := ⟨fun _ x => x, Fin.elim0⟩
def bad : PrimitiveRealization arena.signature := ⟨fun _ _ => true, Fin.elim0⟩
theorem lawVariation : arena.Law good ∧ ¬arena.Law bad := ⟨rfl, Bool.noConfusion⟩
theorem slotSensitivity : FiniteSlotSensitivity arena := by
  constructor
  · intro i
    refine ⟨good, bad, ?_, ?_, ?_⟩
    · intro j ne; cases i; cases j; exact (ne rfl).elim
    · intro j; exact Fin.elim0 j
    · exact ⟨fun _ => lawVariation.2, fun _ => lawVariation.1⟩
  · intro i; exact Fin.elim0 i

local instance : DecidableEq arena.State := arena.toArena.stateDecidableEq
theorem source : arena.Law good := rfl
theorem bridge : LegacyPrimitiveRealization arena (arena.Law good) good := ⟨Iff.rfl⟩
register_information_theorem source in arena primitives good.toPrimitiveBundle
  realization bridge variation lawVariation sensitivity slotSensitivity

information_theorem nativePositive in arena primitives good
  variation lawVariation sensitivity slotSensitivity : arena.Law good := rfl

abbrev objectArena : Arena := arena.toArena
information_theorem nativeOccurrence in arena object_arena objectArena catalog witnessed
  primitives good variation lawVariation sensitivity slotSensitivity : arena.Law good := rfl
theorem legacyOccurrence : arena.Law good := rfl
register_information_theorem legacyOccurrence in arena object_arena objectArena catalog witnessed
  primitives good.toPrimitiveBundle realization bridge
  variation lawVariation sensitivity slotSensitivity

run_cmd Elab.Command.liftTermElabM do
  for name in [``nativePositive, ``nativeOccurrence, ``legacyOccurrence] do
    let some nativeEntry := InformationRegistry.find? (← getEnv) name
      | throwError "NativePositive: missing registration"
    if let some error ← RegistrationGates.validateFinite nativeEntry then throwError "{error}"
  let some entry := InformationRegistry.find? (← getEnv) ``source
    | throwError "Positive: missing registration"
  if let some error ← RegistrationGates.validateFinite entry then throwError "{error}"

/-- info: IE-C048 -/
#guard_msgs in
run_cmd Elab.Command.liftTermElabM do
  let some entry := InformationRegistry.find? (← getEnv) ``source
    | throwError "missing registration"
  let some message ← RegistrationGates.validateFinite { entry with variationWitness := ``bridge }
    | throwError "IffBridge: accepted an Iff.rfl bridge as Law variation"
  unless message.endsWith "reason=invalid_witness" do throwError "{message}"
  logInfo "IE-C048"

run_cmd Elab.Command.liftCoreM do
  let root := `LeanInformationAudit.Tests.RegistrationGates.Positive
  let inputs ← TemplateBinding.moduleInputs (← getEnv) root
  let paths := inputs.map (·.path)
  let theoremUnit := "D5/S3/ConceptDynamics/InformationEscape/TheoremUnit.lean"
  unless paths.contains theoremUnit do
    throwError "[FAIL] indirect_judge_import_retains_content_input"
  let judgePaths := paths.filter (·.startsWith "tools/lean-inspector/")
  unless judgePaths.all (· == TemplateAudit.sourcePath root) do
    throwError "[FAIL] indirect_judge_import_excludes_judge_inputs"
  logInfo "[PASS] indirect_judge_import_content_closure"

run_meta do
  let root := `LeanInformationAudit.Tests.RegistrationGates.Positive
  let theoremUnit := "D5/S3/ConceptDynamics/InformationEscape/TheoremUnit.lean"
  let snapshot ← TemplateBinding.exportSnapshot
  let registered := snapshot.originals.filter (·.occurrence.key.registrationModule == root)
    |>.map (·.occurrence.key)
  let wires ← TemplateBinding.reportJson #[(root, registered)]
  let some wire := wires[0]? | throwError "[FAIL] indirect_judge_import_retains_content_input"
  let .ok wireInputs := wire.getObjValAs? (Array Json) "inputs"
    | throwError "[FAIL] indirect_judge_import_retains_content_input"
  let wirePaths := wireInputs.map fun input =>
    match input.getObjValAs? String "path" with | .ok path => path | .error _ => ""
  logInfo s!"[METADATA] indirect_judge_import_wire_paths={wirePaths.toList}"
  unless wirePaths.contains theoremUnit do
    throwError "[FAIL] indirect_judge_import_retains_content_input"
  let wireJudgePaths := wirePaths.filter (·.startsWith "tools/lean-inspector/")
  unless wireJudgePaths.all (· == TemplateAudit.sourcePath root) do
    throwError "[FAIL] indirect_judge_import_excludes_judge_inputs"
end RegistrationPositive
