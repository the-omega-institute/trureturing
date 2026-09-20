import LeanInformationAudit.Tests.RegistrationGates.InlineProvenanceWire
import LeanInformationAudit.Tests.RegistrationGates.InlineRealizationSource
import LeanInformationAudit.Tests.RegistrationGates.Positive
import LeanInformationAudit.Tests.SourceIsolation

namespace LeanInformationAudit.Tests.InlineRealization

open Lean Lean.Meta Lean.Elab Lean.Elab.Command
open LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape
open RegistrationPositive
open LeanInformationAudit.Tests.InlineRealizationSource

local instance : DecidableEq arena.State := arena.toArena.stateDecidableEq

register_information_theorem quantified in arena
  primitives good.toPrimitiveBundle
  realization inline good := by
    exact ⟨fun _ => rfl, fun _ _ _ x => InlineProofHelper.witness_self x⟩
  variation lawVariation sensitivity slotSensitivity

register_information_theorem readoutQuantified in arena
  readout via (missingInlineTemplate good)
  primitives good.toPrimitiveBundle
  realization inline good := by
    exact ⟨fun _ => rfl, fun _ _ _ x => InlineProofHelper.witness_self x⟩
  variation lawVariation sensitivity slotSensitivity

register_information_theorem occurrenceQuantified in arena
  object_arena objectArena catalog inline
  readout via (missingInlineOccurrenceTemplate good)
  primitives good.toPrimitiveBundle
  realization inline good := by
    exact ⟨fun _ => rfl, fun _ _ _ x => InlineProofHelper.witness_self x⟩
  variation lawVariation sensitivity slotSensitivity

register_information_theorem twoUniverses in arena
  primitives good.toPrimitiveBundle
  realization inline good := by
    exact ⟨fun _ => rfl, fun _ _ _ _ _ x => InlineProofHelper.witness_self x⟩
  variation lawVariation sensitivity slotSensitivity

theorem namedTarget : arena.Law good := rfl
theorem namedBridge : LegacyPrimitiveRealization arena (arena.Law good) good := ⟨Iff.rfl⟩
register_information_theorem namedTarget in arena primitives good.toPrimitiveBundle
  realization namedBridge variation lawVariation sensitivity slotSensitivity

run_meta do
  let env ← getEnv
  for theoremName in [``quantified, ``readoutQuantified, ``occurrenceQuantified,
      ``twoUniverses, ``namedTarget] do
    let some entry := InformationRegistry.find? env theoremName
      | throwError "inline registration missing: {theoremName}"
    unless entry.theoremName == theoremName do
      throwError "inline registration retargeted imported theorem: {theoremName}"
    unless (env.find? entry.realizationName).any (fun info => info matches .thmInfo _) do
      throwError "inline registration companion is not a theorem: {entry.realizationName}"
  let some entry := InformationRegistry.find? env ``quantified
    | throwError "inline quantified registration missing"
  let some (.thmInfo bridgeInfo) := env.find? entry.realizationName
    | throwError "inline quantified companion missing"
  unless !bridgeInfo.levelParams.isEmpty do
    throwError "inline quantified companion lost its universe telescope"
  let theoremExpr ← mkConstWithFreshMVarLevels ``quantified
  let bridge ← mkConstWithFreshMVarLevels entry.realizationName
  let bridgeType ← whnfR (← inferType bridge)
  let arguments := bridgeType.getAppArgs
  unless arguments.size == 3 && (← isDefEq arguments[1]! (← inferType theoremExpr)) do
    throwError "inline quantified companion changed the imported theorem type"
  let theoremInfo ← getConstInfo ``twoUniverses
  let some pair := InformationRegistry.find? env ``twoUniverses
    | throwError "inline two-universe registration missing"
  let bridgeInfo ← getConstInfo pair.realizationName
  let pairArgs := bridgeInfo.type.getAppArgs
  unless theoremInfo.levelParams.length == 2 &&
      theoremInfo.levelParams.all (bridgeInfo.levelParams.contains ·) &&
      pairArgs.size == 3 && pairArgs[1]! == theoremInfo.type do
    throwError "inline bridge changed the independent universes or exact theorem type"
  let records := TemplateBinding.records env
  for theoremName in [``readoutQuantified, ``occurrenceQuantified] do
    let some record := records.find? (·.occurrence.key.theoremName == theoremName)
      | throwError "inline readout route missing: {theoremName}"
    unless record.result matches .declaredUnresolved _ do
      throwError "inline readout route bypassed declared-template assessment: {theoremName}"

elab "reject_inline " label:str " in " command:command : command => do
  let before ← getEnv
  let previousMessages := (← get).messages
  modify fun state => { state with messages := {} }
  elabCommand command
  let errors := (← get).messages.toList.filter (·.severity == .error)
  modify fun state => { state with messages := previousMessages }
  let theoremName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo command.raw[1]
  let unitName := localCompanionName before theoremName theoremUnitSuffix
  let realizationName := localCompanionName before theoremName primitiveRealizationSuffix
  let after ← getEnv
  unless !errors.isEmpty && before.contains unitName == after.contains unitName &&
      before.contains realizationName == after.contains realizationName &&
      (InformationRegistry.entries before).size == (InformationRegistry.entries after).size do
    throwError "{label.getString}: rejected inline registration left residue or no error"

theorem wrongStatementTarget : True := trivial
reject_inline "wrong_statement" in
register_information_theorem wrongStatementTarget in arena primitives good.toPrimitiveBundle
  realization inline good := namedBridge

def otherArena : PrimitiveLawArena where
  toArena := Arena.ofFintype (Fin 1)
  signature := {
    Index := Unit, indexFintype := inferInstance, indexDecidableEq := inferInstance
    Output := fun _ => Bool, outputDecidableEq := fun _ => inferInstance
    axis := fun _ => .cut, readoutAxisNotAnchor := by simp
    AnchorIndex := Fin 0, anchorFintype := inferInstance, anchorDecidableEq := inferInstance }
  Law := fun _ => True

theorem wrongArenaTarget : True := trivial
reject_inline "wrong_arena" in
register_information_theorem wrongArenaTarget in otherArena primitives good.toPrimitiveBundle
  realization inline good := namedBridge

theorem wrongBundleTarget : arena.Law good := rfl
reject_inline "wrong_bundle" in
register_information_theorem wrongBundleTarget in arena primitives bad.toPrimitiveBundle
  realization inline good := by exact ⟨Iff.rfl⟩

theorem nonproofTarget : arena.Law good := rfl
reject_inline "nonproof" in
register_information_theorem nonproofTarget in arena primitives good.toPrimitiveBundle
  realization inline good := true

theorem unresolvedTarget : arena.Law good := rfl
reject_inline "unresolved_proof" in
register_information_theorem unresolvedTarget in arena primitives good.toPrimitiveBundle
  realization inline good := unresolvedInlineProof

theorem forbiddenTarget : arena.Law good := rfl
axiom forbiddenBridge : LegacyPrimitiveRealization arena (arena.Law good) good
reject_inline "forbidden_axiom" in
register_information_theorem forbiddenTarget in arena primitives good.toPrimitiveBundle
  realization inline good := forbiddenBridge

private def replaceSource (path : System.FilePath) (bytes : ByteArray) : IO Unit := do
  let temporary := path.withExtension "inline-realization-temporary"
  IO.FS.writeBinFile temporary bytes
  IO.FS.rename temporary path

run_meta LeanInformationAudit.Tests.withPrivateSources do
  let env ← getEnv
  let root := env.header.mainModule
  let helper := `LeanInformationAudit.Tests.RegistrationGates.InlineProofHelper
  let helperPath := TemplateAudit.sourcePath helper
  let inputs ← TemplateBinding.moduleInputs env root
  unless inputs.any (·.path == helperPath) do
    throwError "inline proof helper absent from module inputs"
  let snapshot ← TemplateBinding.exportSnapshot
  let registered := snapshot.originals.filter (·.occurrence.key.registrationModule == root)
    |>.map (·.occurrence.key)
  let wires ← TemplateBinding.reportJson #[(root, registered)]
  let some wire := wires[0]? | throwError "inline registration report missing"
  unless (wire.getObjVal? "inputs").toOption.isNone do
    throwError "report retains untraced source hashes"
  logInfo m!"INLINE_PROVENANCE_REPORT={wire.compress}"
  unless wire.compress == LeanInformationAudit.Tests.InlineProvenanceWire.canonical do
    throwError "[FAIL] INLINE_PROVENANCE_WIRE_MISMATCH: set InlineProvenanceWire.canonical to the JSON after INLINE_PROVENANCE_REPORT= in this module's build log"
  let path : System.FilePath := helperPath
  let original ← IO.FS.readBinFile path
  try
    replaceSource path (original ++ "\n-- changed after native import\n".toUTF8)
    let rejected ← try
      discard <| TemplateBinding.moduleInputs env root
      pure false
    catch error =>
      let reason ← error.toMessageData.toString
      pure (reason == s!"incomplete_closure:E7.native_source:{helper}" ||
        reason == "incomplete_closure:E7.native_input_changed")
    unless rejected do throwError "changed inline proof helper source was accepted"
  finally
    replaceSource path original
    unless (← IO.FS.readBinFile path) == original do
      throwError "inline proof helper source restoration failed"

end LeanInformationAudit.Tests.InlineRealization
