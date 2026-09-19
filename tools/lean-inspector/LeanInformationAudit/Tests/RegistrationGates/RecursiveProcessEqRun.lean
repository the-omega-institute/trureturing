import LeanInformationAudit.Tests.RegistrationGates.RecursivePrograms
import LeanInformationAudit.Tests.RegistrationGates.DeclaredStructural
import LeanInformationAudit.Tests.SourceIsolation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option trace.InformationTemplate.work true

open LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape
open Lean Meta Elab Command

namespace LeanInformationAudit.Tests.RecursiveProcessEqRun

open LeanInformationAudit.Tests.RecursivePrograms

abbrev InputState := List Nat × List Nat
abbrev arena : StructuralArena := ⟨InputState⟩

def signature : StructuralPrimitiveSignature where
  Index := Bool
  indexFintype := inferInstance
  Output := fun _ => List Nat

def listReadouts (A : StructuralArena) (sig : StructuralPrimitiveSignature)
    (f : forall i, A.State -> sig.Output i) : StructuralPrimitiveRealization A sig := ⟨f⟩

register_information_template listReadouts constructors 1 [List]

def processSide (state : InputState) : List Nat := process state.1 state.2

def runSide (state : InputState) : List Nat :=
  (run state.1 state.2).1 ++ (run state.1 state.2).2

-- Inspect native types and proof-erased definition values. The bounded path
-- witness distinguishes the generated matcher guard from executable source
-- operations without entering any theorem or proof implementation.
run_meta do
  let mut pending := #[( ``processSide, ([] : List String)), (``runSide, [])]
  let mut visited : NameSet := {}
  let mut found := false
  for _ in [:256] do
    if pending.isEmpty then break
    let (name, path) := pending[0]!
    pending := pending.extract 1 pending.size
    if visited.contains name then continue
    visited := visited.insert name
    if name == `Nat.bitwise then
      logInfo m!"KERNEL_DEPENDENCY_PATH {String.intercalate " -> " path}"
      found := true
      break
    let .defnInfo info ← getConstInfo name | continue
    for (kind, raw) in #[("type", info.type), ("body", info.value)] do
      let (erased, _) ← TemplateAudit.eraseProofs raw
      for next in erased.getUsedConstants do
        if next.toString.startsWith "LeanInformationAudit.Tests.Recursive" ||
            #[`Nat.hasNotBit, `Nat.land, `Nat.shiftRight, `Nat.bitwise].contains next then
          pending := pending.push (next, path ++ [s!"{name}.{kind}:{next}"])
  unless found do throwError "missing actual sparse-matcher bitwise dependency path"

def law : StructuralPrimitiveLawArena arena where
  signature := signature
  Law r := forall state, r.readout false state = r.readout true state

def actual : StructuralPrimitiveRealization arena law.signature :=
  listReadouts arena signature
    (fun i state => Bool.rec (processSide state) (runSide state) i)

def bad : StructuralPrimitiveRealization arena law.signature :=
  listReadouts arena signature
    (fun i _ => Bool.rec [] [0] i)

theorem actualLaw : law.Law actual := by
  intro state
  exact process_eq_run state.1 state.2

theorem badNotLaw : ¬ (law.Law bad) := by
  intro h
  simpa [bad, listReadouts] using h ([], [])

theorem lawVariation : law.Nondegenerate := ⟨actual, bad, actualLaw, badNotLaw⟩

theorem slotSensitive : StructuralSlotSensitivity law := by
  intro i
  cases i with
  | false =>
      refine ⟨listReadouts arena signature
          (fun j _ => Bool.rec [] [] j),
        listReadouts arena signature
          (fun j _ => Bool.rec [0] [] j), ?_, ?_⟩
      · intro j hne
        cases j with
        | false => exact (hne rfl).elim
        | true => rfl
      · constructor
        · intro _ h
          simpa [listReadouts] using h ([], [])
        · intro _ _
          rfl
  | true =>
      refine ⟨listReadouts arena signature
          (fun j _ => Bool.rec [] [] j),
        listReadouts arena signature
          (fun j _ => Bool.rec [] [0] j), ?_, ?_⟩
      · intro j hne
        cases j with
        | false => rfl
        | true => exact (hne rfl).elim
      · constructor
        · intro _ h
          simpa [listReadouts] using h ([], [])
        · intro _ _
          rfl

structural_theorem exactProcessEqRun in law
  readout via (listReadouts arena signature
    (fun i state => Bool.rec (processSide state) (runSide state) i))
  realization (listReadouts arena signature
    (fun i state => Bool.rec (processSide state) (runSide state) i))
  nondegeneracy lawVariation sensitivity slotSensitive := by
    intro state
    exact process_eq_run state.1 state.2

run_meta do
  let some row := (TemplateBinding.records (← getEnv)).find?
      (·.occurrence.key.theoremName == ``exactProcessEqRun)
    | throwError "probe: missing process_eq_run binding record"
  match row.result with
  | .declaredValidated certificate =>
      logInfo m!"FULL_LAW_STATE process_eq_run declared_validated evidence={certificate.evidenceRef} arguments={certificate.argumentInputs.size} extraction={certificate.extractionInputs.size}"
      unless certificate.argumentInputs.any (·.name == ``drain) do
        throwError "missing actual recursive drain dependency"
      let omitted := { certificate with argumentInputs :=
        certificate.argumentInputs.filter (·.name != ``drain) }
      let .ok (changedIdentity, _) := TemplateAudit.bindingIdentity
          row.occurrence.statementIdentity omitted 524288
        | throwError "omission control exceeded its identity budget"
      unless changedIdentity != certificate.evidenceRef do
        throwError "[FAIL] recursive_dependency_omission_identity"
      logInfo "[PASS] recursive_dependency_omission_identity"
      let wires ← TemplateBinding.reportJson #[(row.occurrence.key.registrationModule, #[row.occurrence.key])]
      logInfo m!"FULL_LAW_EVIDENCE {(Lean.Json.arr wires).compress}"
      LeanInformationAudit.Tests.withPrivateSources do
        let owner := `LeanInformationAudit.Tests.RegistrationGates.RecursivePrograms
        IO.FS.removeFile (TemplateAudit.sourcePath owner)
        let rejected ← try
          TemplateAudit.NativeCoherence.validate #[owner]
          pure false
        catch error => pure ((← error.toMessageData.toString).contains "E7.native_hash")
        unless rejected do throwError "[FAIL] recursive_missing_dependency_source"
        logInfo "[PASS] recursive_missing_dependency_source"
      -- Omit an actual imported native input, after the loaded snapshot is
      -- established. Restore the exact bytes before returning to Lake.
      let owner := `LeanInformationAudit.Tests.RegistrationGates.RecursivePrograms
      TemplateAudit.NativeCoherence.validate #[owner]
      let nativeTrace := (← findOLean owner).withExtension "trace"
      let original ← IO.FS.readBinFile nativeTrace
      IO.FS.withTempDir fun directory => do
        let savedTrace := directory / "recursive.trace"
        IO.FS.rename nativeTrace savedTrace
        try
          let rejected ← try
            TemplateAudit.NativeCoherence.validate #[owner]
            pure false
          catch error => pure ((← error.toMessageData.toString).contains "E7.native_hash")
          unless rejected do throwError "[FAIL] recursive_missing_native_input"
          logInfo "[PASS] recursive_missing_native_input"
        finally
          IO.FS.rename savedTrace nativeTrace
          unless (← IO.FS.readBinFile nativeTrace) == original do
            throwError "recursive native input restoration failed"
      TemplateAudit.NativeCoherence.validate #[owner]
      logInfo "[PASS] recursive_restored_native_input"
  | .declaredUnresolved diagnostic =>
      logError m!"FULL_LAW_STATE process_eq_run declared_unresolved diagnostic={diagnostic}"
  | .undeclared => logError "FULL_LAW_STATE process_eq_run undeclared"

#print axioms exactProcessEqRun

end LeanInformationAudit.Tests.RecursiveProcessEqRun
