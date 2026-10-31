import LeanInformationAuditRegAnalysis.SearchReduction.Commands
import LeanInformationAuditRegTests.SearchReduction.NativeSignatures

/-! Native nested signatures, deep views, query extensions and checked export. -/
open Lean Meta Elab Command LeanInformationAudit.SearchReduction
set_option Elab.async false
set_option maxHeartbeats 0 in
run_cmd do
  enableInitializersExecution
  let base ← importModules #[{module := `Lean}] {} 0 (leakEnv := false) (loadExts := true)
  let table ← onDemandLookup {environment := base, fixture := true}
  liftTermElabM do
    withEnv base do
      let entry : DiskLookup.Entry := {
        module := "LeanInformationAuditRegTests.SearchReduction.NativeSignatures",
        name := "LeanInformationAudit.Tests.SearchReduction.NativeSignatures.nested_impossible",
        parts := #["LeanInformationAudit", "Tests", "SearchReduction",
          "NativeSignatures", "nested_impossible"].map (fun s => (s, 0))}
      let query ← getEnv
      let some load := table.load? | throwError "native loader missing"
      discard <| load entry none (mkConst ``False)
      let mut extensions := 0
      for extension in ← persistentEnvExtensionsRef.get do
        let ext := extension.toEnvExtension
        unless ptrEq (ext.getState (asyncMode := .sync) query).state
            (ext.getState (asyncMode := .sync) (← getEnv)).state do
          throwError "query extension state changed: {extension.name}"
        unless (ext.getState (asyncMode := .sync) (← getEnv)).importedEntries.size ==
            (← getEnv).header.moduleNames.size do
          throwError "native module metadata domain mismatch: {extension.name}"
        extensions := extensions + 1
      discard <| pure <| getReducibilityStatusCore (← getEnv)
        ``LeanInformationAudit.Tests.SearchReduction.NativeSignatures.nested_impossible
      discard <| synthInstance (← mkAppM ``DecidableEq #[mkConst ``Nat])
      setEnv query
      let goal ← mkFreshExprMVar (mkConst ``False)
      let trace ← attemptLookupLeaf table entry goal.mvarId!
        (fun _ => pure false) (fun _ => pure false)
      unless trace.complete && trace.source?.isNone && trace.failures.isEmpty do
        throwError "native nested signature did not normally fail: {trace.failures}"
      let entry := {entry with
        name := "LeanInformationAudit.Tests.SearchReduction.NativeSignatures.deep_conjunction",
        parts := #["LeanInformationAudit", "Tests", "SearchReduction",
          "NativeSignatures", "deep_conjunction"].map (fun s => (s, 0))}
      let goal ← mkFreshExprMVar (mkConst ``True)
      let trace ← attemptLookupLeaf table entry goal.mvarId!
        (fun _ => pure false) (fun _ => pure false)
      unless trace.complete && trace.source?.isSome && (← goal.mvarId!.isAssigned) do
        throwError "deep conjunction did not produce a checked native certificate: {trace.failures}"
      emitLookupRecord s!"LOOKUP_NATIVE_CERTIFICATION query_extensions={extensions} nested=normal-failure depth=40 certificate=kernel-checked"
