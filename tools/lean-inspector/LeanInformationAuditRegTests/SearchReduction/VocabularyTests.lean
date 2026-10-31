import LeanInformationAuditRegAnalysis.SearchReduction.Commands
import LeanInformationAuditRegTests.SearchReduction.VocabularyCandidates

/-! Isolated production vocabulary and private-name regressions. -/
open Lean Meta Elab Command
open LeanInformationAudit.SearchReduction
open LeanInformationAudit.Tests.SearchReduction

#search_reduction LeanInformationAudit.Tests.SearchReduction.VocabularyCandidates.hardProjection
  at "b530df86e6e9c4709edecd3009bb96c3d4ebc8be"
  baseline [LeanInformationAuditRegTests.SearchReduction.Baseline]
  using [] as hardCertificateResult
#guard hardCertificateResult = Verdict.insufficient
#guard hardCertificateResult.reason.startsWith "search.target_in_vocabulary_certificate"

#search_reduction LeanInformationAudit.Tests.SearchReduction.VocabularyCandidates.modeReflexive
  at "b530df86e6e9c4709edecd3009bb96c3d4ebc8be"
  baseline [LeanInformationAuditRegTests.SearchReduction.Baseline]
  using [] as pureInductiveResult
#guard pureInductiveResult = Verdict.bindOnly

run_cmd do
  let env ← getEnv
  let some (name, _) := env.constants.toList.find? fun (n, _) =>
    isPrivateName n && match n with
      | .str _ part => part == "privateStructure"
      | _ => false
    | throwError "private structure missing"
  let target := mkIdent ``VocabularyCandidates.privateConsumer
  let extra := mkIdent name
  let baseModule := mkIdent `LeanInformationAuditRegTests.SearchReduction.Baseline
  let resultName := mkIdent `privateNameResult
  elabCommand (← `(#search_reduction $target
    at "b530df86e6e9c4709edecd3009bb96c3d4ebc8be"
    baseline [$baseModule]
    using [$extra] as $resultName))

#guard privateNameResult.paired = Run.found
#print axioms privateNameResult.pairedProof

run_cmd do
  let source ← getEnv
  enableInitializersExecution
  let base ← importModules #[{module := `Mathlib.Tactic}]
    LeanInformationAudit.SearchReduction.options 0 (leakEnv := false) (loadExts := true)
  let constructor := ``VocabularyCandidates.PureMode.ab
  let request : Request := {
    target := ``VocabularyCandidates.modeReflexive, «baseline» := #[],
    additions := #[constructor], baselineCommit := "b530df86e6e9c4709edecd3009bb96c3d4ebc8be"}
  if base.contains constructor then throwError "constructor fixture is already baseline"
  let .ok (clean, _, _) ← prepare source base request false
    | throwError "constructor fixture baseline preparation failed"
  unless clean.contains constructor do throwError "constructor was not rebuilt as vocabulary"
  let paired ← prepare source clean request true (originalBaseline? := some base)
  let .ok _ := paired
    | let .error (_, reason) := paired | throwError "missing constructor result"
      throwError "rebuilt constructor misclassified as baseline: {reason}"
  let protectedResult ← prepare source clean request true (originalBaseline? := some clean)
  let .error (_, reason) := protectedResult
    | throwError "actual baseline constructor was accepted as added structure"
  unless reason.startsWith "search.structure_already_in_baseline:" do
    throwError "actual baseline constructor rejected for the wrong reason: {reason}"
  logInfo "constructor origin: rebuilt common vocabulary accepted; original baseline rejected"
