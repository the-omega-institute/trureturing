import LeanInformationAuditRegAnalysis.SearchReduction.Commands
import LeanInformationAuditRegTests.SearchReduction.VocabularyCandidates

/-! Positive/negative transport probes and a deliberately unsound-copy mutant. -/
open Lean Meta Elab Command
open LeanInformationAudit.SearchReduction
open LeanInformationAudit.Tests.SearchReduction

private partial def literalCopy (source : Environment) (n : Name) : MetaM Unit := do
  if (← getEnv).contains n then return
  let some info := (source.setExporting false).find? n | throwError "missing mutant input"
  for dep in info.getUsedConstantsAsSet do literalCopy source dep
  match info with
  | .defnInfo value => addDecl (.defnDecl value)
  | .thmInfo value => addDecl (.thmDecl value)
  | _ => throwError "unsupported mutant input"

run_meta do
  let source ← getEnv
  enableInitializersExecution
  let base ← importModules #[{module := `Mathlib},
    {module := `LeanInformationAuditRegTests.SearchReduction.Baseline}]
    options 0 (leakEnv := true) (loadExts := true)
  enableInitializersExecution
  discard <| referenceHints
  let check := fun n => withEnv base do
    copyVocabulary source n
    let original := ((source.setExporting false).find? n).get!
    let rebuilt ← getConstInfo n
    unless ← isDefEq original.type rebuilt.type do throwError "transport changed type: {n}"
    return ← getEnv
  let modes ← check ``VocabularyCandidates.PureMode
  unless modes.contains ``VocabularyCandidates.PureMode.ab do throwError "missing constructor"
  unless modes.contains (``VocabularyCandidates.PureMode ++ `casesOn) do throwError "missing casesOn"
  discard <| check ``VocabularyCandidates.ForwardLaw
  discard <| check ``VocabularyCandidates.nestedBox
  let first ← check ``VocabularyCandidates.easyBox
  let second ← check ``VocabularyCandidates.easyBoxOther
  let firstInfo := (first.find? ``VocabularyCandidates.easyBox).get!
  let secondInfo := (second.find? ``VocabularyCandidates.easyBoxOther).get!
  unless firstInfo.value? == secondInfo.value? do throwError "author proof body changed reconstruction"
  for (n, _) in first.constants.toList do
    if base.contains n then continue
    if let some info := (source.setExporting false).find? n then
      if ← withEnv source (isProp info.type) then
        throwError "author Prop constant leaked: {n}"
  let hard := ``VocabularyCandidates.hardBox
  let rejected ← try
    discard <| check hard
    pure false
  catch ex =>
    let detail ← ex.toMessageData.toString
    unless detail.startsWith "search.vocabulary_obligation_unclosed" do throw ex
    logInfo detail
    pure true
  unless rejected do throwError "hard embedded certificate accepted"
  -- Mutation: literal copying of an author's proof reference changes rejection
  -- into a kernel-accepted definition. This is precisely the leak being tested.
  withEnv base do
    literalCopy source hard
    let target := ((source.setExporting false).find? ``VocabularyCandidates.hardProjection).get!
    let hints ← strategies (← getEnv)
    let (copiedRun, _) ← search (← getEnv) target.levelParams target.type #[] hints
    unless copiedRun == .found do throwError "literal-copy mutation was not detected"
    unless classify true false copiedRun false false (.incomplete .missing) == .bindOnly do
      throwError "mutant did not change the insufficient verdict"
    logInfo "literal-copy mutant: bind-only; prefix reconstruction: insufficient"

run_meta do
  let source ← getEnv
  enableInitializersExecution
  let base ← importModules #[{module := `Mathlib},
    {module := `LeanInformationAuditRegTests.SearchReduction.Baseline}]
    options 0 (leakEnv := true) (loadExts := true)
  enableInitializersExecution
  discard <| referenceHints
  withEnv base do
    copyVocabulary source ``VocabularyCandidates.easyBox
    let target := ((source.setExporting false).find? ``VocabularyCandidates.easyProjection).get!
    let (outcome, rows) ← search (← getEnv) target.levelParams target.type #[] (← strategies (← getEnv))
    unless outcome == .found && rows.any (·.proof?.isSome) do
      throwError "easy projection reconstruction did not produce a certificate"
    unless classifyCertified true (.incomplete .undecided) outcome false false
        (.incomplete .missing) == .bindOnly do throwError "easy projection was not bind-only"
    logInfo "easy certificate projection: bind-only; kernel-checked complete original type"

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

#guard privateNameResult = Verdict.nonBindOnly
#print axioms privateNameResult.pairedProof
