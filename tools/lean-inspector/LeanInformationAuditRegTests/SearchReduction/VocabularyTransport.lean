import LeanInformationAuditRegAnalysis.SearchReduction.Vocabulary
import LeanInformationAuditRegTests.SearchReduction.VocabularyCandidates

/-! Prefix-copy probes and target proof-field leakage rejection. -/
open Lean Meta Elab Command
open LeanInformationAudit.SearchReduction
open LeanInformationAudit.Tests.SearchReduction

-- Aggregate independent probes; each transport and R call enforces its own bound.
set_option maxHeartbeats 0 in
run_meta do
  let source ← getEnv
  enableInitializersExecution
  let base ← importModules #[{module := `Mathlib.Tactic}]
    LeanInformationAudit.SearchReduction.options 0 (leakEnv := false) (loadExts := true)
  let check := fun n => withEnv base do
    copyVocabulary source n
    let original := ((source.setExporting false).find? n).get!
    let rebuilt ← getConstInfo n
    unless ← isDefEq original.type rebuilt.type do throwError "transport changed type: {n}"
    return ← getEnv
  for n in #[``VocabularyCandidates.transportedAlias,
      ``VocabularyCandidates.transportedAbbreviation, ``VocabularyCandidates.transportedHidden,
      ``VocabularyCandidates.transportedRecursion, ``VocabularyCandidates.easyBox] do
    let rebuilt ← check n
    unless getReducibilityStatusCore rebuilt n == .reducible do
      throwError "transported definition is not reducible: {n}"
    let original := ((source.setExporting false).find? n).get!
    let copied := (rebuilt.find? n).get!
    let .ok originalNormal := DiskLookup.normalizeStatementSyntax source original.type
      | throwError "source statement normalization failed: {n}"
    let .ok copiedNormal := DiskLookup.normalizeStatementSyntax rebuilt copied.type
      | throwError "rebuilt statement normalization failed: {n}"
    unless originalNormal == copiedNormal do
      throwError "transport changed syntax normalization: {n}"
  let rebuilt ← check ``VocabularyCandidates.transportedAbbreviation
  let aliasExpr := mkApp (mkConst ``VocabularyCandidates.transportedAlias) (mkNatLit 4)
  let .ok normal := DiskLookup.normalizeStatementSyntax rebuilt aliasExpr
    | throwError "rebuilt alias normalization failed"
  if normal == aliasExpr then throwError "checked noncomputational alias remained opaque"
  withEnv rebuilt do
    let reduced ← withReducible <| whnf aliasExpr
    if reduced == aliasExpr then
      throwError "transported definition remained opaque to reducible lookup"
  logInfo "transport reducibility: copied definitions are reducible; checked syntax aliases still expand"
  let modes ← check ``VocabularyCandidates.PureMode
  unless modes.contains ``VocabularyCandidates.PureMode.ab do throwError "missing constructor"
  unless modes.contains (``VocabularyCandidates.PureMode ++ `casesOn) do throwError "missing casesOn"
  for n in #[``VocabularyCandidates.instDecidableEqPureMode,
      ``VocabularyCandidates.instReprPureMode, ``VocabularyCandidates.instInhabitedPureMode,
      ``VocabularyCandidates.instFintypePureMode] do
    discard <| check n
  let rejectedInstance ← try
    discard <| check ``VocabularyCandidates.noncanonicalRepr
    pure false
  catch ex =>
    unless (← ex.toMessageData.toString).startsWith "search.derived_computation_mismatch" do throw ex
    pure true
  unless rejectedInstance do throwError "author instance computation was replaced"
  let rejectedFintype ← try
    discard <| check ``VocabularyCandidates.noncanonicalFintype
    pure false
  catch ex =>
    unless (← ex.toMessageData.toString).startsWith "search.derived_computation_mismatch" do throw ex
    pure true
  unless rejectedFintype do throwError "author finite enumeration was replaced"
  discard <| check ``VocabularyCandidates.ForwardLaw
  discard <| check ``VocabularyCandidates.nestedBox
  discard <| check ``VocabularyCandidates.representatives
  discard <| check ``VocabularyCandidates.proofFunctionBox
  discard <| check ``VocabularyCandidates.dependentBox
  discard <| check ``VocabularyCandidates.continuousBox
  withEnv base do
    let n := ``VocabularyCandidates.proofIndexedReflexive
    let statement := ((source.setExporting false).find? n).get!.type
    let rebuilt ← copyStatement source n statement
    unless !(rebuilt.getUsedConstants.any (fun name => name.toString.endsWith ".sideTruth")) do
      throwError "proof-index certificate was not inlined"
    let result ← localRebuild rebuilt
    unless result.cost == .zero && result.proof?.isSome do
      throwError "proof-index statement did not reconstruct"
  let first ← check ``VocabularyCandidates.easyBox
  let second ← check ``VocabularyCandidates.easyBoxOther
  let firstInfo := (first.find? ``VocabularyCandidates.easyBox).get!
  let secondInfo := (second.find? ``VocabularyCandidates.easyBoxOther).get!
  unless ← isDefEq firstInfo.value?.get! secondInfo.value?.get! do
    throwError "certificate copy changed computational value"
  let localNames := first.constants.foldStage2 (fun ns n _ => ns.push n) (#[] : Array Name)
  for n in localNames do
    if base.contains n then continue
    if let some info := (source.setExporting false).find? n then
      if ← withEnv source (isProp info.type) then
        throwError "author Prop constant leaked: {n}"
  let hard ← check ``VocabularyCandidates.hardBox
  withEnv hard do
    let target := ((source.setExporting false).find? ``VocabularyCandidates.hardProjection).get!
    let rejected ← try
      checkTargetVocabularyProjections source base target.type
      pure false
    catch ex =>
      unless (← ex.toMessageData.toString).startsWith "search.target_in_vocabulary_certificate" do throw ex
      pure true
    unless rejected do throwError "target proof-field projection escaped the type-only guard"
    logInfo "hard side certificate: checked copy; target proof-field projection: incomplete"

run_meta do
  let source ← getEnv
  enableInitializersExecution
  let base ← importModules #[{module := `Mathlib.Tactic}]
    LeanInformationAudit.SearchReduction.options 0 (leakEnv := false) (loadExts := true)
  enableInitializersExecution
  withEnv base do
    copyVocabulary source ``VocabularyCandidates.easyBox
    let target := ((source.setExporting false).find? ``VocabularyCandidates.easyProjection).get!
    let result ← localRebuild target.type
    unless result.cost == .zero && result.proof?.isSome do
      throwError "easy projection reconstruction did not produce a certificate"
    let rejected ← try
      checkTargetVocabularyProjections source base target.type
      pure false
    catch ex =>
      unless (← ex.toMessageData.toString).startsWith "search.target_in_vocabulary_certificate" do throw ex
      pure true
    unless rejected do throwError "easy target proof-field projection escaped the type-only guard"
    logInfo "easy projection: direct R proof exists; proof-field transport guard: incomplete"
