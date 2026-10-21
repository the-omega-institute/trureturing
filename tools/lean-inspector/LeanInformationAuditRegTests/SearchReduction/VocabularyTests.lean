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

#guard privateNameResult = Verdict.nonBindOnly
#print axioms privateNameResult.pairedProof
