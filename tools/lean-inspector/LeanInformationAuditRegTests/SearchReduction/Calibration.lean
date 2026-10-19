import LeanInformationAuditRegAnalysis.SearchReduction.Commands
import LeanInformationAuditRegTests.SearchReduction.Candidates

/-! Executed, kernel-checked negative calibration and a paired induction test.
Each command emits a standalone Lean probe under .lake/build/search-reduction. -/
open LeanInformationAudit.Tests.SearchReduction

#search_reduction_config

#search_reduction LeanInformationAudit.Tests.SearchReduction.Candidates.statementAlias
  at "b530df86e6e9c4709edecd3009bb96c3d4ebc8be"
  baseline [LeanInformationAuditRegTests.SearchReduction.Baseline]
  using [] as aliasResult
#guard aliasResult = Verdict.bindOnly

#search_reduction LeanInformationAudit.Tests.SearchReduction.Candidates.wrapped
  at "b530df86e6e9c4709edecd3009bb96c3d4ebc8be"
  baseline [LeanInformationAuditRegTests.SearchReduction.Baseline]
  using [] as wrapResult
#guard wrapResult = Verdict.bindOnly

#search_reduction LeanInformationAudit.Tests.SearchReduction.Candidates.unwrapped
  at "b530df86e6e9c4709edecd3009bb96c3d4ebc8be"
  baseline [LeanInformationAuditRegTests.SearchReduction.Baseline]
  using [] as unwrapResult
#guard unwrapResult = Verdict.bindOnly

#search_reduction LeanInformationAudit.Tests.SearchReduction.Candidates.moved
  at "b530df86e6e9c4709edecd3009bb96c3d4ebc8be"
  baseline [LeanInformationAuditRegTests.SearchReduction.Baseline]
  using [] as movedResult
#guard movedResult = Verdict.bindOnly

#search_reduction LeanInformationAudit.Tests.SearchReduction.Candidates.splitHelper
  at "b530df86e6e9c4709edecd3009bb96c3d4ebc8be"
  baseline [LeanInformationAuditRegTests.SearchReduction.Baseline]
  using [] as splitResult
#guard splitResult = Verdict.bindOnly

#search_reduction LeanInformationAudit.Tests.SearchReduction.Candidates.projection
  at "b530df86e6e9c4709edecd3009bb96c3d4ebc8be"
  baseline [LeanInformationAuditRegTests.SearchReduction.Baseline]
  using [] as projectionResult
#guard projectionResult = Verdict.bindOnly

#search_reduction LeanInformationAudit.Tests.SearchReduction.Candidates.package
  at "b530df86e6e9c4709edecd3009bb96c3d4ebc8be"
  baseline [LeanInformationAuditRegTests.SearchReduction.Baseline]
  using [] as packageResult
#guard packageResult = Verdict.bindOnly

#search_reduction LeanInformationAudit.Tests.SearchReduction.Candidates.specialized
  at "b530df86e6e9c4709edecd3009bb96c3d4ebc8be"
  baseline [LeanInformationAuditRegTests.SearchReduction.Baseline]
  using [] as specializationResult
#guard specializationResult = Verdict.bindOnly

#search_reduction LeanInformationAudit.Tests.SearchReduction.Candidates.intermediate
  at "b530df86e6e9c4709edecd3009bb96c3d4ebc8be"
  baseline [LeanInformationAuditRegTests.SearchReduction.Baseline]
  using [] as intermediateResult
#guard intermediateResult.baseline = Run.exhausted
#guard intermediateResult = Verdict.insufficient

#search_reduction LeanInformationAudit.Tests.SearchReduction.Candidates.content
  at "b530df86e6e9c4709edecd3009bb96c3d4ebc8be"
  baseline [LeanInformationAuditRegTests.SearchReduction.Baseline]
  using [LeanInformationAudit.Tests.SearchReduction.Candidates.intermediate] as arithmeticRestatementResult
#guard arithmeticRestatementResult.baseline = Run.exhausted
#guard arithmeticRestatementResult.paired = Run.incomplete Failure.isolation
#guard arithmeticRestatementResult = Verdict.insufficient

#search_reduction LeanInformationAudit.Tests.SearchReduction.Candidates.contentPair
  at "b530df86e6e9c4709edecd3009bb96c3d4ebc8be"
  baseline [LeanInformationAuditRegTests.SearchReduction.Baseline]
  using [LeanInformationAudit.Tests.SearchReduction.Candidates.intermediate] as packedArithmeticResult
#guard packedArithmeticResult = Verdict.insufficient
#guard packedArithmeticResult.paired = Run.incomplete Failure.isolation

#search_reduction LeanInformationAudit.Tests.SearchReduction.Candidates.doubledContent
  at "b530df86e6e9c4709edecd3009bb96c3d4ebc8be"
  baseline [LeanInformationAuditRegTests.SearchReduction.Baseline]
  using [LeanInformationAudit.Tests.SearchReduction.Candidates.addition] as contentResult
#guard contentResult.baseline = Run.exhausted
#guard contentResult.paired = Run.found
#guard contentResult = Verdict.nonBindOnly

#search_reduction LeanInformationAudit.Tests.SearchReduction.Candidates.doubledPair
  at "b530df86e6e9c4709edecd3009bb96c3d4ebc8be"
  baseline [LeanInformationAuditRegTests.SearchReduction.Baseline]
  using [LeanInformationAudit.Tests.SearchReduction.Candidates.addition] as mixedResult
#guard mixedResult = Verdict.nonBindOnly

#print axioms aliasResult.baselineProof
#print axioms packageResult.baselineProof
#print axioms contentResult.pairedProof
#print axioms contentResult.baselineFailureGuard
#print axioms mixedResult.pairedProof
