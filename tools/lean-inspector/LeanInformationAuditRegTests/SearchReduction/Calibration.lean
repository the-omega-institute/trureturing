import LeanInformationAuditRegAnalysis.SearchReduction.Commands
import LeanInformationAuditRegTests.SearchReduction.Candidates
import LeanInformationAuditRegTests.SearchReduction.PresentationCandidates

/-! Executed, kernel-checked negative calibration and a paired induction test.
Each command emits a standalone Lean probe under .lake/build/search-reduction. -/
open LeanInformationAudit.Tests.SearchReduction

#search_reduction_config

#search_reduction LeanInformationAudit.Tests.SearchReduction.Candidates.statementAlias
  at "b530df86e6e9c4709edecd3009bb96c3d4ebc8be"
  baseline [LeanInformationAuditRegTests.SearchReduction.Baseline]
  using [] as aliasResult
#guard aliasResult = Verdict.bindOnly
#guard aliasResult.presentation = Run.found

#search_reduction LeanInformationAudit.Tests.SearchReduction.Candidates.wrapped
  at "b530df86e6e9c4709edecd3009bb96c3d4ebc8be"
  baseline [LeanInformationAuditRegTests.SearchReduction.Baseline]
  using [] as wrapResult
#guard wrapResult = Verdict.bindOnly
#guard wrapResult.presentation = Run.found

#search_reduction LeanInformationAudit.Tests.SearchReduction.Candidates.unwrapped
  at "b530df86e6e9c4709edecd3009bb96c3d4ebc8be"
  baseline [LeanInformationAuditRegTests.SearchReduction.Baseline]
  using [] as unwrapResult
#guard unwrapResult = Verdict.bindOnly
#guard unwrapResult.presentation = Run.found

#search_reduction LeanInformationAudit.Tests.SearchReduction.Candidates.moved
  at "b530df86e6e9c4709edecd3009bb96c3d4ebc8be"
  baseline [LeanInformationAuditRegTests.SearchReduction.Baseline]
  using [] as movedResult
#guard movedResult = Verdict.bindOnly
#guard movedResult.presentation = Run.found

#search_reduction LeanInformationAudit.Tests.SearchReduction.Candidates.splitHelper
  at "b530df86e6e9c4709edecd3009bb96c3d4ebc8be"
  baseline [LeanInformationAuditRegTests.SearchReduction.Baseline]
  using [] as splitResult
#guard splitResult = Verdict.bindOnly
#guard splitResult.presentation = Run.found

#search_reduction LeanInformationAudit.Tests.SearchReduction.Candidates.projection
  at "b530df86e6e9c4709edecd3009bb96c3d4ebc8be"
  baseline [LeanInformationAuditRegTests.SearchReduction.Baseline]
  using [] as projectionResult
#guard projectionResult = Verdict.bindOnly
#guard projectionResult.presentation = Run.found

#search_reduction LeanInformationAudit.Tests.SearchReduction.Candidates.package
  at "b530df86e6e9c4709edecd3009bb96c3d4ebc8be"
  baseline [LeanInformationAuditRegTests.SearchReduction.Baseline]
  using [] as packageResult
#guard packageResult = Verdict.bindOnly
#guard packageResult.presentation = Run.found

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
#guard contentResult.presentation = Run.exhausted
#guard contentResult.baseline = Run.exhausted
#guard contentResult.paired = Run.found
#guard contentResult = Verdict.nonBindOnly

#search_reduction LeanInformationAudit.Tests.SearchReduction.Candidates.doubledPair
  at "b530df86e6e9c4709edecd3009bb96c3d4ebc8be"
  baseline [LeanInformationAuditRegTests.SearchReduction.Baseline]
  using [LeanInformationAudit.Tests.SearchReduction.Candidates.addition] as mixedResult
#guard mixedResult.presentation = Run.exhausted
#guard mixedResult.baseline = Run.exhausted
#guard mixedResult.paired = Run.found
#guard mixedResult = Verdict.nonBindOnly

-- These expectations distinguish presentation certification from R(B): the
-- scalar induction theorem is usable by the finite arithmetic conversion but
-- does not close R's original target search.
#search_reduction LeanInformationAudit.Tests.SearchReduction.PresentationCandidates.arithmetic
  at "a5e5b163319079eeb1b4b431395c65e43beb4b07"
  baseline [LeanInformationAuditRegTests.SearchReduction.PresentationBaseline]
  using [] as arithmeticPresentationResult
#guard arithmeticPresentationResult.baseline = Run.exhausted
#guard arithmeticPresentationResult.presentation = Run.found
#guard arithmeticPresentationResult = Verdict.bindOnly
#guard arithmeticPresentationResult.presentationSource =
  `LeanInformationAudit.Tests.SearchReduction.PresentationBaseline.ramp_value

#search_reduction LeanInformationAudit.Tests.SearchReduction.PresentationCandidates.packaged
  at "a5e5b163319079eeb1b4b431395c65e43beb4b07"
  baseline [LeanInformationAuditRegTests.SearchReduction.PresentationBaseline]
  using [] as packagedPresentationResult
#guard packagedPresentationResult.baseline = Run.exhausted
#guard packagedPresentationResult.presentation = Run.found
#guard packagedPresentationResult = Verdict.bindOnly

#search_reduction LeanInformationAudit.Tests.SearchReduction.PresentationCandidates.renamed
  at "a5e5b163319079eeb1b4b431395c65e43beb4b07"
  baseline [LeanInformationAuditRegTests.SearchReduction.PresentationBaseline]
  using [] as renamedPresentationResult
#guard renamedPresentationResult.baseline = Run.exhausted
#guard renamedPresentationResult.presentation = Run.found
#guard renamedPresentationResult = Verdict.bindOnly

#search_reduction LeanInformationAudit.Tests.SearchReduction.PresentationCandidates.iffForward
  at "a5e5b163319079eeb1b4b431395c65e43beb4b07"
  baseline [LeanInformationAuditRegTests.SearchReduction.Baseline]
  using [] as forwardPresentationResult
#guard forwardPresentationResult.presentation = Run.found
#guard forwardPresentationResult = Verdict.bindOnly

#search_reduction LeanInformationAudit.Tests.SearchReduction.PresentationCandidates.iffBackward
  at "a5e5b163319079eeb1b4b431395c65e43beb4b07"
  baseline [LeanInformationAuditRegTests.SearchReduction.Baseline]
  using [] as backwardPresentationResult
#guard backwardPresentationResult.presentation = Run.found
#guard backwardPresentationResult = Verdict.bindOnly

#print axioms aliasResult.baselineProof
#print axioms packageResult.baselineProof
#print axioms contentResult.pairedProof
#print axioms contentResult.baselineFailureGuard
#print axioms mixedResult.pairedProof
#print axioms aliasResult.presentationConversion
#print axioms wrapResult.presentationConversion
#print axioms projectionResult.presentationConversion
#print axioms packageResult.presentationConversion
#print axioms arithmeticPresentationResult.presentationConversion
#print axioms arithmeticPresentationResult.presentationProof
#print axioms packagedPresentationResult.presentationProof
#print axioms renamedPresentationResult.presentationProof
#print axioms forwardPresentationResult.presentationConversion
#print axioms backwardPresentationResult.presentationConversion
