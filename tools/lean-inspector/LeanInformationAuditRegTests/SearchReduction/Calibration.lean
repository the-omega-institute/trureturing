import LeanInformationAuditRegAnalysis.SearchReduction.Commands
import LeanInformationAuditRegTests.SearchReduction.Candidates
import LeanInformationAuditRegTests.SearchReduction.PresentationCandidates
import LeanInformationAuditRegTests.SearchReduction.GraphCandidates

/-! Executed, kernel-checked negative calibration and a paired induction test.
Each command emits a standalone Lean probe under .lake/build/search-reduction. -/
open LeanInformationAudit.SearchReduction
open LeanInformationAudit.Tests.SearchReduction

#search_reduction_config

-- A compliant baseline lookup certificate makes the square witness bind-only.
#search_reduction_certificates [by_lookup Nat.exists_mul_self]
#search_reduction LeanInformationAudit.Tests.SearchReduction.GraphCandidates.squareVia
  at "b530df86e6e9c4709edecd3009bb96c3d4ebc8be"
  baseline [LeanInformationAuditRegTests.SearchReduction.Baseline]
  using [LeanInformationAudit.Tests.SearchReduction.GraphCandidates.squareFact] as squareResult
#guard squareResult = Verdict.bindOnly
#guard squareResult.baseline = Run.found
#guard squareResult.paired = Run.found

#search_reduction LeanInformationAudit.Tests.SearchReduction.GraphCandidates.squareVia
  at "b530df86e6e9c4709edecd3009bb96c3d4ebc8be"
  baseline [LeanInformationAuditRegTests.SearchReduction.Baseline]
  using [LeanInformationAudit.Tests.SearchReduction.GraphCandidates.trueFact] as neutralTrueResult
#guard neutralTrueResult = Verdict.bindOnly
#guard neutralTrueResult.baseline = Run.found
#guard neutralTrueResult.paired = Run.found

#search_reduction LeanInformationAudit.Tests.SearchReduction.GraphCandidates.squareVia
  at "b530df86e6e9c4709edecd3009bb96c3d4ebc8be"
  baseline [LeanInformationAuditRegTests.SearchReduction.Baseline]
  using [LeanInformationAudit.Tests.SearchReduction.GraphCandidates.arithmeticFact] as neutralArithmeticResult
#guard neutralArithmeticResult = Verdict.bindOnly
#guard neutralArithmeticResult.baseline = Run.found
#guard neutralArithmeticResult.paired = Run.found

#search_reduction_certificates []

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
#guard intermediateResult.baseline = Run.incomplete Failure.undecided
#guard intermediateResult = Verdict.insufficient

#search_reduction LeanInformationAudit.Tests.SearchReduction.Candidates.content
  at "b530df86e6e9c4709edecd3009bb96c3d4ebc8be"
  baseline [LeanInformationAuditRegTests.SearchReduction.Baseline]
  using [LeanInformationAudit.Tests.SearchReduction.Candidates.intermediate] as arithmeticRestatementResult
#guard arithmeticRestatementResult.baseline = Run.incomplete Failure.undecided
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

#search_reduction LeanInformationAudit.Tests.SearchReduction.Candidates.doubledPair
  at "b530df86e6e9c4709edecd3009bb96c3d4ebc8be"
  baseline [LeanInformationAuditRegTests.SearchReduction.Baseline]
  using [LeanInformationAudit.Tests.SearchReduction.Candidates.addition] as mixedResult
#guard mixedResult.presentation = Run.exhausted

-- The finite arithmetic conversion supplies an independent presentation
-- certificate with its actual single source.
#search_reduction LeanInformationAudit.Tests.SearchReduction.PresentationCandidates.arithmetic
  at "a5e5b163319079eeb1b4b431395c65e43beb4b07"
  baseline [LeanInformationAuditRegTests.SearchReduction.PresentationBaseline]
  using [] as arithmeticPresentationResult
#guard arithmeticPresentationResult.presentation = Run.found
#guard arithmeticPresentationResult = Verdict.bindOnly
#guard arithmeticPresentationResult.presentationSource =
  `LeanInformationAudit.Tests.SearchReduction.PresentationBaseline.ramp_value

#search_reduction LeanInformationAudit.Tests.SearchReduction.PresentationCandidates.packaged
  at "a5e5b163319079eeb1b4b431395c65e43beb4b07"
  baseline [LeanInformationAuditRegTests.SearchReduction.PresentationBaseline]
  using [] as packagedPresentationResult
#guard packagedPresentationResult.presentation = Run.found
#guard packagedPresentationResult = Verdict.bindOnly

#search_reduction LeanInformationAudit.Tests.SearchReduction.PresentationCandidates.renamed
  at "a5e5b163319079eeb1b4b431395c65e43beb4b07"
  baseline [LeanInformationAuditRegTests.SearchReduction.PresentationBaseline]
  using [] as renamedPresentationResult
#guard renamedPresentationResult.presentation = Run.found
#guard renamedPresentationResult = Verdict.bindOnly

#search_reduction LeanInformationAudit.Tests.SearchReduction.PresentationCandidates.iffForward
  at "a5e5b163319079eeb1b4b431395c65e43beb4b07"
  baseline [LeanInformationAuditRegTests.SearchReduction.Baseline]
  using [] as forwardPresentationResult
#guard forwardPresentationResult.presentation = Run.found
#guard forwardPresentationResult.presentationSource =
  `LeanInformationAudit.Tests.SearchReduction.Baseline.commuted
#guard forwardPresentationResult = Verdict.bindOnly

#search_reduction LeanInformationAudit.Tests.SearchReduction.PresentationCandidates.iffBackward
  at "a5e5b163319079eeb1b4b431395c65e43beb4b07"
  baseline [LeanInformationAuditRegTests.SearchReduction.Baseline]
  using [] as backwardPresentationResult
#guard backwardPresentationResult.presentation = Run.found
#guard backwardPresentationResult.presentationSource =
  `LeanInformationAudit.Tests.SearchReduction.Baseline.commuted
#guard backwardPresentationResult = Verdict.bindOnly

#print axioms aliasResult.baselineProof
#print axioms squareResult.pairedProof
#print axioms squareResult.baselineProof
#print axioms packageResult.baselineProof
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
