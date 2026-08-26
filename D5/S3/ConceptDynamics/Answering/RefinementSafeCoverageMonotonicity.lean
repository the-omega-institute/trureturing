/- GID: D5/S3/ConceptDynamics/Answering/RefinementSafeCoverageMonotonicity
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Answering/RefinementSafeCoverageMonotonicity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Refinement preserves safe answers, enlarges their domain, and raises its probability. -/

import D5.S3.ConceptDynamics.Answering.RefinementMonotoneAnswerDomain
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/- Library-search audit trail (2026-08-27):
   * Exact repository hits `refinement_monotone_answer_domain` and
     `answer_domain_monotone` provide the source's pointwise and set-inclusion
     clauses and are applied directly.
   * Repository searches for safe coverage, probability of `answerDomain`, and
     their refinement monotonicity found no declaration stating all clauses.
   * Pinned Mathlib's bundled `ProbabilityMeasure` is the source probability
     carrier, and `measure_mono` is the exact monotonicity result applied below. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Answering.RefinementSafeCoverageMonotonicity

open D5.S3.ConceptDynamics.Answering.RefinementMonotoneAnswerDomain
open D5.S3.ConceptDynamics.Answering.SafeAnswerCoverageMaximality
open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open MeasureTheory

/-- Probability that an admitted state lies in the canonical safe-answer domain. -/
def safeCoverage {X B Y : Type*} [MeasurableSpace X]
    (probability : ProbabilityMeasure X) (A : X -> Prop)
    (q : Concept X B) (T : X -> Y) : ENNReal :=
  (probability : Measure X) (answerDomain A q T)

/-- Refinement preserves each canonical answer, contains the coarse answer
domain, and therefore cannot decrease its probability under any state law. -/
theorem refinement_safe_coverage_monotonicity
    {X C D Y : Type*} [MeasurableSpace X]
    (probability : ProbabilityMeasure X) (A : X -> Prop)
    (q_C : Concept X C) (q_D : Concept X D) (T : X -> Y)
    (refinement : Refines q_C q_D) :
    (forall (x : X), A x -> forall y,
      canonicalSafeAnswer A q_C T (q_C x) = some y ->
        canonicalSafeAnswer A q_D T (q_D x) = some y) /\
      answerDomain A q_C T ⊆ answerDomain A q_D T /\
      safeCoverage probability A q_C T <= safeCoverage probability A q_D T := by
  have hdomain : answerDomain A q_C T ⊆ answerDomain A q_D T :=
    answer_domain_monotone A q_C q_D T refinement
  constructor
  · intro x hx y hanswer
    exact refinement_monotone_answer_domain A q_C q_D T refinement x hx y hanswer
  · constructor
    · exact hdomain
    · exact measure_mono hdomain

#print axioms refinement_safe_coverage_monotonicity

end D5.S3.ConceptDynamics.Answering.RefinementSafeCoverageMonotonicity
