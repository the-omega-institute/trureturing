/- GID: D5/S3/ConceptDynamics/ExperimentDesign/PrefixLawCompletionSeparation
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/ExperimentDesign/PrefixLawCompletionSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Equivalent finite-prefix laws coexist with mutually singular completed laws. -/

import D5.S3.ConceptDynamics.ExperimentBoundary.FinitePrefixInfiniteCompletionSeparation

/- Library-search audit trail (2026-08-26):
   * The frozen predecessor states the exact source theorem on the canonical
     Bernoulli observation system, but was withdrawn solely for placement. The
     redo mandate requires a fresh GID while leaving that module untouched.
   * The imported family is the single source of truth for `finiteTranscript`,
     `stateLaw`, and the completed product laws. No local carrier, law, `def`, or
     `abbrev` is introduced.
   * Pinned Mathlib provides component measure primitives but no full theorem
     joining finite-prefix equivalence with completion singularity. The frozen
     repository theorem is applied directly rather than reproved. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.ExperimentDesign.PrefixLawCompletionSeparation

open MeasureTheory ProbabilityTheory
open D5.S3.ConceptDynamics.Experiment.InfiniteIdentificationFiniteInexactness
open D5.S3.ConceptDynamics.ExperimentBoundary.FinitePrefixInfiniteCompletionSeparation renaming
  finite_prefix_infinite_completion_separation → frozen_prefix_completion_separation

/-- In the canonical two-state Bernoulli observation system, every finite-prefix
law is equivalent in both directions while the completed laws are mutually
singular. -/
theorem finite_prefix_infinite_completion_separation :
    (∀ m : Nat,
      Measure.map (finiteTranscript m) (stateLaw false) ≪
          Measure.map (finiteTranscript m) (stateLaw true) ∧
        Measure.map (finiteTranscript m) (stateLaw true) ≪
          Measure.map (finiteTranscript m) (stateLaw false)) ∧
      stateLaw false ⟂ₘ stateLaw true := by
  change
    (∀ m : Nat,
      Measure.map (finiteTranscript m) (stateLaw false) ≪
          Measure.map (finiteTranscript m) (stateLaw true) ∧
        Measure.map (finiteTranscript m) (stateLaw true) ≪
          Measure.map (finiteTranscript m) (stateLaw false)) ∧
      stateLaw false ⟂ₘ stateLaw true
  exact frozen_prefix_completion_separation

#print axioms finite_prefix_infinite_completion_separation

end D5.S3.ConceptDynamics.ExperimentDesign.PrefixLawCompletionSeparation
