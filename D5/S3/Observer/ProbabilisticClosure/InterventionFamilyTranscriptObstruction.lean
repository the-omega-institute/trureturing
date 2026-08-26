/- GID: D5/S3/Observer/ProbabilisticClosure/InterventionFamilyTranscriptObstruction
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/InterventionFamilyTranscriptObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Reusing one intervention family cannot distinguish models in its joint-law kernel. -/

import D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion

/- Library-search audit trail (2026-08-26):
   * Searches for repeated interventions, same-family kernels, adaptive
     transcripts, sample size, and randomized postprocessing found no exact
     whole-clause D5 theorem.
   * `KernelTranscriptInvariance` covers finite iid repetition and randomized
     postprocessing for one channel. `PassiveAdaptiveTranscriptUpperBound`
     covers deterministic adaptive protocols over a family. Neither states the
     full family-relative target obstruction below.
   * Body-shape search for `fun x i => q i x` found the canonical family profile
     `jointReadout`, imported and instantiated below instead of redeclared.
   * Pinned Mathlib provides equality congruence but no exact intervention-
     family transcript obstruction theorem.
 -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.ProbabilisticClosure.InterventionFamilyTranscriptObstruction

open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion

/-- At the level of statistical laws, every repeated or adaptively rearranged
transcript using only one intervention family is a function of that family's
complete law profile. Thus arbitrary sample sizes and randomized law-level
postprocessing preserve equality on the family kernel and cannot exactly return
two different target values. -/
theorem repeated_intervention_family_kernel_obstruction
    {Intervention Model Law TranscriptLaw DecisionLaw : Type*}
    (law : Intervention -> Model -> Law)
    (target : Model -> DecisionLaw)
    (M N : Model)
    (same_family_law : jointReadout law M = jointReadout law N)
    (different_target : target M = target N -> False)
    (adaptiveTranscriptLaw : Nat -> Nat -> Model -> TranscriptLaw)
    (uses_only_family : forall repetitions sampleSize x y,
      jointReadout law x = jointReadout law y ->
        adaptiveTranscriptLaw repetitions sampleSize x =
          adaptiveTranscriptLaw repetitions sampleSize y) :
    forall (repetitions sampleSize : Nat)
      (randomizedPostprocess : TranscriptLaw -> DecisionLaw),
      randomizedPostprocess
          (adaptiveTranscriptLaw repetitions sampleSize M) =
        randomizedPostprocess
          (adaptiveTranscriptLaw repetitions sampleSize N) /\
      Not (
        randomizedPostprocess
              (adaptiveTranscriptLaw repetitions sampleSize M) =
            target M /\
          randomizedPostprocess
              (adaptiveTranscriptLaw repetitions sampleSize N) =
            target N) := by
  intro repetitions sampleSize randomizedPostprocess
  have sameTranscript :=
    uses_only_family repetitions sampleSize M N same_family_law
  have sameDecision := congrArg randomizedPostprocess sameTranscript
  constructor
  · exact sameDecision
  · rintro ⟨exactM, exactN⟩
    apply different_target
    calc
      target M = randomizedPostprocess
          (adaptiveTranscriptLaw repetitions sampleSize M) := exactM.symm
      _ = randomizedPostprocess
          (adaptiveTranscriptLaw repetitions sampleSize N) := sameDecision
      _ = target N := exactN

#print axioms repeated_intervention_family_kernel_obstruction

end D5.S3.Observer.ProbabilisticClosure.InterventionFamilyTranscriptObstruction
