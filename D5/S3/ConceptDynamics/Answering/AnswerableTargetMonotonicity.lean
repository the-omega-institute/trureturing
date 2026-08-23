/- GID: D5/S3/ConceptDynamics/Answering/AnswerableTargetMonotonicity
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Answering/AnswerableTargetMonotonicity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Concept refinement monotonically enlarges the set of answerable targets. -/

import D5.S3.ConceptDynamics.Refinement.RefinementTransitivity
import D5.S3.ConceptDynamics.Sufficiency.UniversalSufficiencyFactorization

/- Library-search audit trail (2026-08-23):
   * `RefinementMonotoneAnswerDomain.answer_domain_monotone` is a semantic miss: it
     concerns states receiving a safe answer, not the source's set of target readouts.
   * Exact repository hits `Concept`, `Refines`, `canonicalTargetReadout`, and
     `refinement_transitive` provide the source's canonical concepts, target concept,
     refinement relation, and transitivity rule; all are imported rather than forked.
   * Searches in `D5` and `Golden/Frozen/accepted` found no existing definition of the
     set of targets answerable by a concept and no theorem stating its monotonicity. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Answering.AnswerableTargetMonotonicity

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.Refinement.RefinementTransitivity
open D5.S3.ConceptDynamics.Sufficiency.UniversalSufficiencyFactorization

/-- Targets answerable through a concept are exactly those whose canonical target
readout factors through that concept. -/
def AnswerableTargets {X B Y : Type _} (q_C : Concept X B) : Set (Concept X Y) :=
  {T | Refines (canonicalTargetReadout T) q_C}

/-- Every target answerable through a coarse concept remains answerable through a finer
concept. -/
theorem answerable_target_monotone
    {X C D Y : Type _} (q_C : Concept X C) (q_D : Concept X D)
    (refinement : Refines q_C q_D) :
    AnswerableTargets (Y := Y) q_C ⊆ AnswerableTargets (Y := Y) q_D := by
  intro target targetAnswerable
  exact refinement_transitive (canonicalTargetReadout target) q_C q_D
    refinement targetAnswerable

/-- Identity observation answers every Boolean target that a constant observation can
answer. -/
example :
    AnswerableTargets (Y := Bool) (fun _ : Bool => ()) ⊆
      AnswerableTargets (Y := Bool) (id : Bool → Bool) := by
  apply answerable_target_monotone
  exact ⟨fun _ => (), rfl⟩

#print axioms answerable_target_monotone

end D5.S3.ConceptDynamics.Answering.AnswerableTargetMonotonicity
