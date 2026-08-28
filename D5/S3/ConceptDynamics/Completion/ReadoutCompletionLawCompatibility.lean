/- GID: D5/S3/ConceptDynamics/Completion/ReadoutCompletionLawCompatibility
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Completion/ReadoutCompletionLawCompatibility
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The readout-target law and completion law are the same joint pushforward. -/

import D5.S3.ConceptDynamics.Communication.TranslationLossMonotonicity
import D5.S3.ConceptDynamics.Completion.CompletionInformationCost

/- Library-search audit trail (2026-08-28):
   * The repository search followed the joint-law objects and their defining pushforward,
     rather than guessing a bridge theorem name. No file mentioned both `readoutTargetLaw`
     and `completionLaw`, so no theorem related the two definitions before this module.
   * `Concept` resolves to `ConceptFiberDecomposition.Concept`, whose definition is exactly
     `X → B`; it carries no fields, constraints, quotient, or coercion.
   * Direct inspection of both definitions on `origin/dev` found the same paired observation
     map and the same `pushforward`. Pinned Mathlib cannot contain a theorem naming these two
     repository-local definitions, so the remaining obligation is definitional equality. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Completion.ReadoutCompletionLawCompatibility

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.Communication.TranslationLossMonotonicity
open D5.S3.ConceptDynamics.Completion.CompletionInformationCost

/-- The readout-target law and the completion law are the same joint pushforward when given
the same source mass, readout, and target. The `Concept` parameter on the communication side
is definitionally the function type used on the completion side.

**What this does not claim.** This equality does not assert that an arbitrary real-valued
mass is normalized or nonnegative, hence it does not by itself make the common function a
probability law. It also does not identify the surrounding main theorems:
`translation_loss_monotone` compares a readout before and after postprocessing, whereas
`completion_information_cost` identifies an entropy increment for one fixed joint law. -/
theorem readoutTargetLaw_eq_completionLaw
    {X Readout Target : Type*} [Fintype X]
    (mass : X → Real) (readout : Concept X Readout)
    (target : Concept X Target) :
    readoutTargetLaw mass readout target =
      completionLaw mass readout target := by
  rfl

/-- Reverse probe for CAS-A1: the public function equality controls every joint-law value. -/
example
    {X Readout Target : Type*} [Fintype X]
    (mass : X → Real) (readout : Concept X Readout)
    (target : Concept X Target)
    (bridge : readoutTargetLaw mass readout target =
      completionLaw mass readout target)
    (value : Readout × Target) :
    readoutTargetLaw mass readout target value =
      completionLaw mass readout target value :=
  congrFun bridge value

#print axioms readoutTargetLaw_eq_completionLaw

end D5.S3.ConceptDynamics.Completion.ReadoutCompletionLawCompatibility
