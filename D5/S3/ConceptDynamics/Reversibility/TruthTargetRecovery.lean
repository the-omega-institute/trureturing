/- GID: D5/S3/ConceptDynamics/Reversibility/TruthTargetRecovery
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Reversibility/TruthTargetRecovery
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A supplied left inverse recovers each Boolean truth target of the original state. -/

import D5.S3.ConceptDynamics.Reversibility.LeftInvertibleRecoversAllTargets

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Reversibility.TruthTargetRecovery

open D5.S3.ConceptDynamics.Reversibility.LeftInvertibleRecoversAllTargets

/-- Boolean-target specialization of the existing all-target recovery theorem.
Recovery concerns the original state's target, not invariance under state evolution
or access by a restricted observer. -/
theorem truth_target_recovers {X B : Type*} (U : X → B) (R : B → X)
    (hleft : Function.LeftInverse R U) (truth : X → Bool) :
    truth = (truth ∘ R) ∘ U :=
  ((left_invertible_recovers_all_targets U R hleft).1 truth).1

#print axioms truth_target_recovers

end D5.S3.ConceptDynamics.Reversibility.TruthTargetRecovery
