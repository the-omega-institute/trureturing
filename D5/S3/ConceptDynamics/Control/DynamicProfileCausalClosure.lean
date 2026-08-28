/- GID: D5/S3/ConceptDynamics/Control/DynamicProfileCausalClosure
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Control/DynamicProfileCausalClosure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Complete control profiles carry interventions by right-shifting action indices. -/

import D5.S3.ConceptDynamics.Control.ControlQuotientUniversalMinimality

/- Library-search audit trail (2026-08-27):
   * Current-tree searches for causal closure, dynamic closure, profile shifts,
     and monoid-indexed readouts found the canonical `controlProfile`, which is
     imported and used directly.
   * `dynamic_closure_is_intervention_closed` proves list-trace fiber closure,
     while `control_quotient_universal_minimality` exposes the induced quotient
     action. Neither public statement gives the profile-level right-shift map.
   * Pinned Mathlib supplies the exact action law `mul_smul`; it is applied to
     identify the continuation coordinate after one intervention. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Control.DynamicProfileCausalClosure

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.Control.ControlQuotientUniversalMinimality

/-- The complete action profile after applying `action` is obtained by
right-multiplying every continuation index by `action`. This equation both
exhibits the descended macroscopic update and gives its computation rule. -/
theorem dynamic_profile_causal_closure
    {M X O : Type*} [Monoid M] [MulAction M X]
    (readout : Concept X O) :
    forall action : M,
      controlProfile readout ∘ (fun state => action • state) =
        (fun profile continuation => profile (continuation * action)) ∘
          controlProfile readout := by
  intro action
  funext state continuation
  exact congrArg readout (mul_smul continuation action state).symm

#print axioms dynamic_profile_causal_closure

end D5.S3.ConceptDynamics.Control.DynamicProfileCausalClosure
