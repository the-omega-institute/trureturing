/- GID: D5/S3/ConceptDynamics/RefinementFactorization/InterventionFamilyKernelMonotonicity
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/RefinementFactorization/InterventionFamilyKernelMonotonicity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Enlarging an arbitrary intervention family shrinks its joint-law equality kernel. -/

import D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
import Mathlib.Data.Set.Basic
import Mathlib.Data.Setoid.Basic

/- Library-search audit trail (2026-08-25):
   * Exact current-tree hit `jointReadout` is the canonical dependent product
     readout and is imported rather than redeclared.
   * `indexed_readout_monotonicity` is an exact finite-family specialization,
     but its `Finset` carrier does not cover the source's arbitrary intervention
     families, so it cannot be bound to this atom.
   * Repository searches for arbitrary set-indexed readout restriction and
     kernel inclusion found no theorem on the source carrier.
   * Pinned Mathlib searches found no packaged `Setoid.ker` restriction law;
     dependent function evaluation supplies the direct proof below.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.RefinementFactorization.InterventionFamilyKernelMonotonicity

open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion

universe u v w

/-- If one allowed intervention family is contained in another, equality of
the larger joint law profile implies equality of the smaller profile. Thus
allowing more interventions can only shrink or preserve the causal residual. -/
theorem intervention_family_kernel_monotonicity
    {Intervention : Type u} {Model : Type v} {Law : Type w}
    (law : Intervention -> Model -> Law)
    {familyA familyB : Set Intervention} (included : familyA ⊆ familyB) :
    Setoid.ker (jointReadout (fun intervention : familyB => law intervention.1)) <=
      Setoid.ker
        (jointReadout (fun intervention : familyA => law intervention.1)) := by
  intro model₁ model₂ sameLargerProfile
  change
    (fun intervention : familyA => law intervention.1 model₁) =
      fun intervention : familyA => law intervention.1 model₂
  funext intervention
  exact congrFun sameLargerProfile ⟨intervention.1, included intervention.2⟩

#print axioms intervention_family_kernel_monotonicity

end D5.S3.ConceptDynamics.RefinementFactorization.InterventionFamilyKernelMonotonicity
