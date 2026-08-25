/- GID: D5/S3/ConceptDynamics/PolicyCapabilityMonotonicity
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/PolicyCapabilityMonotonicity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Refining a readout can only enlarge the set of policies implemented through it. -/

import D5.S3.ConceptDynamics.ConceptJoinUniversal
import Mathlib.Data.Set.Image

/- Library-search audit trail (2026-08-21):
   * Searches for policy-capability monotonicity and implementable policies in
     `D5` and the active frozen ledger found no declaration of this theorem.
   * The source contains the same mathematical statement earlier as theorem
     220.1, but no Lean deposit or accepted declaration covers either occurrence.
   * Exact repository hit `ConceptJoinUniversal.Refines` is the source's
     factor-map refinement relation and is reused directly.
   * Exact pinned-Mathlib hit `Set.range_comp_subset_range` states that the
     range of a composite is contained in the range of its outer map; it is
     applied directly to policy simulation below. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.PolicyCapabilityMonotonicity

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal

/-- Policies implementable through a readout are exactly the actions obtained
by postcomposing that readout with a decision rule on its concept values. -/
def policyCapability {X C : Type _} (readout : Concept X C) (U : Type _) :
    Set (X -> U) :=
  Set.range fun policy : C -> U => policy ∘ readout

/-- If `D` refines `C`, every policy based on `C` is implemented from `D` by
first recovering the `C`-value and then applying the original decision rule. -/
theorem policy_capability_monotone
    {X C D U : Type _} (q_C : Concept X C) (q_D : Concept X D)
    (refinement : Refines q_C q_D) :
    policyCapability q_C U ⊆ policyCapability q_D U := by
  rcases refinement with ⟨factor, hfactor⟩
  rintro _ ⟨policy, rfl⟩
  refine ⟨policy ∘ factor, ?_⟩
  rw [hfactor]
  unfold Function.comp
  rfl

/-- The public state domain is inhabited. -/
example : Bool := false

/-- A constant coarse readout factors through the identity fine readout, so the
public refinement premise is simultaneously satisfiable. -/
example : Refines (fun _ : Bool => false) (fun x : Bool => x) :=
  ⟨fun _ => false, by funext x; rfl⟩

/-- Without the refinement direction, policy-capability inclusion can fail:
the identity action is unavailable through a constant Boolean readout. -/
example :
    (fun x : Bool => x) ∈ policyCapability (fun x : Bool => x) Bool ∧
      (fun x : Bool => x) ∉ policyCapability (fun _ : Bool => false) Bool := by
  constructor
  · exact ⟨id, rfl⟩
  · rintro ⟨policy, hpolicy⟩
    have hfalse := congrFun hpolicy false
    have htrue := congrFun hpolicy true
    simp only [Function.comp_apply] at hfalse htrue
    exact Bool.false_ne_true (hfalse.symm.trans htrue)

#print axioms policy_capability_monotone

end D5.S3.ConceptDynamics.PolicyCapabilityMonotonicity
