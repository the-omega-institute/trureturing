/- GID: D5/S3/ConceptDynamics/Policy/StrictPolicyPowerGrowth
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Policy/StrictPolicyPowerGrowth
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A finer readout separating one coarse fiber strictly adds a differentiating policy. -/

import D5.S3.ConceptDynamics.PolicyCapabilityMonotonicity

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'strict_policy_power_growth' D5 Golden/Frozen/accepted` found no
     existing declaration.
   * The repository policy/capability search found
     `PolicyCapabilityMonotonicity.policyCapability`, reused here as the common
     definition of policies implementable from a concept readout.
   * `StrictRefinementCapability.strict_refinement_capability` is adjacent but
     requires both readouts to be surjective and a global strict refinement.
     The present theorem assumes only one explicit coarse-equal, fine-distinct
     pair, which does not imply those hypotheses, so that theorem cannot be
     applied here.
   * The pinned-Mathlib search found only the basic range membership and
     function-composition machinery used by `policyCapability`; no theorem
     packages the separating-policy construction and coarse impossibility. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Policy.StrictPolicyPowerGrowth

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.PolicyCapabilityMonotonicity

/-- A state policy distinguishes two states when it selects different actions. -/
def distinguishesAt {X U : Type*} (policy : X -> U) (x y : X) : Prop :=
  policy x ≠ policy y

/-- If a finer readout separates two states in one coarse fiber and two actions
are available, its policy capability contains a policy outside the coarse
capability that distinguishes those states, while every coarse policy treats
them alike. -/
theorem strict_policy_power_growth
    {X C D U : Type*} (q_C : Concept X C) (q_D : Concept X D) (x y : X)
    (sameCoarse : q_C x = q_C y) (differentFine : q_D x ≠ q_D y)
    (distinctActions : ∃ u₀ u₁ : U, u₀ ≠ u₁) :
    (∃ policy : X -> U,
      policy ∈ policyCapability q_D U ∧
        policy ∉ policyCapability q_C U ∧ distinguishesAt policy x y) ∧
      ∀ policy : X -> U,
        policy ∈ policyCapability q_C U → ¬distinguishesAt policy x y := by
  classical
  obtain ⟨u₀, u₁, actionsDifferent⟩ := distinctActions
  let action_D : D -> U := fun coordinate =>
    if coordinate = q_D x then u₀ else u₁
  let policy : X -> U := action_D ∘ q_D
  have policySeparates : distinguishesAt policy x y := by
    change action_D (q_D x) ≠ action_D (q_D y)
    change (if q_D x = q_D x then u₀ else u₁) ≠
      (if q_D y = q_D x then u₀ else u₁)
    rw [if_pos rfl, if_neg differentFine.symm]
    exact actionsDifferent
  have coarseCannotSeparate :
      ∀ coarsePolicy : X -> U,
        coarsePolicy ∈ policyCapability q_C U →
          ¬distinguishesAt coarsePolicy x y := by
    intro coarsePolicy coarseMembership
    obtain ⟨action_C, rfl⟩ := coarseMembership
    intro separates
    apply separates
    change action_C (q_C x) = action_C (q_C y)
    exact congrArg action_C sameCoarse
  refine ⟨⟨policy, ?_, ?_, policySeparates⟩, coarseCannotSeparate⟩
  · exact ⟨action_D, rfl⟩
  · intro coarseMembership
    exact coarseCannotSeparate policy coarseMembership policySeparates

/-- A constant coarse readout and the Boolean identity readout exhibit strict
policy-power growth between `false` and `true`. -/
example :
    (∃ policy : Bool -> Bool,
      policy ∈ policyCapability (fun state : Bool => state) Bool ∧
        policy ∉ policyCapability (fun _ : Bool => ()) Bool ∧
          distinguishesAt policy false true) ∧
      ∀ policy : Bool -> Bool,
        policy ∈ policyCapability (fun _ : Bool => ()) Bool →
          ¬distinguishesAt policy false true := by
  exact strict_policy_power_growth
    (fun _ : Bool => ()) (fun state : Bool => state) false true rfl
    Bool.false_ne_true ⟨false, true, Bool.false_ne_true⟩

#print axioms strict_policy_power_growth

end D5.S3.ConceptDynamics.Policy.StrictPolicyPowerGrowth
