/- GID: D5/S3/ConceptDynamics/SufficiencyQuotient/TaskIdentityGlobalIdentityCriterion
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/SufficiencyQuotient/TaskIdentityGlobalIdentityCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The target quotient is global identity exactly for jointly faithful targets. -/

import D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
import Mathlib.Data.Setoid.Basic

/- Library-search audit trail (2026-08-26):
   * Body-shape search for `fun x i => q i x` found the canonical repository
     primitive `jointReadout`, which is imported rather than redeclared.
   * The adjacent `TargetFamilyMinimalQuotient` constructs the same canonical
     kernel quotient, but it does not state when that quotient is global identity.
   * Pinned Mathlib exact hits `Setoid.injective_iff_ker_bot`, `Quotient.exact`,
     and `Quotient.sound` supply the kernel and quotient equivalences directly.
   * The imported constant-family theorem supplies the nonfaithful countermodel.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.SufficiencyQuotient.TaskIdentityGlobalIdentityCriterion

open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion

universe u v w

/-- The canonical target-profile quotient identifies exactly the states that no
target distinguishes. It is injective, and hence agrees with global identity,
exactly when the target family is jointly faithful. A constant target family
exhibits the strict task/global identity separation. -/
theorem task_identity_global_identity_criterion :
    (forall (I : Type u) (X : Type v) (Y : I -> Type w)
      (targets : forall index, X -> Y index),
      let profile := jointReadout targets
      let taskIdentity : X -> Quotient (Setoid.ker profile) :=
        fun state => Quotient.mk (Setoid.ker profile) state
      (forall left right,
        taskIdentity left = taskIdentity right <->
          forall index, targets index left = targets index right) /\
        (Function.Injective profile <-> Setoid.ker profile = ⊥) /\
        (Function.Injective taskIdentity <-> Function.Injective profile)) /\
      (exists targets : forall _ : Unit, Bool -> Unit,
        let profile := jointReadout targets
        let taskIdentity : Bool -> Quotient (Setoid.ker profile) :=
          fun state => Quotient.mk (Setoid.ker profile) state
        exists left right,
          Not (left = right) /\
            (forall index, targets index left = targets index right) /\
            taskIdentity left = taskIdentity right) := by
  constructor
  · intro I X Y targets
    dsimp only
    let profile := jointReadout targets
    let taskIdentity : X -> Quotient (Setoid.ker profile) :=
      fun state => Quotient.mk (Setoid.ker profile) state
    constructor
    · intro left right
      constructor
      · intro sameIdentity index
        exact congrFun (Quotient.exact sameIdentity) index
      · intro sameTargets
        apply Quotient.sound
        funext index
        exact sameTargets index
    constructor
    · exact Setoid.injective_iff_ker_bot profile
    · constructor
      · intro taskInjective left right sameProfile
        apply taskInjective
        exact Quotient.sound sameProfile
      · intro profileInjective left right sameIdentity
        apply profileInjective
        exact Quotient.exact sameIdentity
  · obtain ⟨targets, ⟨left, right, different, sameTargets⟩, _, _, _⟩ :=
      constant_concept_family_not_jointly_faithful
    refine ⟨targets, ?_⟩
    dsimp only
    refine ⟨left, right, different, sameTargets, ?_⟩
    apply Quotient.sound
    funext index
    exact sameTargets index

#print axioms task_identity_global_identity_criterion

end D5.S3.ConceptDynamics.SufficiencyQuotient.TaskIdentityGlobalIdentityCriterion
