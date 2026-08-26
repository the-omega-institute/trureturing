/- GID: D5/S3/ConceptDynamics/InstitutionalCapture/KnowledgePolicyThreshold
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InstitutionalCapture/KnowledgePolicyThreshold
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Secret recovery and injective secret policies have the same coalition-size threshold. -/

import D5.S3.ConceptDynamics.ConceptJoinUniversal
import Mathlib.Data.Finset.Card
import Mathlib.Order.Lattice.Nat

/- Library-search audit trail (2026-08-21):
   * `ConceptJoinUniversal.Refines` and `ConceptFiberDecomposition.Concept` are
     exact repository hits for source factorization and readout carriers; they
     are imported and used directly.
   * No accepted declaration packages a finite-coalition threshold or the
     secret-image inverse construction. Searches for coalition, threshold,
     secret-sharing, and policy factorization found no exact theorem.
   * Pinned Mathlib hits `Nat.sInf`, `Nat.sInf_def`, `Set.InjOn`, and
     `Function.comp`; no stronger threshold theorem matched the source.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InstitutionalCapture.KnowledgePolicyThreshold

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal

/- A coalition sees exactly the shares whose participant labels lie in the
coalition; absent labels carry `none`, so the carrier is independent of K. -/
def coalitionReadout {I X V : Type*} [DecidableEq I]
    (share : I → X → V) (K : Finset I) : Concept X (I → Option V) :=
  fun x i => if i ∈ K then some (share i x) else none

/- The source's minimum coalition size is the natural infimum of the sizes of
coalitions satisfying a public factorization predicate. -/
def coalitionSizeSet {I : Type*} (property : Finset I → Prop) : Set Nat :=
  {n | ∃ K, property K ∧ K.card = n}

noncomputable def minimumCoalitionSize {I : Type*} (property : Finset I → Prop) : Nat :=
  sInf (coalitionSizeSet property)

noncomputable def recoverViaPolicy {X B U : Type*} [Nonempty B]
    (secret : Concept X B) (policyMap : B → U)
    (injectiveOnSecret : Set.InjOn policyMap (Set.range secret)) : U → B := by
  classical
  exact fun u =>
    if hu : ∃ b, b ∈ Set.range secret ∧ policyMap b = u then
      Classical.choose hu
    else
      Classical.choice (inferInstance : Nonempty B)

theorem knowledge_policy_threshold_consistent
    {I X V B U : Type*} [Fintype I] [DecidableEq I] [Nonempty B]
    (share : I → X → V) (secret : Concept X B) (policy : Concept X U)
    (policy_factor : ∃ policyMap : B → U,
      policy = policyMap ∘ secret ∧
        Set.InjOn policyMap (Set.range secret))
    (full_recovery :
      Refines secret (coalitionReadout share (Finset.univ : Finset I))) :
    minimumCoalitionSize (fun K =>
        Refines policy (coalitionReadout share K)) =
      minimumCoalitionSize (fun K =>
        Refines secret (coalitionReadout share K)) := by
  rcases policy_factor with ⟨policyMap, hpolicy, hinjective⟩
  have hrecover (x : X) :
      recoverViaPolicy secret policyMap hinjective (policyMap (secret x)) = secret x := by
    unfold recoverViaPolicy
    split
    · next hu =>
        have hchosen := Classical.choose_spec hu
        apply hinjective hchosen.1 ⟨x, rfl⟩
        exact hchosen.2
    · next hu =>
        exact False.elim (hu ⟨secret x, ⟨x, rfl⟩, rfl⟩)
  have hrefines (K : Finset I) :
      Refines policy (coalitionReadout share K) ↔
        Refines secret (coalitionReadout share K) := by
    constructor
    · rintro ⟨factor, hfactor⟩
      refine ⟨recoverViaPolicy secret policyMap hinjective ∘ factor, ?_⟩
      funext x
      have hpolicyPoint := congrFun hpolicy x
      have hfactorPoint := congrFun hfactor x
      unfold Function.comp at hpolicyPoint hfactorPoint ⊢
      calc
        secret x = recoverViaPolicy secret policyMap hinjective (policy x) := by
          simp only [hpolicy]
          exact (hrecover x).symm
        _ = recoverViaPolicy secret policyMap hinjective
            (factor (coalitionReadout share K x)) :=
          congrArg (recoverViaPolicy secret policyMap hinjective) hfactorPoint
    · rintro ⟨factor, hfactor⟩
      refine ⟨policyMap ∘ factor, ?_⟩
      funext x
      have hpolicyPoint := congrFun hpolicy x
      have hfactorPoint := congrFun hfactor x
      unfold Function.comp at hpolicyPoint hfactorPoint ⊢
      exact hpolicyPoint.trans (congrArg policyMap hfactorPoint)
  have hsize_sets :
      coalitionSizeSet (fun K => Refines policy (coalitionReadout share K)) =
        coalitionSizeSet (fun K => Refines secret (coalitionReadout share K)) := by
    ext n
    constructor
    · rintro ⟨K, hK, rfl⟩
      exact ⟨K, (hrefines K).mp hK, rfl⟩
    · rintro ⟨K, hK, rfl⟩
      exact ⟨K, (hrefines K).mpr hK, rfl⟩
  have _full_policy :
      Refines policy (coalitionReadout share (Finset.univ : Finset I)) :=
    (hrefines (Finset.univ : Finset I)).mpr full_recovery
  unfold minimumCoalitionSize
  rw [hsize_sets]

example : ∃ K : Finset Bool, K.card = 2 := by
  exact ⟨{false, true}, by decide⟩

#print axioms knowledge_policy_threshold_consistent

end D5.S3.ConceptDynamics.InstitutionalCapture.KnowledgePolicyThreshold
