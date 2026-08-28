/- GID: D5/S3/ConceptDynamics/InstitutionalCapture/InjectivePolicyCoalitionThreshold
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InstitutionalCapture/InjectivePolicyCoalitionThreshold
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: An injective secret policy has exactly the secret-recovery coalition threshold. -/

import D5.S3.ConceptDynamics.InstitutionalCapture.KnowledgePolicyThreshold

/- Library-search audit trail (2026-08-27):
   * Exact repository hits `coalitionReadout`, `coalitionSizeSet`,
     `minimumCoalitionSize`, and `recoverViaPolicy` are the canonical family
     primitives and are reused directly.
   * The frozen predecessor proves the threshold equality only with an
     unnecessary finite-participant instance and full-coalition recovery premise.
   * Repository searches for the same equality without those premises found no
     declaration. Pinned Mathlib's `Nat.sInf_eq_zero` handles the empty secret
     carrier; no exact threshold theorem matched the source. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.ConceptDynamics.InstitutionalCapture.InjectivePolicyCoalitionThreshold

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.InstitutionalCapture.KnowledgePolicyThreshold

/-- Preserving every distinction on the actual secret image makes policy
implementation and secret recovery have the same minimum coalition size. -/
theorem injective_policy_coalition_threshold
    {I X V B U : Type*} [DecidableEq I]
    (share : I -> X -> V) (secret : Concept X B) (policy : Concept X U)
    (policy_factor : exists policyMap : B -> U,
      policy = policyMap ∘ secret /\
        Set.InjOn policyMap (Set.range secret)) :
    minimumCoalitionSize (fun K =>
        Refines policy (coalitionReadout share K)) =
      minimumCoalitionSize (fun K =>
        Refines secret (coalitionReadout share K)) := by
  classical
  cases isEmpty_or_nonempty B with
  | inl emptyB =>
      letI : IsEmpty B := emptyB
      letI : IsEmpty X := ⟨fun x => isEmptyElim (secret x)⟩
      have hsecretSet :
          coalitionSizeSet (fun K => Refines secret (coalitionReadout share K)) = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro n
        rintro ⟨K, ⟨factor, _⟩, _⟩
        exact isEmptyElim (factor (fun _ => none))
      have hsecretMinimum :
          minimumCoalitionSize (fun K => Refines secret (coalitionReadout share K)) = 0 := by
        unfold minimumCoalitionSize
        rw [hsecretSet, Nat.sInf_empty]
      cases isEmpty_or_nonempty U with
      | inl emptyU =>
          letI : IsEmpty U := emptyU
          have hpolicySet :
              coalitionSizeSet (fun K => Refines policy (coalitionReadout share K)) = ∅ := by
            apply Set.eq_empty_iff_forall_notMem.mpr
            intro n
            rintro ⟨K, ⟨factor, _⟩, _⟩
            exact isEmptyElim (factor (fun _ => none))
          unfold minimumCoalitionSize
          rw [hpolicySet, hsecretSet]
      | inr nonemptyU =>
          letI : Nonempty U := nonemptyU
          have hzero :
              0 ∈ coalitionSizeSet
                (fun K => Refines policy (coalitionReadout share K)) := by
            refine ⟨∅, ?_, Finset.card_empty⟩
            refine ⟨fun _ => Classical.choice nonemptyU, ?_⟩
            funext x
            exact isEmptyElim x
          rw [hsecretMinimum]
          unfold minimumCoalitionSize
          exact Nat.sInf_eq_zero.mpr (Or.inl hzero)
  | inr nonemptyB =>
      letI : Nonempty B := nonemptyB
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
          calc
            secret = recoverViaPolicy secret policyMap hinjective ∘ policy := by
              funext x
              simp only [Function.comp_apply, hpolicy]
              exact (hrecover x).symm
            _ = recoverViaPolicy secret policyMap hinjective ∘
                  (factor ∘ coalitionReadout share K) := by rw [hfactor]
            _ = (recoverViaPolicy secret policyMap hinjective ∘ factor) ∘
                  coalitionReadout share K := by rfl
        · rintro ⟨factor, hfactor⟩
          refine ⟨policyMap ∘ factor, ?_⟩
          calc
            policy = policyMap ∘ secret := hpolicy
            _ = policyMap ∘ (factor ∘ coalitionReadout share K) := by rw [hfactor]
            _ = (policyMap ∘ factor) ∘ coalitionReadout share K := by rfl
      have hsizeSets :
          coalitionSizeSet (fun K => Refines policy (coalitionReadout share K)) =
            coalitionSizeSet (fun K => Refines secret (coalitionReadout share K)) := by
        ext n
        constructor
        · rintro ⟨K, hK, rfl⟩
          exact ⟨K, (hrefines K).mp hK, rfl⟩
        · rintro ⟨K, hK, rfl⟩
          exact ⟨K, (hrefines K).mpr hK, rfl⟩
      unfold minimumCoalitionSize
      rw [hsizeSets]

#print axioms injective_policy_coalition_threshold

end D5.S3.ConceptDynamics.InstitutionalCapture.InjectivePolicyCoalitionThreshold
