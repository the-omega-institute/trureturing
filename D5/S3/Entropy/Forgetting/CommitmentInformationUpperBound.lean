/- GID: D5/S3/Entropy/Forgetting/CommitmentInformationUpperBound
   generality: G
   mirror-B: D5/B/S3/Entropy/Forgetting/CommitmentInformationUpperBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Conditional commitment information is bounded by commitment entropy given environment. -/

import D5.S3.Entropy.ConditionalEntropyEquality
import D5.S3.Entropy.Forgetting.CommitmentInformationSaturation

/- Library-search audit trail (2026-08-27):
   * Exact family primitives `pushforward`, `targetResidualEntropy`, and
     `conditionalMutualInformation` are imported rather than redeclared.
   * Exact frozen component hits `conditional_information_forgetting` and
     `commitment_information_saturation` are applied directly. No frozen theorem
     states their upper-bound consequence for the actual future record.
   * Pinned Mathlib has no theorem on the repository's finite real-valued
     conditional-information carrier. The deterministic recovery step uses the
     exact repository hit `conditional_entropy_eq_zero_of_point_mass_on_support`. -/

noncomputable section

namespace D5.S3.Entropy.Forgetting.CommitmentInformationUpperBound

open D5.S3.ConceptDynamics.Communication.TranslationLossMonotonicity
open D5.S3.Divergence.ChainRule
open D5.S3.Entropy.ConditionalEntropy
open D5.S3.Entropy.ConditionalEntropyEquality
open D5.S3.Entropy.Forgetting.CapacityMonotone
open D5.S3.Entropy.Forgetting.CommitmentInformationSaturation
open D5.S3.Entropy.Forgetting.ConditionalInformationForgetting
open D5.S3.Entropy.Submodularity.ConditionalMutualInformation

set_option autoImplicit false
set_option relaxedAutoImplicit false

private theorem enriched_record_residual_entropy_zero
    {Sample Environment Commitment Future : Type*}
    [Fintype Sample] [Fintype Environment] [Fintype Commitment]
    [Fintype Future]
    (mass : Sample -> Real) (environment : Sample -> Environment)
    (commitment : Sample -> Commitment) (future : Sample -> Future) :
    targetResidualEntropy mass
        (fun sample =>
          (environment sample, (commitment sample, future sample)))
        commitment = 0 := by
  classical
  let key : Sample -> Environment × (Commitment × Future) := fun sample =>
    (environment sample, (commitment sample, future sample))
  let joint : (Environment × (Commitment × Future)) × Commitment -> Real :=
    readoutTargetLaw mass key commitment
  change conditionalEntropy joint = 0
  apply conditional_entropy_eq_zero_of_point_mass_on_support joint
  intro observed hmarginal
  have hmarginal_eq : marginal joint = pushforward key mass := by
    funext value
    simp only [joint, readoutTargetLaw, marginal, pushforward]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro sample _
    by_cases hkey : key sample = value
    · simp [hkey]
    · simp [hkey]
  have hexists : exists sample, key sample = observed := by
    by_contra hnone
    push Not at hnone
    apply hmarginal
    rw [hmarginal_eq]
    simp only [pushforward]
    apply Finset.sum_eq_zero
    intro sample _
    simp [hnone sample]
  obtain ⟨sample0, hsample0⟩ := hexists
  refine ⟨commitment sample0, ?_⟩
  funext value
  rw [conditional]
  by_cases hvalue : value = commitment sample0
  · subst value
    have hcell :
        joint (observed, commitment sample0) = marginal joint observed := by
      rw [hmarginal_eq]
      simp only [joint, readoutTargetLaw, pushforward]
      apply Finset.sum_congr rfl
      intro sample _
      by_cases hkey : key sample = observed
      · have hcommitment : commitment sample = commitment sample0 :=
          congrArg (fun value : Environment × (Commitment × Future) =>
            value.2.1) (hkey.trans hsample0.symm)
        simp [hkey, hcommitment]
      · simp [hkey]
    simp [hcell, hmarginal]
  · have hcell : joint (observed, value) = 0 := by
      simp only [joint, readoutTargetLaw, pushforward]
      apply Finset.sum_eq_zero
      intro sample _
      by_cases hkey : key sample = observed
      · have hcommitment : commitment sample = commitment sample0 :=
          congrArg (fun item : Environment × (Commitment × Future) =>
            item.2.1) (hkey.trans hsample0.symm)
        simp [hkey, hcommitment, Ne.symm hvalue]
      · simp [hkey]
    simp [hcell, hvalue]

/-- The conditional information transmitted from a current commitment to a
future behavior record cannot exceed the commitment entropy remaining after
conditioning on the environment record. -/
theorem commitment_information_le_residual_entropy
    {Sample Environment Commitment Future : Type*}
    [Fintype Sample] [Fintype Environment] [Fintype Commitment]
    [Fintype Future]
    (mass : Sample -> Real)
    (hmass : (forall sample, 0 <= mass sample) /\ ∑ sample, mass sample = 1)
    (environment : Sample -> Environment)
    (commitment : Sample -> Commitment) (future : Sample -> Future) :
    conditionalMutualInformation
        (pushforward (fun sample =>
          (environment sample, (commitment sample, future sample))) mass) <=
      targetResidualEntropy mass environment commitment := by
  let enrichedFuture : Sample -> Commitment × Future := fun sample =>
    (commitment sample, future sample)
  have hforgetting := conditional_information_forgetting mass hmass
    environment commitment enrichedFuture (fun value => value.2)
  have hsaturation := commitment_information_saturation mass hmass.1
    environment commitment enrichedFuture (by
      simpa only [enrichedFuture] using
        enriched_record_residual_entropy_zero
          mass environment commitment future)
  calc
    conditionalMutualInformation
          (pushforward (fun sample =>
            (environment sample, (commitment sample, future sample))) mass) <=
        conditionalMutualInformation
          (pushforward (fun sample =>
            (environment sample,
              (commitment sample, enrichedFuture sample))) mass) := by
      simpa only [enrichedFuture] using hforgetting
    _ = targetResidualEntropy mass environment commitment := hsaturation

#print axioms commitment_information_le_residual_entropy

end D5.S3.Entropy.Forgetting.CommitmentInformationUpperBound
