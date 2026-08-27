/- GID: D5/S3/Entropy/Forgetting/ConditionalInformationForgetting
   generality: G
   mirror-B: D5/B/S3/Entropy/Forgetting/ConditionalInformationForgetting
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Deterministic forgetting of future records cannot increase conditional information. -/

import D5.S3.ConceptDynamics.Communication.TranslationLossMonotonicity
import D5.S3.Entropy.Submodularity.ConditionalMutualInformation

/- Library-search audit trail (2026-08-27):
   * Exact family hits pushforward, readoutTargetLaw, targetResidualEntropy, xyProjection,
     xzProjection, and conditionalMutualInformation are imported rather than redeclared.
   * Exact frozen hit translation_loss_monotone supplies deterministic postprocessing of the
     paired environment-future readout and is applied directly.
   * Repository and pinned-Mathlib searches found no theorem directly stating conditional
     mutual-information contraction for the finite real-valued joint laws used here. -/

noncomputable section

namespace D5.S3.Entropy.Forgetting.ConditionalInformationForgetting

open D5.S3.ConceptDynamics.Communication.TranslationLossMonotonicity
open D5.S3.Divergence.ChainRule
open D5.S3.Entropy.ConditionalEntropy
open D5.S3.Entropy.Forgetting.CapacityMonotone
open D5.S3.Entropy.MaxEntropy
open D5.S3.Entropy.Submodularity.ConditionalMutualInformation
open D5.S3.Entropy.Submodularity.StrongSubadditivity

set_option autoImplicit false
set_option relaxedAutoImplicit false

private theorem pushforward_nonnegative
    {Sample Value : Type*} [Fintype Sample]
    (mass : Sample -> Real) (readout : Sample -> Value)
    (hmass : forall sample, 0 <= mass sample) :
    forall value, 0 <= pushforward readout mass value := by
  classical
  intro value
  simp only [pushforward]
  exact Finset.sum_nonneg fun sample _ => by
    by_cases hreadout : readout sample = value <;> simp [hreadout, hmass sample]

private theorem readout_target_marginal
    {Sample Readout Target : Type*}
    [Fintype Sample] [Fintype Target]
    (mass : Sample -> Real) (readout : Sample -> Readout)
    (target : Sample -> Target) :
    marginal (readoutTargetLaw mass readout target) =
      pushforward readout mass := by
  classical
  funext readoutValue
  simp only [marginal, readoutTargetLaw, pushforward]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro sample _
  by_cases hreadout : readout sample = readoutValue
  · rw [Finset.sum_eq_single (target sample)]
    · simp [hreadout]
    · intro targetValue _ htarget
      simp [hreadout, Ne.symm htarget]
    · simp
  · simp [hreadout]

private theorem target_residual_entropy_eq_entropy_sub_readout
    {Sample Readout Target : Type*}
    [Fintype Sample] [Fintype Readout] [Fintype Target]
    (mass : Sample -> Real) (readout : Sample -> Readout)
    (target : Sample -> Target) (hmass : forall sample, 0 <= mass sample) :
    targetResidualEntropy mass readout target =
      shannonEntropy (readoutTargetLaw mass readout target) -
        shannonEntropy (pushforward readout mass) := by
  have hchain := entropy_chain_rule
    (readoutTargetLaw mass readout target)
    (pushforward_nonnegative mass (fun sample =>
      (readout sample, target sample)) hmass)
  rw [readout_target_marginal mass readout target] at hchain
  unfold targetResidualEntropy
  linarith

private theorem xy_projection_joint_law
    {Sample Environment Commitment Future : Type*}
    [Fintype Sample] [Fintype Future]
    (mass : Sample -> Real) (environment : Sample -> Environment)
    (commitment : Sample -> Commitment) (future : Sample -> Future) :
    xyProjection
        (pushforward (fun sample =>
          (environment sample, (commitment sample, future sample))) mass) =
      readoutTargetLaw mass environment commitment := by
  classical
  funext value
  simp only [xyProjection, readoutTargetLaw, pushforward]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro sample _
  by_cases henvironment : environment sample = value.1
  · by_cases hcommitment : commitment sample = value.2
    · rw [Finset.sum_eq_single (future sample)]
      · simp_all
      · intro futureValue _ hdifferent
        have hfuture : future sample ≠ futureValue := Ne.symm hdifferent
        simp_all [Prod.ext_iff]
      · simp
    · simp_all [Prod.ext_iff]
  · simp_all [Prod.ext_iff]

private theorem xz_projection_joint_law
    {Sample Environment Commitment Future : Type*}
    [Fintype Sample] [Fintype Commitment]
    (mass : Sample -> Real) (environment : Sample -> Environment)
    (commitment : Sample -> Commitment) (future : Sample -> Future) :
    xzProjection
        (pushforward (fun sample =>
          (environment sample, (commitment sample, future sample))) mass) =
      pushforward (fun sample => (environment sample, future sample)) mass := by
  classical
  funext value
  simp only [xzProjection, pushforward]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro sample _
  by_cases henvironment : environment sample = value.1
  · by_cases hfuture : future sample = value.2
    · rw [Finset.sum_eq_single (commitment sample)]
      · simp_all
      · intro commitmentValue _ hdifferent
        have hcommitment : commitment sample ≠ commitmentValue :=
          Ne.symm hdifferent
        simp_all [Prod.ext_iff]
      · simp
    · simp_all [Prod.ext_iff]
  · simp_all [Prod.ext_iff]

private theorem marginal_xy_projection
    {Environment Commitment Future : Type*}
    [Fintype Commitment] [Fintype Future]
    (law : Environment × (Commitment × Future) -> Real) :
    marginal (xyProjection law) = marginal law := by
  classical
  funext environmentValue
  simp only [marginal, xyProjection, Fintype.sum_prod_type]

private theorem marginal_joint_law
    {Sample Environment Commitment Future : Type*}
    [Fintype Sample] [Fintype Commitment] [Fintype Future]
    (mass : Sample -> Real) (environment : Sample -> Environment)
    (commitment : Sample -> Commitment) (future : Sample -> Future) :
    marginal
        (pushforward (fun sample =>
          (environment sample, (commitment sample, future sample))) mass) =
      pushforward environment mass := by
  rw [← marginal_xy_projection,
    xy_projection_joint_law mass environment commitment future,
    readout_target_marginal mass environment commitment]

private theorem reordered_joint_entropy
    {Sample Environment Commitment Future : Type*}
    [Fintype Sample] [Fintype Environment] [Fintype Commitment] [Fintype Future]
    (mass : Sample -> Real) (environment : Sample -> Environment)
    (commitment : Sample -> Commitment) (future : Sample -> Future) :
    shannonEntropy
        (readoutTargetLaw mass
          (fun sample => (environment sample, future sample)) commitment) =
      shannonEntropy
        (pushforward (fun sample =>
          (environment sample, (commitment sample, future sample))) mass) := by
  classical
  let reorder : ((Environment × Future) × Commitment) ≃
      Environment × (Commitment × Future) :=
    (Equiv.prodAssoc Environment Future Commitment).trans
      (Equiv.prodCongr (Equiv.refl Environment)
        (Equiv.prodComm Future Commitment))
  have hlaw :
      readoutTargetLaw mass
          (fun sample => (environment sample, future sample)) commitment =
        fun value =>
          pushforward (fun sample =>
            (environment sample, (commitment sample, future sample))) mass
            (reorder value) := by
    funext value
    simp only [readoutTargetLaw, pushforward, reorder, Equiv.trans_apply,
      Equiv.prodAssoc_apply, Equiv.prodCongr_apply, Prod.ext_iff]
    apply Finset.sum_congr rfl
    intro sample _
    by_cases henvironment : environment sample = value.1.1 <;>
      by_cases hfuture : future sample = value.1.2 <;>
        by_cases hcommitment : commitment sample = value.2 <;>
          simp [henvironment, hfuture, hcommitment]
  rw [hlaw, shannonEntropy]
  exact Fintype.sum_equiv reorder _ _ (fun _ => rfl)

private theorem conditional_information_eq_residual_difference
    {Sample Environment Commitment Future : Type*}
    [Fintype Sample] [Fintype Environment] [Fintype Commitment] [Fintype Future]
    (mass : Sample -> Real) (environment : Sample -> Environment)
    (commitment : Sample -> Commitment) (future : Sample -> Future)
    (hmass : forall sample, 0 <= mass sample) :
    conditionalMutualInformation
        (pushforward (fun sample =>
          (environment sample, (commitment sample, future sample))) mass) =
      targetResidualEntropy mass environment commitment -
        targetResidualEntropy mass
          (fun sample => (environment sample, future sample)) commitment := by
  let jointLaw :=
    pushforward (fun sample =>
      (environment sample, (commitment sample, future sample))) mass
  have hinformation := conditional_mutual_information_eq_entropy_defect jointLaw
    (pushforward_nonnegative mass (fun sample =>
      (environment sample, (commitment sample, future sample))) hmass)
  rw [xy_projection_joint_law mass environment commitment future,
    xz_projection_joint_law mass environment commitment future,
    marginal_joint_law mass environment commitment future] at hinformation
  have henvironment := target_residual_entropy_eq_entropy_sub_readout
    mass environment commitment hmass
  have hfuture := target_residual_entropy_eq_entropy_sub_readout mass
    (fun sample => (environment sample, future sample)) commitment hmass
  rw [reordered_joint_entropy mass environment commitment future] at hfuture
  dsimp only [jointLaw] at hinformation
  linarith

/-- Deterministically forgetting or coarse-graining the future behavior record cannot increase
the conditional mutual information carried from the current commitment to that record, given
the environment history. -/
theorem conditional_information_forgetting
    {Sample Environment Commitment Future Coarse : Type*}
    [Fintype Sample] [Fintype Environment] [Fintype Commitment]
    [Fintype Future] [Fintype Coarse]
    (mass : Sample -> Real)
    (hmass : (forall sample, 0 <= mass sample) /\ ∑ sample, mass sample = 1)
    (environment : Sample -> Environment)
    (commitment : Sample -> Commitment) (future : Sample -> Future)
    (forget : Future -> Coarse) :
    conditionalMutualInformation
        (pushforward (fun sample =>
          (environment sample, (commitment sample, forget (future sample)))) mass) <=
      conditionalMutualInformation
        (pushforward (fun sample =>
          (environment sample, (commitment sample, future sample))) mass) := by
  have hresidual :=
    (translation_loss_monotone mass hmass
      (fun sample => (environment sample, future sample))
      (fun value => (value.1, forget value.2)) commitment).2
  have hcoarse := conditional_information_eq_residual_difference mass
    environment commitment (fun sample => forget (future sample)) hmass.1
  have hfine := conditional_information_eq_residual_difference mass
    environment commitment future hmass.1
  change targetResidualEntropy mass
      (fun sample => (environment sample, future sample)) commitment <=
    targetResidualEntropy mass
      (fun sample => (environment sample, forget (future sample))) commitment at hresidual
  linarith

#print axioms conditional_information_forgetting

end D5.S3.Entropy.Forgetting.ConditionalInformationForgetting
