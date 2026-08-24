/- GID: D5/S3/Entropy/Submodularity/SelectedObservationInformationMonotonicity
   generality: G
   mirror-B: D5/B/S3/Entropy/Submodularity/SelectedObservationInformationMonotonicity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Mutual information from selected finite experiments is monotone under inclusion. -/

import D5.S3.ConceptDynamics.Communication.TranslationLossMonotonicity
import Mathlib.Data.Fintype.Pi

/- Library-search audit trail (2026-08-25):
   * Pinned Mathlib searches for finite mutual information, deterministic
     postprocessing, and selected experiment families found no real-valued
     finite mutual-information monotonicity theorem. Its conditional-
     independence API is measure-theoretic rather than this finite carrier.
   * Repository searches found no selected-output joint-law constructor or
     Finset-indexed mutual-information monotonicity theorem.
   * Exact hits `readoutTargetLaw`, `targetResidualEntropy`, and `pushforward`
     construct the finite laws below. Exact hit `translation_loss_monotone`
     supplies deterministic postprocessing monotonicity and is applied
     directly; the local helper only converts its residual-entropy conclusion
     back to the imported finite mutual information. Mathlib's exact dependent
     Pi `Fintype` instance supplies heterogeneous selected-output tuples. -/

noncomputable section

namespace D5.S3.Entropy.Submodularity.SelectedObservationInformationMonotonicity

open D5.S3.ConceptDynamics.Communication.TranslationLossMonotonicity
open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.Divergence.ChainRule
open D5.S3.Entropy.ConditionalEntropy
open D5.S3.Entropy.Forgetting.CapacityMonotone
open D5.S3.Entropy.MaxEntropy
open D5.S3.Entropy.MutualInformation
open D5.S3.Entropy.MutualInformationEntropy

open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- The tuple of experiment outputs selected by a finite index set. -/
def selectedExperimentReadout
    {Sample Index : Type*} {Output : Index -> Type*}
    (output : forall i, Sample -> Output i) (selected : Finset Index) :
    Sample -> (forall i : selected, Output i.1) :=
  fun sample i => output i.1 sample

/-- The joint law of the selected output tuple and the hidden state. -/
noncomputable def selectedObservationJointLaw
    {Sample Hidden Index : Type*} {Output : Index -> Type*}
    [Fintype Sample]
    (mass : Sample -> Real) (hidden : Sample -> Hidden)
    (output : forall i, Sample -> Output i) (selected : Finset Index) :
    (forall i : selected, Output i.1) × Hidden -> Real :=
  readoutTargetLaw mass (selectedExperimentReadout output selected) hidden

/-- The source set function: mutual information between the hidden state and
the tuple of outputs indexed by the selected experiments. -/
noncomputable def selectedObservationInformation
    {Sample Hidden Index : Type*} {Output : Index -> Type*}
    [Fintype Sample] [Fintype Hidden] [forall i, Fintype (Output i)]
    (mass : Sample -> Real) (hidden : Sample -> Hidden)
    (output : forall i, Sample -> Output i) (selected : Finset Index) : Real := by
  classical
  letI (i : selected) : Fintype (Output i.1) := inferInstance
  exact mutualInformation (selectedObservationJointLaw mass hidden output selected)

private theorem target_information_eq_entropy_sub_residual
    {Sample Readout Hidden : Type*}
    [Fintype Sample] [Fintype Readout] [Fintype Hidden]
    (mass : Sample -> Real) (readout : Concept Sample Readout)
    (hidden : Concept Sample Hidden) (hmass : forall sample, 0 <= mass sample) :
    mutualInformation (readoutTargetLaw mass readout hidden) =
      shannonEntropy (pushforward hidden mass) -
        targetResidualEntropy mass readout hidden := by
  classical
  have hjoint_nonnegative :
      forall q, 0 <= readoutTargetLaw mass readout hidden q := by
    intro q
    simp only [readoutTargetLaw, pushforward]
    exact Finset.sum_nonneg fun sample _ => by
      split_ifs
      · exact hmass sample
      · exact le_rfl
  have htarget_marginal :
      marginal (fun q : Hidden × Readout =>
        readoutTargetLaw mass readout hidden (q.2, q.1)) =
        pushforward hidden mass := by
    funext hiddenValue
    simp only [marginal, readoutTargetLaw, pushforward]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro sample _
    rw [Finset.sum_eq_single (readout sample)]
    · simp [Prod.ext_iff]
    · intro readoutValue _ different
      simp [Prod.ext_iff, Ne.symm different]
    · simp
  have hinformation := mutual_information_eq_entropy_sub
    (readoutTargetLaw mass readout hidden) hjoint_nonnegative
  have hchain := entropy_chain_rule
    (readoutTargetLaw mass readout hidden) hjoint_nonnegative
  rw [htarget_marginal] at hinformation
  unfold targetResidualEntropy
  linarith

/-- Observing every experiment in a larger finite set cannot decrease its
mutual information with the hidden state. Conditional independence is not
needed for this monotonicity clause; it is needed only for the subsequent
submodularity claim in the source. -/
theorem selected_observation_information_monotone
    {Sample Hidden Index : Type*} {Output : Index -> Type*}
    [Fintype Sample] [Fintype Hidden]
    [forall i, Fintype (Output i)]
    (mass : Sample -> Real) (hidden : Sample -> Hidden)
    (output : forall i, Sample -> Output i)
    (hmass : (forall sample, 0 <= mass sample) /\ ∑ sample, mass sample = 1)
    {smaller larger : Finset Index} (subset : smaller ⊆ larger) :
    selectedObservationInformation mass hidden output smaller <=
      selectedObservationInformation mass hidden output larger := by
  classical
  letI (i : smaller) : Fintype (Output i.1) := inferInstance
  letI (i : larger) : Fintype (Output i.1) := inferInstance
  let restrictOutputs :
      (forall i : larger, Output i.1) -> (forall i : smaller, Output i.1) :=
    fun values i => values (Subtype.mk i.1 (subset i.2))
  have hreadout :
      restrictOutputs ∘ selectedExperimentReadout output larger =
        selectedExperimentReadout output smaller := by
    funext sample i
    rfl
  have hresidual :=
    (translation_loss_monotone mass hmass
      (selectedExperimentReadout output larger) restrictOutputs hidden).2
  rw [hreadout] at hresidual
  have hsmaller := target_information_eq_entropy_sub_residual mass
    (selectedExperimentReadout output smaller) hidden hmass.1
  have hlarger := target_information_eq_entropy_sub_residual mass
    (selectedExperimentReadout output larger) hidden hmass.1
  unfold selectedObservationInformation selectedObservationJointLaw
  linarith

#print axioms selectedExperimentReadout
#print axioms selectedObservationJointLaw
#print axioms selectedObservationInformation
#print axioms selected_observation_information_monotone

end D5.S3.Entropy.Submodularity.SelectedObservationInformationMonotonicity
