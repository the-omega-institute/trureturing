/- GID: D5/S3/Entropy/Submodularity/SelectedObservationInformationMonotonicityCanonical
   generality: G
   mirror-B: D5/B/S3/Entropy/Submodularity/SelectedObservationInformationMonotonicityCanonical
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Selected canonical joint readouts carry monotone mutual information. -/

import D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
import D5.S3.Entropy.Submodularity.SelectedObservationInformationMonotonicity

/- Library-search audit trail (2026-08-25):
   * Exact current-tree hit `jointReadout` is the canonical dependent-product
     readout and is imported and instantiated directly in the public statement.
   * The frozen selected-observation theorem proves the required monotonicity,
     but its public statement uses a withdrawn duplicate readout definition. It
     is imported solely as proof machinery and is not bound to this atom.
   * Current-tree searches found no other canonical selected-Finset statement.
   * Pinned Mathlib searches for finite mutual-information monotonicity and data
     processing found no exact theorem on this finite real-valued law carrier. -/

noncomputable section

namespace D5.S3.Entropy.Submodularity.SelectedObservationInformationMonotonicityCanonical

open D5.S3.ConceptDynamics.Communication.TranslationLossMonotonicity
open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
open D5.S3.Entropy.MutualInformation
open D5.S3.Entropy.Submodularity.SelectedObservationInformationMonotonicity

open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Enlarging a finite experiment selection cannot decrease the mutual
information between its canonical joint readout and the hidden state.
Conditional independence is not needed for this monotonicity clause. -/
theorem selected_observation_information_monotone_canonical
    {Sample Hidden Index : Type*} {Output : Index -> Type*}
    [Fintype Sample] [Fintype Hidden] [forall i, Fintype (Output i)]
    (mass : Sample -> Real) (hidden : Sample -> Hidden)
    (output : forall i, Sample -> Output i)
    (hmass : (forall sample, 0 <= mass sample) /\ ∑ sample, mass sample = 1)
    {smaller larger : Finset Index} (subset : smaller ⊆ larger) :
    (by
      classical
      letI (i : smaller) : Fintype (Output i.1) := inferInstance
      exact mutualInformation
        (readoutTargetLaw mass
          (jointReadout (fun i : smaller => output i.1)) hidden)) <=
      (by
        classical
        letI (i : larger) : Fintype (Output i.1) := inferInstance
        exact mutualInformation
          (readoutTargetLaw mass
            (jointReadout (fun i : larger => output i.1)) hidden)) := by
  classical
  change selectedObservationInformation mass hidden output smaller <=
    selectedObservationInformation mass hidden output larger
  exact selected_observation_information_monotone mass hidden output hmass subset

#print axioms selected_observation_information_monotone_canonical

end D5.S3.Entropy.Submodularity.SelectedObservationInformationMonotonicityCanonical
