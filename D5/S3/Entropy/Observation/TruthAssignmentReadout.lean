/- GID: D5/S3/Entropy/Observation/TruthAssignmentReadout
   generality: G
   mirror-B: D5/B/S3/Entropy/Observation/TruthAssignmentReadout
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Truth-assignment entropy splits into readout entropy and conditional uncertainty. -/

import D5.S3.Entropy.Observation.DeterministicReadoutEntropyDecomposition

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Entropy.Observation.TruthAssignmentReadout

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.Information.RefinementEntropyMonotonicity
open D5.S3.Entropy.MaxEntropy
open D5.S3.Entropy.Observation.DeterministicReadoutEntropyDecomposition

open Classical in
/-- Apply deterministic readout accounting to assignments of finitely many Boolean
coordinates. These coordinates need not exhaust logical propositions, and the entropy
is finite Shannon entropy rather than a measure of logical validity. -/
theorem truth_assignment_entropy_decomposition
    {Question Fine Coarse : Type*} [Fintype Question] [Fintype Fine] [Fintype Coarse]
    (mu : (Question → Bool) → Real)
    (hmu : (∀ x, 0 ≤ mu x) ∧ (∑ x, mu x) = 1)
    (fine : Concept (Question → Bool) Fine) (coarse : Concept (Question → Bool) Coarse)
    (forget : Fine → Coarse) (hFactor : coarse = forget ∘ fine) :
    shannonEntropy mu = conceptInformation mu fine + conceptResidual mu fine ∧
      conceptResidual mu fine ≤ conceptResidual mu coarse :=
  deterministic_readout_entropy_decomposition mu hmu fine coarse forget hFactor

#print axioms truth_assignment_entropy_decomposition

end D5.S3.Entropy.Observation.TruthAssignmentReadout
