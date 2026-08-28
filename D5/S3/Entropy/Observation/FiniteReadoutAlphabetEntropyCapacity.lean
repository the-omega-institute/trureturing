/- GID: D5/S3/Entropy/Observation/FiniteReadoutAlphabetEntropyCapacity
   generality: G
   mirror-B: D5/B/S3/Entropy/Observation/FiniteReadoutAlphabetEntropyCapacity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A finite realized readout image bounds the entropy of every pushed-forward law. -/

import D5.S3.ConceptDynamics.Dialectics.DeterministicInterfaceEquivalence
import D5.S3.Entropy.MaxEntropy
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/- Library-search audit trail (2026-08-28):
   * Exact family hit `realizedReadout` is the canonical map from states to the
     effective image of a readout and is imported rather than redeclared.
   * Exact family hit `entropy_le_log_card` bounds a finite real probability
     mass function by the logarithm of its carrier cardinality and is applied
     directly to the pushed-forward PMF below.
   * Pinned Mathlib exact hits `PMF.map`, `PMF.tsum_coe`,
     `PMF.apply_ne_top`, and `ENNReal.toReal_sum` supply the source law and its
     finite real normalization. No existing theorem packages these primitives
     as the finite effective-readout alphabet bound. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Entropy.Observation.FiniteReadoutAlphabetEntropyCapacity

open D5.S3.ConceptDynamics.Dialectics.DeterministicInterfaceEquivalence
open D5.S3.Entropy.MaxEntropy

/-- Pushing any discrete probability law through a readout with finite realized
image produces at most the logarithm of that image's cardinality in Shannon
entropy. The bound names only the realized image, not the sizes of its fibers. -/
theorem finite_readout_alphabet_entropy_capacity
    {X Output : Type*} (readout : X -> Output)
    [Fintype (Set.range readout)] (prior : PMF X) :
    shannonEntropy
        (fun value : Set.range readout =>
          (PMF.map (realizedReadout readout) prior value).toReal) <=
      Real.log (Fintype.card (Set.range readout)) := by
  letI : Nonempty (Set.range readout) := by
    rcases prior.support_nonempty with ⟨state, _⟩
    exact ⟨realizedReadout readout state⟩
  have outputLawSum :
      (∑ value : Set.range readout,
          (PMF.map (realizedReadout readout) prior value).toReal) = 1 := by
    have pmfSum :
        (∑ value : Set.range readout,
          PMF.map (realizedReadout readout) prior value) = 1 := by
      simpa using (PMF.map (realizedReadout readout) prior).tsum_coe
    calc
      (∑ value : Set.range readout,
          (PMF.map (realizedReadout readout) prior value).toReal) =
          (∑ value : Set.range readout,
            PMF.map (realizedReadout readout) prior value).toReal := by
        symm
        exact ENNReal.toReal_sum (fun value _ =>
          PMF.apply_ne_top (PMF.map (realizedReadout readout) prior) value)
      _ = 1 := by rw [pmfSum]; simp
  exact entropy_le_log_card _ ⟨fun _ => ENNReal.toReal_nonneg, outputLawSum⟩

#print axioms finite_readout_alphabet_entropy_capacity

end D5.S3.Entropy.Observation.FiniteReadoutAlphabetEntropyCapacity
