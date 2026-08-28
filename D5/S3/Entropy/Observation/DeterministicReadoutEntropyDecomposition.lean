/- GID: D5/S3/Entropy/Observation/DeterministicReadoutEntropyDecomposition
   generality: G
   mirror-B: D5/B/S3/Entropy/Observation/DeterministicReadoutEntropyDecomposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A deterministic readout splits source entropy, and garbling increases its residual. -/

/- Library-search audit trail (2026-08-29):
   * Exact repository hit `quotient_fiber_entropy_decomposition` supplies the entropy split for
     the canonical graph law of a deterministic finite readout and is applied below.
   * Exact repository hit `refinement_information_residual_monotone` supplies residual-entropy
     monotonicity for the canonical `Concept` factorization order and is applied below.
   * Pinned Mathlib searches for finite Shannon entropy, conditional entropy, deterministic
     readout chain rules, and entropy monotonicity under garbling found no exact real-valued
     finite theorem; the repository owners already record the same miss. -/

import D5.S3.ConceptDynamics.Information.RefinementEntropyMonotonicity
import D5.S3.Entropy.Fusion.QuotientFiberDecomposition

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Entropy.Observation.DeterministicReadoutEntropyDecomposition

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.Information.RefinementEntropyMonotonicity
open D5.S3.Divergence.ChainRule
open D5.S3.Entropy.Fusion.QuotientFiberDecomposition
open D5.S3.Entropy.Forgetting.CapacityMonotone
open D5.S3.Entropy.MaxEntropy

/-- A finite probability law splits into the entropy retained by a deterministic readout and the
conditional entropy remaining in its fibers. If a coarser readout factors through the finer one,
then the finer readout leaves no more residual entropy than the coarser readout. -/
theorem deterministic_readout_entropy_decomposition
    {X Fine Coarse : Type*} [Fintype X] [Fintype Fine] [Fintype Coarse]
    (mu : X -> Real)
    (hmu : (forall x, 0 <= mu x) /\ (∑ x, mu x) = 1)
    (fine : Concept X Fine) (coarse : Concept X Coarse)
    (forget : Fine -> Coarse) (hFactor : coarse = forget ∘ fine) :
    shannonEntropy mu = conceptInformation mu fine + conceptResidual mu fine /\
      conceptResidual mu fine <= conceptResidual mu coarse := by
  have hDecomposition :=
    (quotient_fiber_entropy_decomposition mu fine hmu.1 hmu.2).2
  have hGraphLaw :
      pushforward (fun x => (fine x, x)) mu = conceptStateLaw mu fine := by
    funext z
    rcases z with ⟨c, x⟩
    classical
    simp only [pushforward, conceptStateLaw]
    rw [Finset.sum_eq_single x]
    · by_cases hfx : fine x = c <;> simp [hfx]
    · intro y _ hy
      have hPair : (fine y, y) ≠ (c, x) := by
        intro h
        exact hy (congrArg Prod.snd h)
      exact if_neg hPair
    · simp
  rw [hGraphLaw] at hDecomposition
  have hBalance :
      shannonEntropy mu = conceptInformation mu fine + conceptResidual mu fine := by
    simpa [conceptInformation, conceptLaw, conceptResidual] using hDecomposition
  have hMonotonicity :=
    refinement_information_residual_monotone mu hmu coarse fine ⟨forget, hFactor⟩
  exact ⟨hBalance, hMonotonicity.2⟩

/-- The uniform Boolean law, identity fine readout, and constant coarse readout
witness that the public carrier, probability, and factorization hypotheses are inhabited. -/
example :
    let mu : Bool -> Real := fun _ => 1 / 2
    shannonEntropy mu = conceptInformation mu id + conceptResidual mu id /\
      conceptResidual mu id <= conceptResidual mu (fun _ : Bool => ()) := by
  dsimp only
  apply deterministic_readout_entropy_decomposition (forget := fun _ => ())
  · constructor
    · intro x
      norm_num
    · norm_num [Fintype.sum_bool]
  · rfl

#print axioms deterministic_readout_entropy_decomposition

end D5.S3.Entropy.Observation.DeterministicReadoutEntropyDecomposition
