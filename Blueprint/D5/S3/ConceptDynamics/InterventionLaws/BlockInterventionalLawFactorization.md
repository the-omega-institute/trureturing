# Block Interventional Law Factorization

## Abstract

Independent block responses give a product post-intervention law.

A block intervention and a family of block response channels determine the joint response through the existing block outcome map. Pushing the source measure through that response defines its intervention law; pushing through one coordinate defines the corresponding local law.

**Theorem 1.1 (Independent block intervention laws factor).**

$$\mathit{BlockIndependent}\left(\mathit{mu}, a, M\right) \Rightarrow \mathit{blockInterventionalLaw}\left(\mathit{mu}, a, M\right) = \mathit{MeasurePi}\left(\mathit{localInterventionalLaw}\left(\mathit{mu}, a, M\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InterventionLaws/BlockInterventionalLawFactorization.block_interventional_law_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Probability-level block independence includes measurability of every intervened response and mutual independence of the finite family. Mathlib's finite independent-pushforward theorem then identifies the joint law with the product of its local pushforwards.

**Lemma 1.2 (A single block factors trivially).**

$$\mathit{AEMeasurable}\left(\mathit{MUnit}\left(\mathit{aUnit}\right), \mathit{mu}\right) \Rightarrow \left(\mathit{BlockIndependent}\left(\mathit{mu}, \mathit{aUnit}, \mathit{MUnit}\right) \land \mathit{blockInterventionalLaw}\left(\mathit{mu}, \mathit{aUnit}, \mathit{MUnit}\right) = \mathit{MeasurePi}\left(\mathit{localInterventionalLaw}\left(\mathit{mu}, \mathit{aUnit}, \mathit{MUnit}\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InterventionLaws/BlockInterventionalLawFactorization.single_block_factorization_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On a one-element block index, every measurable response family is mutually independent. The general theorem therefore reduces the joint law to the one-coordinate product law.

**Lemma 1.3 (The empty block law is Dirac).**

$$\mathit{blockInterventionalLaw}\left(\mathit{dirac}\left(\mathit{unit}\right), \mathit{emptyIntervention}, \mathit{emptyModel}\right) = \mathit{dirac}\left(\mathit{emptyTuple}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InterventionLaws/BlockInterventionalLawFactorization.empty_block_factorization_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an empty block family, the response tuple is unique. The empty finite product measure is the Dirac law at that empty tuple.

**Lemma 1.4 (A cross-block edge defeats the product law).**

$$\left(\neg \mathit{BlockIndependent}\left(\mathit{uniform}\left(\mathit{BoolPair}\right), \mathit{nullIntervention}, \mathit{directedEdgeResponse}\right)\right) \land \left(\neg \mathit{blockInterventionalLaw}\left(\mathit{uniform}\left(\mathit{BoolPair}\right), \mathit{nullIntervention}, \mathit{directedEdgeResponse}\right) = \mathit{MeasurePi}\left(\mathit{localInterventionalLaw}\left(\mathit{uniform}\left(\mathit{BoolPair}\right), \mathit{nullIntervention}, \mathit{directedEdgeResponse}\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InterventionLaws/BlockInterventionalLawFactorization.block_independence_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With two fair exogenous bits, the right block copies the left block along a directed edge. The two responses are equal, so their all-true diagonal has mass one half, whereas the product of the two fair marginals assigns one quarter. Thus block independence and the product identity both fail.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InterventionLaws/BlockInterventionalLawFactorization.block_independence_is_necessary`
- Truth anchor: `D5/S3/ConceptDynamics/InterventionLaws/BlockInterventionalLawFactorization.block_interventional_law_factorization`
- Truth anchor: `D5/S3/ConceptDynamics/InterventionLaws/BlockInterventionalLawFactorization.empty_block_factorization_witness`
- Truth anchor: `D5/S3/ConceptDynamics/InterventionLaws/BlockInterventionalLawFactorization.single_block_factorization_witness`
- Dependency: [D5/S3/ConceptDynamics/Interventions/BlockCausalQuotientDecomposition](../Interventions/BlockCausalQuotientDecomposition.md)
