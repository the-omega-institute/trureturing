# Lossless Readout Reflexive Gap

## Abstract

A lossless readout realizes every Boolean state predicate but no same-state catalog is exhaustive.

**Definition 1.1 (Observable predicate pullback).**

$$\forall A: Type, O: Type, R: A \to O,\\{}q: \operatorname{range}\left(R\right) \to Bool, a: A,\\{}\operatorname{observablePullback}\left(R, q, a\right) = \operatorname{q}\left(\operatorname{realizedReadout}\left(R, a\right)\right).$$

*Formalization.* `D5/S3/ConceptDynamics/ObservationTopology/LosslessReadoutReflexiveGap.observablePullback` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A Boolean predicate on the realized range of R is pulled back along the canonical realized readout from states to that range.

**Theorem 1.2 (A lossless readout realizes every state predicate uniquely).**

$$\forall A: Type, O: Type, R: A \to O,\\{}\operatorname{Injective}\left(R\right) \Rightarrow \operatorname{Bijective}\left(\operatorname{observablePullback}\left(R\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ObservationTopology/LosslessReadoutReflexiveGap.lossless_readout_predicate_equiv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary types A and O and an injective readout R from A to O, pullback is a bijection from Boolean predicates on range R to all Boolean predicates on A.

The proof uses the exact identification with Mathlib's range factorization and its predicate-space composition theorem.

**Theorem 1.3 (The transported diagonal escapes every same-state catalog).**

$$\forall A: Type, O: Type, R: A \to O,\\{}\operatorname{Injective}\left(R\right), catalog: A \to \left(\operatorname{range}\left(R\right) \to Bool\right),\\{}\exists q: \operatorname{range}\left(R\right) \to Bool, \forall a: A, \operatorname{q}\left(\operatorname{realizedReadout}\left(R, a\right)\right) \neq \operatorname{catalog}\left(a, \operatorname{realizedReadout}\left(R, a\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ObservationTopology/LosslessReadoutReflexiveGap.observable_diagonal_escape` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Given the same arbitrary carriers and injective readout, every catalog from states to Boolean predicates on range R misses a predicate q.

At each state a, q disagrees with catalog a at the realized readout of a, making the witness explicit on the empirical image.

**Theorem 1.4 (Empirical predicate completeness with strict reflexive failure).**

$$\forall A: Type, O: Type, R: A \to O,\\{}\operatorname{Injective}\left(R\right) \Rightarrow\\{}\operatorname{Bijective}\left(\operatorname{observablePullback}\left(R\right)\right) \land\\{}\forall catalog: A \to \left(\operatorname{range}\left(R\right) \to Bool\right), \neg \operatorname{Surjective}\left(catalog\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ObservationTopology/LosslessReadoutReflexiveGap.lossless_observation_strict_reflexive_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An injective readout simultaneously gives a bijective predicate pullback and makes every same-state catalog non-surjective onto the observable Boolean predicate space.

The result does not claim a new diagonal theorem; it identifies the escaped predicate space with the image of the verified readout.

## References

- Truth anchor: `D5/S3/ConceptDynamics/ObservationTopology/LosslessReadoutReflexiveGap.lossless_observation_strict_reflexive_gap`
- Truth anchor: `D5/S3/ConceptDynamics/ObservationTopology/LosslessReadoutReflexiveGap.lossless_readout_predicate_equiv`
- Truth anchor: `D5/S3/ConceptDynamics/ObservationTopology/LosslessReadoutReflexiveGap.observablePullback`
- Truth anchor: `D5/S3/ConceptDynamics/ObservationTopology/LosslessReadoutReflexiveGap.observable_diagonal_escape`
- Dependency: [D5/S3/ConceptDynamics/Dialectics/RealizedReadoutCompatibility](../Dialectics/RealizedReadoutCompatibility.md)
