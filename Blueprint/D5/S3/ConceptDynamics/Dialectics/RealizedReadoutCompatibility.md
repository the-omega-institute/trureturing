# Realized Readout Compatibility

## Abstract

The realized readout is Mathlib's canonical factorization through a range.

For every function q from a state type X to a codomain B, the local realized readout is equal as a function to Mathlib's Set.rangeFactorization q.

This equality does not say that q is injective or surjective onto B, and it does not identify B with the realized range. Both sides already have codomain Set.range q, so no quotient or coercion is introduced.

**Theorem 1.1 (The realized readout is range factorization).**

$$\operatorname{realizedReadout}\left(q\right) = \operatorname{rangeFactorization}\left(q\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Dialectics/RealizedReadoutCompatibility.realizedReadout_eq_rangeFactorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The pinned upstream and local definitions construct the same subtype-valued function; their range-membership proofs are proof-irrelevant.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Dialectics/RealizedReadoutCompatibility.realizedReadout_eq_rangeFactorization`
- Dependency: [D5/S3/ConceptDynamics/Dialectics/DeterministicInterfaceEquivalence](DeterministicInterfaceEquivalence.md)
