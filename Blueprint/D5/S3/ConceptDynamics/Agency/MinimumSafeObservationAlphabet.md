# Minimum Safe Observation Alphabet

## Abstract

Safe-compatible partitions determine the exact minimum safe observation alphabet.

**Theorem 1.1 (Safe partitions and deterministic safe observers have the same minimum size).**

$$\forall X, A \in \operatorname{Type},\\{}Legal: X \to \operatorname{Set}\left(A\right), chi_{safe} \in \mathbb{N},\\{}\operatorname{IsLeast}\left(\{k \in \mathbb{N} \mid \operatorname{SafeCompatiblePartition}\left(Legal, k\right)\}, chi_{safe}\right) \iff \operatorname{IsLeast}\left(\{k \in \mathbb{N} \mid \operatorname{SupportsDeterministicSafePolicy}\left(Legal, k\right)\}, chi_{safe}\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Agency/MinimumSafeObservationAlphabet.minimum_safe_observation_alphabet` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A safe-compatible partition is represented by a surjective readout into Fin k. Surjectivity ensures that all k observation values occur, and each effective fiber must admit one action legal at every state in that fiber.

The repository's deterministic safe-policy existence theorem identifies this fiber condition with a policy on the effective observation values, for each fixed k.

Transporting that equivalence through IsLeast proves both required halves: the minimum partition size is attained by a safe observer, and every safe observer uses at least that many realized values.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Agency/MinimumSafeObservationAlphabet.minimum_safe_observation_alphabet`
- Dependency: [D5/S3/ConceptDynamics/Agency/DeterministicSafePolicyExistence](DeterministicSafePolicyExistence.md)
