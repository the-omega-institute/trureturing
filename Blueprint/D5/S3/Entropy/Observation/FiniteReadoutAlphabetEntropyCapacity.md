# Finite Readout Alphabet Entropy Capacity

## Abstract

A finite realized readout image bounds the entropy of every pushed-forward law.

**Theorem 1.1 (A finite readout alphabet bounds pushed-forward entropy).**

$$\begin{gathered}\forall X, O: \operatorname{Type},\\{}q: X \to O,\\{}\operatorname{Fintype}\left(\operatorname{range}\left(q\right)\right) \Rightarrow\\{}\forall P: \operatorname{PMF}\left(X\right),\\{}\operatorname{H}\left((y: \operatorname{range}\left(q\right)\mapsto \operatorname{toReal}\left(PMF.map(realizedReadout(q), P)(y)\right))\right) \le \log(\operatorname{card}\left(\operatorname{range}\left(q\right)\right)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/Observation/FiniteReadoutAlphabetEntropyCapacity.finite_readout_alphabet_entropy_capacity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The state space may be infinite. A PMF on that space is pushed forward along the canonical realizedReadout map into the actual range of the supplied readout.

Finiteness is required only for the realized image. The real-valued law in the displayed formula is obtained by applying ENNReal.toReal to the pushed-forward PMF pointwise.

The upper bound depends only on the cardinality of the realized image. No cardinality of an individual readout fiber occurs in either the hypothesis or the conclusion.

## References

- Truth anchor: `D5/S3/Entropy/Observation/FiniteReadoutAlphabetEntropyCapacity.finite_readout_alphabet_entropy_capacity`
- Dependency: [D5/S3/ConceptDynamics/Dialectics/DeterministicInterfaceEquivalence](../../ConceptDynamics/Dialectics/DeterministicInterfaceEquivalence.md)
- Dependency: [D5/S3/Entropy/MaxEntropy](../MaxEntropy.md)
