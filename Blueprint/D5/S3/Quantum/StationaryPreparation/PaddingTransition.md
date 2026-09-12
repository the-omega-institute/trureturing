# Padding Transition

## Abstract

Recoverable predecessors make the explicit last-tail transition an isometry.

**Theorem 1.1 (Padding Transition).**

$$\operatorname{conjTranspose}\left(\operatorname{W}\left(a, head\right)\right) \operatorname{W}\left(a, head\right) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/PaddingTransition.W_gram` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite alphabet, every multiset a and every chosen head, W(a,head) has orthonormal columns. No maximality or positive-capacity assumption is needed. Its memory is the sink together with each nonzero bounded tail and a bounded head index.

The probability law includes the one-tail boundary: positive head index emits head, while index zero emits the sole tail letter into the sink. Zero-probability letters cannot produce supported predecessors. On nonzero support, the emitted letter and successor recover the entire predecessor; this recovery discharges the off-diagonal Gram entries.

## References

- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PaddingTransition.W_gram`
- Dependency: [D5/S3/Quantum/Entanglement/OccupancyWordSectors](../Entanglement/OccupancyWordSectors.md)
- Dependency: [D5/S3/Quantum/Entanglement/SequentialRegisterCircuit](../Entanglement/SequentialRegisterCircuit.md)
