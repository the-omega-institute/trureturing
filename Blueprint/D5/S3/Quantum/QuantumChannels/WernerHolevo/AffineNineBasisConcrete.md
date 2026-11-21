# Symmetric unitary bases in powers of nine

## Abstract

Symmetric unitary bases in powers of nine.

**Theorem 1.1 (Orthogonal unitaries span the symmetric subspace).**

$$n = 9^{d},\quad\operatorname{hs}\left(b_{i}, b_{j}\right) = n\delta_{ij}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/WernerHolevo/AffineNineBasisConcrete.exists_f9Basis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural exponent d at least two, there exists a basis b over the complex numbers of the entire space of n by n complex symmetric matrices. It has n(n+1)/2 elements, each of which is unitary, and the pairing formula holds for all basis indices i and j. The construction applies the order-nine seed and the edge labeling to affine lines.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/WernerHolevo/AffineNineBasisConcrete.exists_f9Basis`
- Dependency: [D5/S3/Quantum/QuantumChannels/WernerHolevo/AffineNineBasis](AffineNineBasis.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/WernerHolevo/AffineNineFinite](AffineNineFinite.md)
