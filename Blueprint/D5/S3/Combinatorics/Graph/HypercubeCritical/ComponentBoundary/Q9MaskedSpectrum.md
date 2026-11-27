# The masked Huang eigenfunction

## Abstract

Spectral saturation of masked nine-cube components

**Theorem 1.1 (A singular mask forces a strictly positive eigenfunction on a component).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9MaskedSpectrum.exists_positive_masked_component`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9MaskedSpectrum.exists_positive_masked_component` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In a balanced actual component, a singular defect on one parity for a nonempty mask I gives a connected component of the graph retaining only the axes in I. The unsigned adjacency on that component has a strictly positive eigenfunction at the square root of the cardinality of I.

A nonzero kernel vector satisfies the parity Gram equation. Extend it by zero to the cube. Its Huang image already spends its full squared norm on the opposite parity in the component, by the weighted Clifford square identity. This yields a supported signed eigenvector. Switching to the unsigned rows and taking absolute values gives a row inequality. The same squared norm identity forces equality in each row. Positivity propagates from a nonzero vertex along masked edges.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9MaskedSpectrum.exists_positive_masked_component`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9MaskedGram](Q9MaskedGram.md)
