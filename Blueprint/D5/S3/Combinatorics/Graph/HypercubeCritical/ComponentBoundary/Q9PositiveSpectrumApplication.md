# Occupied spectra of actual paired fibres

## Abstract

Occupied spectra of actual paired fibres

**Theorem 1.1 (Adjacency eigenvalue four).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9PositiveSpectrumApplication.component_adjacency_eigenvalue`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9PositiveSpectrumApplication.component_adjacency_eigenvalue` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complementary Huang Gram identity has scalar eight at unit transverse weights. The occupied Gram is four on the diagonal and the occupied adjacency off the diagonal. A boundary kernel therefore gives an adjacency eigenvector of eigenvalue four.

**Theorem 1.2 (Every axis in two actual components has at least nine paired fibres).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9PositiveSpectrumApplication.exists_two_components_with_positive_spectrum_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9PositiveSpectrumApplication.exists_two_components_with_positive_spectrum_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The positive eigenvector on a fixed occupied component invokes the spectral count and eight-star equality. If the actual axis had only eight paired fibres, they would all have the same projected parity, contradicting the exact occupied-fibre divisibility. https://arxiv.org/html/2610.09483v1#Thmproblem2

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9PositiveSpectrumApplication.component_adjacency_eigenvalue`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9PositiveSpectrumApplication.exists_two_components_with_positive_spectrum_bound`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/DiamondFreeSpectral](DiamondFreeSpectral.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9EightStarRigidity](Q9EightStarRigidity.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9PairedFibreAnyAxis](Q9PairedFibreAnyAxis.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9PositivePairedKernel](Q9PositivePairedKernel.md)
