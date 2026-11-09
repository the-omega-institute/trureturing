# Sector skew symmetry and finite braiding convolution

## Abstract

Sector skew symmetry and finite braiding convolution

The actual lattice state-field skew-symmetry law descends to arbitrary charge sectors. For every signed mode n, the canonical coefficient is a finite convolution of reversed-sector coefficients, with the charge-preserving translation power and the normalized factor (-1)^(n+j+1)/j!. The proof transports the all-state identity through single_canonical, the charge-sector translation law, and projection.

**Definition 1.1 (Finite sector braiding term).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeSectorBraiding.reverseTerm`

*Formalization.* `D5/S3/VertexAlgebra/Sectors/LatticeSectorBraiding.reverseTerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The jth charge-sector contribution to the skew-symmetry convolution.

**Theorem 1.2 (Canonical sector skew symmetry).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeSectorBraiding.canonical_skew`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeSectorBraiding.canonical_skew` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every canonical sector mode has finite reverse support and equals the corresponding finite braiding convolution.

This is a finite algebraic specialization of the existing actual state-field skew-symmetry supplier. It makes no claim of analytic convergence, a coherent tensor-category hexagon, a Monster module, or a physical CFT/string realization.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeSectorBraiding.canonical_skew`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeSectorBraiding.reverseTerm`
- Dependency: [D5/S3/VertexAlgebra/Sectors/LatticeSectorBorcherds](LatticeSectorBorcherds.md)
- Dependency: [D5/S3/VertexAlgebra/Sectors/LatticeSectorGround](LatticeSectorGround.md)
- Dependency: [D5/S3/VertexAlgebra/StateField/SkewSymmetry](../StateField/SkewSymmetry.md)
