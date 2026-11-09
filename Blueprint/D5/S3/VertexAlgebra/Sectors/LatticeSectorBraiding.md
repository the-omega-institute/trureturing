# Sector skew symmetry and finite braiding convolution

## Abstract

The actual lattice state-field skew-symmetry law descends to arbitrary charge sectors. For every signed mode `n`, the canonical coefficient is a finite convolution of reversed-sector coefficients, with the charge-preserving translation power and the normalized factor `(-1)^(n+j+1)/j!`.

**Definition 1.1 (Finite sector braiding term).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeSectorBraiding.reverseTerm`

*Formalization.* `D5/S3/VertexAlgebra/Sectors/LatticeSectorBraiding.reverseTerm` (`✓ std3`).

*Source.* Repository-derived from the actual state-field skew-symmetry supplier.

*Commentary.*

The `j`th charge-sector contribution to the skew-symmetry convolution.

**Theorem 1.2 (Canonical sector skew symmetry).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeSectorBraiding.canonical_skew`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeSectorBraiding.canonical_skew` (`✓ std3`). ∎

*Source.* Repository-derived from the actual state-field skew-symmetry supplier.

*Commentary.*

Every canonical sector mode has finite reverse support and equals the corresponding finite braiding convolution. The proof transports the all-state identity through `single_canonical`, the charge-sector translation law, and projection.

This is a finite algebraic specialization. It does not assert analytic convergence, a coherent tensor-category hexagon, a Monster module, or a physical CFT/string realization.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeSectorBraiding.canonical_skew`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeSectorBraiding.reverseTerm`
- Dependency: [D5/S3/VertexAlgebra/StateField/SkewSymmetry](../../StateField/SkewSymmetry.md)
- Dependency: [D5/S3/VertexAlgebra/Sectors/LatticeSectorBorcherds](LatticeSectorBorcherds.md)
