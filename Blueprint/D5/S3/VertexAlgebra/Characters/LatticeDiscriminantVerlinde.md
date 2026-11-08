# Finite Discriminant Verlinde Convolution

## Abstract

Finite discriminant fusion convolution for the Weil S-kernel.

**Definition 1.1 (Normalized finite triple convolution).**

Lean statement: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantVerlinde.fusionCoefficient`

*Formalization.* `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantVerlinde.fusionCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For discriminant labels a, b and c, fusionCoefficient is the rho-normalized finite triple product of the pairing characters. It is the pointed finite modular-data analogue of a Verlinde coefficient.

**Theorem 1.2 (Discriminant addition law).**

Lean statement: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantVerlinde.fusionCoefficient_eq_indicator`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantVerlinde.fusionCoefficient_eq_indicator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The normalized Weil S convolution is exactly the indicator of the finite addition law a + b = c. The proof uses the nondegenerate pairing character orthogonality and rho squared equal to the discriminant cardinality.

This is a finite modular-data identity for the lattice discriminant pairing. It does not assert a tensor-category construction or an analytic Verlinde theorem.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantVerlinde.fusionCoefficient`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantVerlinde.fusionCoefficient_eq_indicator`
- Dependency: [D5/S3/VertexAlgebra/Characters/LatticeDiscriminantWeil](LatticeDiscriminantWeil.md)
