# Ordered integral hyperbolic extension

## Abstract

Ordered integral hyperbolic extension

The finite coordinates remain the original ordered Fin(rank+2): the old coordinates precede m and n. The literal new block has zero diagonal and off-diagonal entries one. The full pairing is B(a,b)+m*s+n*r, the charge energy is energy(a)+m*n, and the canonical LOWER cocycle adds n*r. No charge is removed. The inverse is the old integral inverse and the same U block. Its two multiplication equations are proved before casting to the complex Gram inverse. The real subspaces (x,t,t) and (0,t,-t) give signature (rank+1,1) when the old real Gram matrix is positive definite; they do not change integral coordinates or the hyperbolic normalization.

**Definition 1.1 (The ordered block construction).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/OrderedHyperbolicExtension.extend`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/OrderedHyperbolicExtension.extend` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The old Gram block is followed by the literal matrix with zero diagonal and both off-diagonal entries one, using the old-then-m,n finite order.

**Theorem 1.2 (The exact ordered lower cocycle).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/OrderedHyperbolicExtension.lowerCocycleExponent_splice`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/OrderedHyperbolicExtension.lowerCocycleExponent_splice` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary old charges a,b and integers m,n,r,s, the original lower-triangle exponent is lower(a,b)+n*r.

**Theorem 1.3 (The constructed left inverse).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/OrderedHyperbolicExtension.integerInverse_left`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/OrderedHyperbolicExtension.integerInverse_left` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The literal reindexed block matrix with blocks G inverse and U multiplies the extended integral Gram matrix to the identity.

**Theorem 1.4 (The constructed right inverse).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/OrderedHyperbolicExtension.integerInverse_right`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/OrderedHyperbolicExtension.integerInverse_right` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The extended integral Gram matrix multiplies the same constructed integral inverse to the identity.

**Theorem 1.5 (Signature from explicit real subspaces).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/OrderedHyperbolicExtension.signature_extend`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/OrderedHyperbolicExtension.signature_extend` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The images of (x,t) mapped to (x,t,t) and t mapped to (0,t,-t) have proved dimensions rank+1 and one and positive and negative restricted quadratic forms.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/OrderedHyperbolicExtension.extend`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/OrderedHyperbolicExtension.integerInverse_left`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/OrderedHyperbolicExtension.integerInverse_right`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/OrderedHyperbolicExtension.lowerCocycleExponent_splice`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/OrderedHyperbolicExtension.signature_extend`
- Dependency: [D5/S3/VertexAlgebra/Lattice/LatticeRealNullFrame](LatticeRealNullFrame.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeActualProductKernel](../LatticeActualProductKernel.md)
- Dependency: [D5/S3/VertexAlgebra/LatticePositiveEnergy](../LatticePositiveEnergy.md)
