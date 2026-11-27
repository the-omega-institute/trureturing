# Mixed Products of Norm-Four Lattice States

## Abstract

The singular mixed products of signed norm-four states vanish for opposite signs or orthogonal directions.

**Theorem 1.1 (Opposite signs in one norm-four direction).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LeechFrame/NormFourMixedProducts.opposite_sign_products`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LeechFrame/NormFourMixedProducts.opposite_sign_products` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a norm-four charge and s² = 1, every nonnegative product of the states of signs s and −s vanishes. The mixed terms cancel, and the quadratic and charged terms cancel in degrees zero through three. Their higher products vanish by the self-product tail formulas.

**Theorem 1.2 (Products of states in orthogonal directions).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LeechFrame/NormFourMixedProducts.orthogonal_products`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LeechFrame/NormFourMixedProducts.orthogonal_products` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For orthogonal charges and arbitrary scalars, all nonnegative mixed products vanish. Orthogonality removes the current contractions, and negative creation-coefficient indices give the ground-product vanishing.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LeechFrame/NormFourMixedProducts.opposite_sign_products`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LeechFrame/NormFourMixedProducts.orthogonal_products`
- Dependency: [D5/S3/VertexAlgebra/Lattice/NormFourVirasoroVector](../NormFourVirasoroVector.md)
