# Exact integral construction

## Abstract

Explicit Golay-congruence lattice mathematics.

**Theorem 1.1 (Original lattice normalization).**

Lean statement: `D5/S3/VertexAlgebra/GolayLeech/ExplicitLeechLattice.charge_pairing_scaled`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/GolayLeech/ExplicitLeechLattice.charge_pairing_scaled` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original LatticeData bilinear pairing on arbitrary charges equals the coordinate dot product of B times the charges divided by eight. Every integer scaling identity is proved.

**Theorem 1.2 (Genuine positive definiteness).**

Lean statement: `D5/S3/VertexAlgebra/GolayLeech/ExplicitLeechLattice.real_positive`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/GolayLeech/ExplicitLeechLattice.real_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real extension of B is injective because its actual determinant is nonzero. The scaled Gram identity turns every nonzero real quadratic value into a positive sum of squares.

**Theorem 1.3 (Explicit rank-24 supplier and original ground).**

Lean statement: `D5/S3/VertexAlgebra/GolayLeech/ExplicitLeechLattice.actual_leech_supplier`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/GolayLeech/ExplicitLeechLattice.actual_leech_supplier` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The concrete original LatticeData has rank twenty-four, determinant one, even norms, minimum nonzero norm four, attained norm four and the full congruence/basis identity. Its actual unit determinant is passed directly to actual_twisted_ground_representation, obtaining the original irreducible ground of dimension 4096. This does not construct the full moonshine extension, Monster action, a fusion category, string dynamics or AdS/CFT.

## References

- Truth anchor: `D5/S3/VertexAlgebra/GolayLeech/ExplicitLeechLattice.actual_leech_supplier`
- Truth anchor: `D5/S3/VertexAlgebra/GolayLeech/ExplicitLeechLattice.charge_pairing_scaled`
- Truth anchor: `D5/S3/VertexAlgebra/GolayLeech/ExplicitLeechLattice.real_positive`
- Dependency: [D5/S3/VertexAlgebra/GolayLeech/ExplicitGolayDuality](ExplicitGolayDuality.md)
- Dependency: [D5/S3/VertexAlgebra/GolayLeech/ExplicitLeechSpan](ExplicitLeechSpan.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeTwistedGroundRealization](../LatticeTwistedGroundRealization.md)
