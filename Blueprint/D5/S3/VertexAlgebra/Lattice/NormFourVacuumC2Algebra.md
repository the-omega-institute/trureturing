# Actual Algebra on the Norm-Four Vacuum C2 Quotient

## Abstract

Actual Algebra on the Norm-Four Vacuum C2 Quotient.

**Definition 1.1 (Descended coefficient product).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/NormFourVacuumC2Algebra.quotientProduct`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/NormFourVacuumC2Algebra.quotientProduct` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every D,a,s with B(a,a)=4 and s squared equal to one: The bilinear map on the existing quotient induced by the actual minus-one coefficient on S. Both argument kernels follow from the full actual commutator identities.

**Definition 1.2 (Existing quotient ring).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/NormFourVacuumC2Algebra.quotientRing`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/NormFourVacuumC2Algebra.quotientRing` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every D,a,s with B(a,a)=4 and s squared equal to one: The commutative ring whose addition is the existing quotient addition, whose product is quotientProduct, and whose unit is the actual vacuum class. Associativity follows from the complete actual iterate formula.

**Definition 1.3 (Compatible complex algebra).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/NormFourVacuumC2Algebra.quotientAlgebra`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/NormFourVacuumC2Algebra.quotientAlgebra` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every D,a,s with B(a,a)=4 and s squared equal to one: The complex algebra supplied by the existing complex module and the descended bilinear product, with scalars mapping to scalar multiples of vacuum.

**Theorem 1.4 (Actual Algebra on the Norm-Four Vacuum C2 Quotient).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/NormFourVacuumC2Algebra.actual_vacuum_c2_algebra`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/NormFourVacuumC2Algebra.actual_vacuum_c2_algebra` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite integral symmetric even-diagonal lattice D, charge a with B(a,a)=4, and complex s with s squared equal to one, let S be the span of all finite negative Virasoro words on the actual vacuum. Let C be the inverse image in S of the span of u_(-2)v with both u and v in S. The existing additive quotient S/C carries a commutative associative unital ring and a complex algebra compatible with its existing module. Its multiplication sends the classes of u and v to the class of the actual coefficient u_(-1)v, and its unit is the vacuum class. The quotient is finite dimensional of dimension three.

The complete mode commutator at p=-1,q=-2 proves that multiplication by any actual state of S preserves C2. Every correction is a higher negative product of two states in S, so the left-state derivative theorem places it in literal C2. The commutator at p=q=-1 applied to the vacuum proves commutativity modulo C2 and hence preservation in the other argument.

The complete iterate formula at r=n=-1 proves associativity modulo C2. The first family at index zero is the desired iterated product; every positive-index term in that family, and every term of the second family, is a higher negative product in C2. Both finite-support families are consumed. The bilinear map then descends through both actual kernels by liftQ₂. Vacuum creation supplies the unit. The commutative ring reuses the existing additive group, and Algebra.ofModule reuses the existing complex scalar action. The dimension theorem is consumed from NormFourVacuumC2Exact.

This is a realization of the classical C2 algebra construction in the actual lattice carrier, in the context of Li, Abelianizing vertex algebras, Corollary 3.6 and Proposition 3.7. The norm-four vector retains its Dong-Mason-Zhu and Shimakura attribution. No C2 ideal, associativity, basis, positivity or rootlessness premise is added. The companion module identifies the algebra with truncated polynomials. Rationality, Zhu algebra, fusion, analytic CFT and string realization remain outside this result.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/NormFourVacuumC2Algebra.actual_vacuum_c2_algebra`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/NormFourVacuumC2Algebra.quotientAlgebra`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/NormFourVacuumC2Algebra.quotientProduct`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/NormFourVacuumC2Algebra.quotientRing`
- Dependency: [D5/S3/VertexAlgebra/Lattice/NormFourVacuumC2](NormFourVacuumC2.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/NormFourVacuumC2Exact](NormFourVacuumC2Exact.md)
