# The Ordered Quadratic of the Third Cover

## Abstract

The fractional Virasoro modes are the ordered quadratic coefficients of the two complementary currents, with the vacuum shift.

**Definition 1.1 (Sign ordering of the current modes).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedQuadratic.orderedPair`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedQuadratic.orderedPair` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

Let k and l be native indices, with frequencies k/3 and l/3. Place the first current on the left when k is negative and on the right otherwise. This is the mode ordering of the field product at n = −1 in Bakalov and Kac, arXiv:math/0402315v3, equation (3.13).

**Definition 1.2 (Native indices of a residue grid).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedQuadratic.residue`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedQuadratic.residue` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The set consists of integers with remainder a on division by three. For a = 1 or 2 the corresponding frequencies form the two complementary grids.

**Theorem 1.3 (Reflection interchanges the grid sums).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedQuadratic.complementary_residue_sums`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedQuadratic.complementary_residue_sums` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each m and polynomial Q, the sums on residues one and two agree. Reflection k ↦ 3m − k exchanges the grids and preserves the index-sorted pair. Sign ordering differs from sorting only where the fractional Heisenberg bracket vanishes.

**Definition 1.4 (Coefficient of the ordered product).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedQuadratic.orderedCoefficient`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedQuadratic.orderedCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

The coefficient of z^(-m-2) on a polynomial Q is the sum of ordered pairs with first index k in residue one and second index 3m − k in residue two.

**Theorem 1.5 (Finite support on each polynomial).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedQuadratic.orderedPair_finite_on_residue`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedQuadratic.orderedPair_finite_on_residue` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each m, polynomial Q and nonzero residue a, only finitely many summands on that residue act nontrivially. Restrict the finite support from ThirdCoverComplement.complementPair_finiteSupport to the given residue. The normalization uses ThirdCoverComplement.inverse_scale_sq.

**Theorem 1.6 (The fractional Virasoro mode as a single ordered sum).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedQuadratic.fractionalVirasoro_apply_ordered`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedQuadratic.fractionalVirasoro_apply_ordered` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On every polynomial, the complement mode equals the ordered coefficient plus 1/9 times the polynomial at m = 0. The two factors of the inverse square root account for the native one-third normalization. The native half-sum then splits into the two equal grid sums.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedQuadratic.complementary_residue_sums`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedQuadratic.fractionalVirasoro_apply_ordered`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedQuadratic.orderedCoefficient`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedQuadratic.orderedPair`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedQuadratic.orderedPair_finite_on_residue`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedQuadratic.residue`
- Dependency: [D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverComplement](ThirdCoverComplement.md)
