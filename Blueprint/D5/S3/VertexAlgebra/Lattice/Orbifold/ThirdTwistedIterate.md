# The Third-Cover Comparison from the Twisted Iterate

## Abstract

The native lattice current minus-one product has the fractional Virasoro modes under an explicit twisted iterate premise.

**Definition 1.1 (Coefficientwise twisted iterate premise).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedIterate.pairIterate`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedIterate.pairIterate` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

Use Bakalov and Kac, arXiv:math/0402315v3, equation (3.13), at n = −1 with first frequency grid 1/3. For every integer m and complement polynomial, take the sign-ordered finsum of products of the supplied modes over indices k in residue one with partner index 3m − k. This equals the finsum over j ≥ 0 of Ring.choose (1/3) j times the twisted mode of the native (j−1)-product. The shift z^(-j) selects native index 3(m + 1 − j) in that mode.

**Theorem 1.2 (Fractional modes of the native quadratic state).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedIterate.fractionalVirasoro_of_twistedIterate`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedIterate.fractionalVirasoro_of_twistedIterate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

Take the two native current states from ConformalGroundTransport.current and assume their complex bilinear Gram pairing is one. The supplied complex-linear map must restrict to the normalized fractional currents on residues one and two respectively, vanish off each of those grids, send the vacuum to the identity at native index −3 and zero elsewhere, and satisfy the coefficientwise iterate on this pair. At index 3(m + 1), the twisted mode of the actual native (−1)-product is fractionalVirasoro(m). The basis products from FullJacobiCurrentTransport.source_current_product extend bilinearly. The iterate retains the native (−1)-product at j = 0 and the vacuum contraction at j = 2. The latter contributes −1/9 at m = 0 on the iterate side.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedIterate.fractionalVirasoro_of_twistedIterate`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedIterate.pairIterate`
- Dependency: [D5/S3/VertexAlgebra/Lattice/Automorphisms/ConformalGroundTransport](../Automorphisms/ConformalGroundTransport.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedQuadratic](ThirdTwistedQuadratic.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeActualConformalState](../../LatticeActualConformalState.md)
- Dependency: [D5/S3/VertexAlgebra/Modules/FullJacobiCurrentTransport](../../Modules/FullJacobiCurrentTransport.md)
