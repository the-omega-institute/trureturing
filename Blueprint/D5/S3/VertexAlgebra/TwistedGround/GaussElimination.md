# The Global Even Quadratic Gauss Law

## Abstract

The Global Even Quadratic Gauss Law.

**Theorem 1.1 (The Global Even Quadratic Gauss Law).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/GaussElimination.even_quadratic_gauss`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/GaussElimination.even_quadratic_gauss` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Q be a square coefficient matrix over Z/8 with any finite coordinate type, including the empty type. Suppose Q+Q transpose has unit determinant. The coordinate cardinality n is even, and the sign sum of x transpose Q x reduced modulo two equals 2^(n/2) times Mathlib chi_8(det(Q+Q transpose)).

A nonempty alternating reduction has a nonzero off-diagonal entry in every row: otherwise its determinant would vanish. Choose such a pair, separate its two coordinates, and combine opposite off-diagonal coefficients without changing the quadratic self-evaluation. The odd binary block is eliminated by the determinant-one Schur substitution. Its reduction modulo two is a genuine coordinate bijection, so finite summation factors into the binary Gauss sum and the residual Gauss sum.

Strong induction removes two coordinates at a time. The Gram determinant factors into the binary and residual determinants, and multiplicativity of chi_8 assembles their signs. The empty case has determinant and Gauss sum one.

For the original lattice, Q is lowerMatrix reduced modulo eight. Its symmetrization is the integral Gram matrix reduced modulo eight, and its mod-two self-evaluation is literally the original modTwoCocycle. An integer unit determinant has chi_8 equal to one. FlipAverage evaluates the flip-average trace on the selected ActualGround, and SymmetricPairing constructs a nonzero symmetric invariant form from it.

**Theorem 1.2 (The Original Charge-Cocycle Sum).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/GaussElimination.actual_quadratic_gauss_sum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/GaussElimination.actual_quadratic_gauss_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the original integral symmetric even lattice data D and integer unit determinant hu, the sum of complexSign(modTwoCocycle D a a) over all ModTwoCharge D is exactly 2 to groundRank D hu. The ground rank is the rank fixed by actual_twisted_ground_representation at D and hu. The statement includes every rank, including zero.

The proof applies the global elimination theorem to lowerMatrix reduced modulo eight. The identity lower_matrix_symmetrization identifies its polarization with D.G. Ring-map composition identifies its reduced quadratic polynomial with modTwoCocycle on equal arguments. An integer unit is 1 or -1, and chi_8 is one on both. The selected-rank equation identifies D.rank/2 with groundRank D hu, including rank zero.

This proves the positive quadratic sum required by the symmetric-pairing construction. FlipAverage and SymmetricPairing use this sum to construct the nondegenerate symmetric invariant form on the exact selected ActualGround.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/GaussElimination.actual_quadratic_gauss_sum`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/GaussElimination.even_quadratic_gauss`
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockChargedTensorCoefficients](../LatticeHalfFockChargedTensorCoefficients.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/BinarySchur](BinarySchur.md)
