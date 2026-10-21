# Actual half-Fock graded trace

## Abstract

Actual all-grade half-Fock eigenspaces and inserted traces

For arbitrary integral symmetric even-diagonal lattice data D, an invertible Gram determinant hu, every natural grade N and every ground endomorphism A, this source uses the original ActualGround, ActualTensor, public actualInverse and tensorL0. The odd oscillator weight is omega(i,n)=2n+1 and the actual grade is the kernel of tensorL0-(rank/16+N/2)id.

The finite fibre consists of finitely supported exponent vectors of odd weight N. Positivity is not assumed: odd positive weights bound occupied modes and exponents, including the N=0 and rank=0 boundaries. The ambient monomial/tensor basis remains infinite and arbitrary vectors are expanded through its finite Finsupp representation.

The local inverse identities are derived by mapping the public integral nonsingular-inverse laws into Complex. The resulting diagonal action is then transported through the actual tensor basis, giving the support criterion and the span of the finite grade vectors.

Ground endomorphisms act through TensorProduct.map id A. They commute with the actual L0 operator and therefore preserve every grade without a semisimplicity or preservation premise. The finite-ground dimension is inherited from the selected irreducible ground supplier.

The finite grade basis has indices OddFiber(D,N) times the Half ground basis. Its dimension is 2^(rank/2) times b_rank(N), and the trace of the actual restricted insertion is b_rank(N) times trace(A). Here b is independently the finite partition sum whose odd-part multiplicity m contributes multichoose(rank,m), while every even part contributes zero. A colour-allocation equivalence proves the count and identifies its generating function with the odd geometric-factor product.

For the actual quotient ground representation, nonzero quotientCharge makes every inserted grade trace vanish. Rank 24 and grade 1 give actual L0 weight 2, dimension 98304 and normalized exponent 1. For identity insertion, the rank-24 normalized character begins with 4096 times q^(1/2). Canonical twisted lift and parity, full module and orbifold structure, Monster identification, analytic evaluation of this character, fusion and anomaly structure, and the CFT/string/AdS-CFT bridge remain separate obligations. The existing eta S law is not a proof of these additional claims.

**Theorem 1.1 (All-grade inserted trace).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockGradedTrace.actual_grade_insert_trace_bRank`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockGradedTrace.actual_grade_insert_trace_bRank` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every grade N and every ground endomorphism A, the trace on the actual finite kernel grade equals the independently counted odd-partition multiplicity times the ground trace. A finite basis and actual restriction justify this trace; the infinite ambient tensor space is never assigned a finite-dimensional trace.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockGradedTrace.actual_grade_insert_trace_bRank`
- Dependency: [D5/S3/Combinatorics/Partitions/ColouredOddMultiplicity](../Combinatorics/Partitions/ColouredOddMultiplicity.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockChargedLZero](LatticeHalfFockChargedLZero.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockChargedTensorCoefficients](LatticeHalfFockChargedTensorCoefficients.md)
- Dependency: [D5/S3/VertexAlgebra/PolynomialFockCharacter](PolynomialFockCharacter.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OperatorAlgebra](TwistedGround/OperatorAlgebra.md)
