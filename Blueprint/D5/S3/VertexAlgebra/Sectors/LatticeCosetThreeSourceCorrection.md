# Native three-source Schur correction

## Abstract

LatticeCosetThreeSourceCorrection

Let D be the positive definite original integral even lattice, e any finite external rank, B the integral mixed block, and C any symmetric integral block with even diagonal. Write E for ambient(D,e,B,C), J for injection, P for projection, I for compressed, and K(a,b,n) for the native correction: (-1)^n times the rational generalized binomial choose(schur(a,b),n), cast to complex scalars. The ambient block need not be positive or nondegenerate; either rank may vanish. These are exactly the native carriers and parameters of LatticeCosetOperatorCorrection.

**Theorem 1.1 (field_transverse_creation).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeCosetThreeSourceCorrection.field_transverse_creation`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeCosetThreeSourceCorrection.field_transverse_creation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all integral external a,b, every original source u, arbitrary ambient z, integer m and natural n, let M(b,n) multiply the ambient state by transversePolynomial of the n-th native external creationExponential coefficient of b. Then Y_E(J_a u)[m](M(b,n)z) is the finite sum for k in range(n+1) of K(a,b,k) times M(b,n-k)(Y_E(J_a u)[m-k]z). Residual creation is retained before projection. Polynomial induction uses field_transverse_commutator on arbitrary ambient states. The retained substitution of the native creation exponential is a product of retained creation and the existing scalar substitution; PowerSeries differential uniqueness proves that product identity. The scalar coefficients are supplied by transverse_creation_coefficient, without a binomial-support assumption.

**Theorem 1.2 (three_source_projection_correction).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeCosetThreeSourceCorrection.three_source_projection_correction`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeCosetThreeSourceCorrection.three_source_projection_correction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all external integral a,b,c,d, every original states u,v,t,w and integer p,q,r, the theorem jointly asserts finite support on the single product index (i,j,k) in N times N times N and the exact equation: P_(a+(b+(c+d)))(Y_E(J_a u)[p](Y_E(J_b v)[q](Y_E(J_c t)[r](J_d w)))) equals the finsum over (i,j,k) of (K(a,b,i)*K(a,c,j)*K(b,c,k)) times I(a,b+(c+d),u,p-i-j)(I(b,c+d,v,q+i-k)(I(c,d,t,r+j+k)w)). Inner truncation first bounds j+k. For the finitely many remaining pairs, middle truncation on each actual resulting c-state bounds i. Only after this joint support proof is the creation index n reindexed as j+k. The c-field is reconstructed by inner_creation_expansion; the middle field acts by field_transverse_creation; the existing projected_transverse_polynomial and transverse_creation_coefficient supply K(a,c,j). The existing intermediate_projection_correction supplies the middle reconstruction and K(a,b,i), while the retained middle action supplies K(b,c,k). No uniform outer cutoff, ground-state restriction or assumed rational locality or associativity enters.

The original integer modes, epsilon and half-diagonal conventions are preserved. Native lattice fields follow Bakalov-Kac, math/0402315v1, section 4.1. This is an operator identity on the existing native carriers; it supplies a reusable composition law toward the broader mathematical objective and makes no assertion of completed string theory, physical realization, a new VOA structure or an AdS/CFT correspondence.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeCosetThreeSourceCorrection.field_transverse_creation`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeCosetThreeSourceCorrection.three_source_projection_correction`
- Dependency: [D5/S3/VertexAlgebra/Sectors/LatticeCosetOperatorCorrection](LatticeCosetOperatorCorrection.md)
