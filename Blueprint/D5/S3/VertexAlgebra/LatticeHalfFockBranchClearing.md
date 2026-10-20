# Integer Gram Branch Clearing

## Abstract

Integral Gram pairings give exact clearing and reciprocity for both half-contraction branches.

Write g=bilinear D left right, p=g.toNat, n=(-g).toNat and N=g.natAbs=p+n. The inherited halfContraction is the product of the rescaled binomial series of g and the binomial series of -g. The cleared polynomial is P_g(t)=(1-t)^(2*p)*(1+t)^(2*n). All signed pairings, including g=0, remain in scope; no determinant-unit or positivity premise is used in this module.

**Theorem 1.1 (The two binomial branches clear with opposite exponents).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockBranchClearing.half_contraction_two_branch_clearing`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockBranchClearing.half_contraction_two_branch_clearing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplication of halfContraction by (1-t)^n*(1+t)^p gives (1-t)^p*(1+t)^n in PowerSeries C. Binomial-series addition, rescaling by -1 and the integer identities n+g=p and p-g=n prove the equality.

**Theorem 1.2 (The physical factor clears to the explicit polynomial).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockBranchClearing.half_contraction_physical_clearing`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockBranchClearing.half_contraction_physical_clearing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplication by (1-t^2)^N gives P_g.toPowerSeries. Factoring 1-t^2 into the two linear factors converts two-branch clearing into this identity, consumed by native_cleared_kernel_expansion.

**Theorem 1.3 (The cleared degree is at most twice the absolute pairing).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockBranchClearing.cleared_polynomial_degree`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockBranchClearing.cleared_polynomial_degree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every integer gram, clearedPolynomial gram has natDegree at most 2*gram.natAbs. ClearedKernel uses this upper bound to replace its coefficient expansion by the finite range from 0 through 2*N.

**Theorem 1.4 (Reflection at twice the absolute pairing preserves the polynomial).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockBranchClearing.cleared_polynomial_reciprocity`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockBranchClearing.cleared_polynomial_reciprocity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

P_g.reflect(2*N)=P_g. Reflection negates the factor 1-t, preserves 1+t, and the even exponent 2*p removes the sign. The proof uses degree bounds and polynomial reflection, uniformly in the sign of g.

**Theorem 1.5 (Complementary coefficients agree inside the cleared range).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockBranchClearing.cleared_polynomial_coefficient_reciprocity`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockBranchClearing.cleared_polynomial_coefficient_reciprocity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For degree at most 2*N, coefficient 2*N-degree of P_g equals coefficient degree. ClearedKernel consumes this coefficient consequence when reflecting the finite sum and exchanging the two branches.

**Theorem 1.6 (The clearing sign is the integral pairing parity).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockBranchClearing.physical_clearing_sign`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockBranchClearing.physical_clearing_sign` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every integer gram, (-1:C)^gram.natAbs=paritySign gram. PhysicalLocality consumes this parity identity to cancel the actual ground-action exchange sign.

These are repository-derived consequences of the existing half-contraction definition and polynomial/binomial-series APIs. They supply algebraic clearing and reciprocity, without asserting analytic branch convergence, a new literature theorem or the charged tensor locality endpoint on their own.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockBranchClearing.cleared_polynomial_coefficient_reciprocity`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockBranchClearing.cleared_polynomial_degree`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockBranchClearing.cleared_polynomial_reciprocity`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockBranchClearing.half_contraction_physical_clearing`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockBranchClearing.half_contraction_two_branch_clearing`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockBranchClearing.physical_clearing_sign`
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockChargedCoefficients](LatticeHalfFockChargedCoefficients.md)
