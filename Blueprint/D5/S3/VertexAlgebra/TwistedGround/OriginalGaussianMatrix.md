# Native Gaussian Finite-Section Operator-Norm Bound

## Abstract

Native Gaussian Finite-Section Operator-Norm Bound

For positive frequencies s,t, the native entry is pairScalar s t divided by the two square-root frequency factors and multiplied by z^(s+t). The finite section uses s=i.val+1 and t=j.val+1, so N=0 is an empty matrix and z=0 is handled directly.

The proof introduces the real central-binomial weights b_n=centralBinom(n)/4^n. Their recurrence gives the exact finite boundary induction for s*b_s times the partial sum of b_(t+1)/(s+t+1), and hence the weighted row estimate with p_s=1/sqrt(s) and eta=norm(z)^2. The radial matrix is Hermitian and the existing scaled complex quadratic-row bound supplies its Euclidean operator norm.

For z=rho*u with norm(u)=1, the phase is a two-sided diagonal unitary congruence D_u A(rho) D_u. Both unitary factors preserve the matrix norm. The finite-section theorem gives the uniform bound on the full complex open unit disk; the infinite operator, holomorphy, determinant, charge summability, occupation attribution and broader VOA/CFT/string/AdS-CFT goals remain outside this theorem.

The compiled Reg mirror intentionally leaves sourceSelection null and continuation unknown: the exact information-escape source audit is unresolved and compilation does not claim a registration certificate.

**Theorem 1.1 (finiteSection_opNorm_le).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianMatrix.finiteSection_opNorm_le`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianMatrix.finiteSection_opNorm_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every N and every complex z with norm(z)<1, the actual native finite-section matrix has Euclidean operator norm at most norm(z)^2.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianMatrix.finiteSection_opNorm_le`
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection](../LatticeHalfFockFiniteCorrection.md)
- Dependency: [D5/S3/Weil/ProjectiveRayleigh/ScaledComplexQuadraticRowBound](../../Weil/ProjectiveRayleigh/ScaledComplexQuadraticRowBound.md)
