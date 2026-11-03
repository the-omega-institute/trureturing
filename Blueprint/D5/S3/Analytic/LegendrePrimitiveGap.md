# Finite Legendre Primitive Energy Gap

## Abstract

An inverse weighted Sturm construction bounds the actual primitive of a complex high-mode Legendre expansion.

**Theorem 1.1 (Hermitian pairing of finite expansions).**

Lean statement: `D5/S3/Analytic/LegendrePrimitiveGap.mixed_expansion`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/LegendrePrimitiveGap.mixed_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural d and arbitrary complex coefficient sequences a,b, the bilinear moment of expansion(d,a) and the coefficient conjugate of expansion(d,b) equals sum_(n<d) a_n conjugate(b_n)/(2n+1). This finite moment identity is used both in inverse weighted energy and in the low/high orthogonality of corrected approximation.

**Theorem 1.2 (The finite inverse Sturm energy estimate).**

Lean statement: `D5/S3/Analytic/LegendrePrimitiveGap.complex_legendre_primitive_gap`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/LegendrePrimitiveGap.complex_legendre_primitive_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural d,q with q>=1 and every complex coefficient sequence a satisfying a_n=0 for all n<q, let p be sum_(n<d) a_n L_n. The integral over [0,1] of the squared norm of the actual interval primitive of p is at most 1/(4q(q+1)) times the squared L2 norm of p. No relation between d and q is imposed, and the empty expansion is included.

For w=x(1-x), the coefficient recurrence proves -(w L_n')'=n(n+1)L_n. Dividing each high coefficient by this positive eigenvalue constructs F with -(w F')'=p. Both flux endpoints vanish. Integration by parts gives integral w norm(F')^2 equal to sum norm(a_n)^2/((2n+1)n(n+1)). The bound 0<=w<=1/4 then bounds primitive energy. Eigenvalue monotonicity and the existing exact finite Parseval identity finish the estimate. The infinite-dimensional extension is proved in MomentOrthogonalPrimitiveGap. There is no sublinear supplier or RH claim.

## References

- Truth anchor: `D5/S3/Analytic/LegendrePrimitiveGap.complex_legendre_primitive_gap`
- Truth anchor: `D5/S3/Analytic/LegendrePrimitiveGap.mixed_expansion`
- Dependency: [D5/S3/Analytic/PolynomialL2Derivative](PolynomialL2Derivative.md)
