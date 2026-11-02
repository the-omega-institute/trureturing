# Moment Orthogonal Complex L2 Primitive Gap

## Abstract

Vanishing low moments give a quantitative primitive energy gap for arbitrary complex L2 input.

**Theorem 1.1 (The original interval, complex L2 domain and constant).**

Lean statement: `D5/S3/Analytic/MomentOrthogonalPrimitiveGap.complex_L2_moment_primitive_gap`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/MomentOrthogonalPrimitiveGap.complex_L2_moment_primitive_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real D>0, every natural q>=1, and every function A from the reals to the complex numbers that belongs to L2 for volume restricted to the closed interval [0,D], assume that the integral of x^r A(x) vanishes for every natural r<q. Define V(x) as the Bochner interval integral of A from zero to x. The exact target is integral_[0,D] norm(V)^2 <= D^2/(4 q(q+1)) integral_[0,D] norm(A)^2. The zero function, arbitrary complex phases, all finite q and merely L2 representatives are included. There is no polynomial, continuity, real-valuedness or assumed spectral-expansion hypothesis.

On [0,1], reuse PolynomialL2Derivative.legendreC, its actual coefficient formula, finite expansion and expansion_parseval. The existing normalization is integral norm(L_n)^2=1/(2n+1). The finite inverse Sturm construction uses the spanning and mixed expansion identities and the finite primitive estimate proved in LegendrePrimitiveGap.

Set w=x(1-x) and T(p)=-(w p')'. The coefficient calculation gives coeff_k(Tp)=k(k+1) coeff_k(p)-(k+1)^2 coeff_(k+1)(p). The two binomial recurrences in Mathlib imply T(L_n)=n(n+1)L_n, including n=0 and coefficients outside the degree range. For a finite high-mode expansion A=sum_(n<d) a_n L_n, with a_n=0 for n<q, set F=sum a_n/(n(n+1)) L_n. The formal division by zero at n=0 is harmless because its coefficient is zero; every used high eigenvalue is positive since q>=1. Then T(F)=A and V=-w F'.

Integration by parts, with w vanishing at both endpoints, gives integral w norm(F')^2=integral A conjugate(F). Expanding the right side using the existing moment helpers gives sum norm(a_n)^2/((2n+1)n(n+1)). The bound 0<=w<=1/4 gives integral norm(V)^2 <= (1/4) integral w norm(F')^2. Finally n(n+1)>=q(q+1) on high modes and the reused Parseval identity give the claimed unit-interval constant. Conjugation is retained throughout this calculation.

For a general L2 input, the raw density argument first uses MemLp.exists_boundedContinuous_integral_rpow_sub_le and then applies real Weierstrass approximation separately to the real and imaginary parts. Corrected density removes the first q Legendre coordinates and shows that this correction does not increase the error from A: the vanished moments make A orthogonal to that span, so the removed terms are its finite orthogonal projection. Finite Parseval for polynomials alone does not establish this join.

The integration operator is a bounded complex-linear primitive operator on the actual L2 quotient. Indicator inner-product Cauchy-Schwarz bounds norm(integral_0^x f) by norm(f) in L2([0,1]) for every x in [0,1]. The construction supplies measurability, square integrability, linearity and independence of representatives, using L2 indicator inner products. Continuity of the operator and squared L2 norm passes the finite inequality to A. The limit proof consumes both corrected density and primitive continuity.

Dilation uses B(t)=A(Dt), interval substitution and integrability of A and norm(A)^2. Its moment factor is D^(-(r+1)); E(B)=D^(-1)E(A); and E(primitive B)=D^(-3)E(V). These exact factors yield D^2 in the final bound. There is no measure-preservation assumption for the dilation.

This classical analytic estimate quantifies low-moment cancellation through the energy of the actual primitive. A sublinear m(D)=o(D) supplier and fixed-window coercivity for a specific kernel require further results. No literature novelty, scalar subexponential remainder, R-bound or RH claim follows from this estimate alone.

## References

- Truth anchor: `D5/S3/Analytic/MomentOrthogonalPrimitiveGap.complex_L2_moment_primitive_gap`
- Dependency: [D5/S3/Analytic/LegendrePrimitiveGap](LegendrePrimitiveGap.md)
