# Polynomial growth of the Mellin remainder

## Abstract

Polynomial growth of the Mellin remainder.

**Theorem 1.1 (A fixed compact interval for the adjoint).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/FiniteMellin.adjointKernel_eq_fixed`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/FiniteMellin.adjointKernel_eq_fixed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If both the starting center x0 and evaluation point t are at most b, the Mellin adjoint equals its center integral on [x0,b]. The kernel vanishes for larger centers. This representation bounds the initial corrections uniformly throughout a vertical strip.

**Theorem 1.2 (Integrability on bounded intervals of centers).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/MellinResidue.forwardResponse_compact_integrable`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/MellinResidue.forwardResponse_compact_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the complete Chebyshev error is eventually bounded by a nonnegative real power, the complete forward response is integrable on every compact interval whose lower endpoint is at least three. The global power estimate for the response supplies an integrable continuous majorant on that interval.

**Theorem 1.3 (The explicit common remainder).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/MellinResidue.forward_kernel_mellin_explicit_remainder`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/MellinResidue.forward_kernel_mellin_explicit_remainder` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For x0 at least three, put y=max(4,x0) and a=max(9,endpoint(y)). The remainder is the Mellin integral of the response on [x0,y], plus the finite signed correction at a, minus E(a)r_s(a), minus the integral of E(t)r_s'(t) on (a,infinity). Under an eventual power bound with exponent alpha, this same function is holomorphic on Re(s)>alpha-7/10 and gives the Mellin identity on Re(s)>max(1/2,alpha-3/10). Its formula does not depend on alpha.

**Theorem 1.4 (Quadratic growth in closed vertical strips).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/MellinPolynomialGrowth.forward_kernel_mellin_polynomial_remainder`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/MellinPolynomialGrowth.forward_kernel_mellin_polynomial_remainder` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume |psi(t)-t| is eventually bounded by C sqrt(t) log(t)^2. For every x0 at least three, one common explicit remainder R is holomorphic on Re(s)>-1/5 and satisfies F(s)=-zeta'(s+1/2)/(2 zeta(s+1/2))-1/(2(s-1/2))+R(s) for Re(s)>1/2. For each margin delta strictly between zero and one fifth, R(s) is bounded by C_delta(1+|Im(s)|)^2 whenever -1/5+delta<=Re(s)<=1. Relative powers and their time derivatives have strip bounds independent of the imaginary part except for the indicated polynomial factors. Compact contributions are uniformly bounded using the real part of each Mellin exponent. A small positive power absorbs the logarithmic factors in the Chebyshev error and gives an integrable majorant for the tail. All half-plane and strip estimates concern the same explicit R.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/FiniteMellin.adjointKernel_eq_fixed`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/MellinPolynomialGrowth.forward_kernel_mellin_polynomial_remainder`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/MellinResidue.forwardResponse_compact_integrable`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/MellinResidue.forward_kernel_mellin_explicit_remainder`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/MellinResidue](MellinResidue.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/StripAsymptotic](StripAsymptotic.md)
