# Uniform freezing of macroscopic lengths

## Abstract

Uniform freezing of macroscopic lengths

**Theorem 1.1 (Eventual macroscopic scale conditions).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/MacroscopicFreezing.scale_conditions`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/MacroscopicFreezing.scale_conditions` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume 0<alpha<theta<beta<1, c>0, M>0, L>=0 and delta>0. For all sufficiently large X, one has X>=4, M*X^theta<=X, L*X^theta/X<=1/2, (4X)^alpha<=c*X^theta, 4*c*X^theta<=(X/2)^beta, and M*X^theta/X<delta. These bounds depend on the constants and exponents, so the same threshold applies to every length function satisfying the corresponding size and derivative bounds.

**Theorem 1.2 (Finite freezing error).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/MacroscopicFreezing.freezing_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/MacroscopicFreezing.freezing_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let M>=1, L>=0 and n>0. A nonnegative C1 length a on [1,2], bounded by M with derivative bounded by L, is frozen at the left endpoints of n equal blocks. Under the window variance bound and the stated scale inequalities, the sum of squared block errors divided by X*X^theta*log(X) is at most 120*(1+L)*(1/n+M*X^theta/X)+640*(1+L)*epsilon. The mean value inequality bounds each endpoint gap by L*X^theta/n, and the local endpoint estimate retains each block length X/n+M*X^theta.

**Theorem 1.3 (Uniform eventual freezing error).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/MacroscopicFreezing.freezing_eventually`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/MacroscopicFreezing.freezing_eventually` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the qualitative variance-band asymptotic, fix M>=1, L>=0 and n>0. For every eta>0, all sufficiently large X simultaneously satisfy freezingError<=120*(1+L)/n+eta for every nonnegative C1 length a bounded by M with derivative bounded by L. The threshold precedes the choice of a. The power-band conditions hold eventually, the macroscopic scale ratio tends to zero, and the window error can be chosen arbitrarily small.

**Theorem 1.4 (Uniform square bound).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/MacroscopicFreezing.normalized_square_eventually`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/MacroscopicFreezing.normalized_square_eventually` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the variance-band asymptotic, fix M>=1 and L>=0. For all sufficiently large X, every nonnegative C1 length a bounded by M with derivative bounded by L has normalized square integral at most 880*M. Apply the same endpoint comparison on the whole dyadic interval with frozen length zero, gap bound M*X^theta, and window error at most one.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/MacroscopicFreezing.freezing_bound`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/MacroscopicFreezing.freezing_eventually`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/MacroscopicFreezing.normalized_square_eventually`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/MacroscopicFreezing.scale_conditions`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/FixedLengthCovariance](FixedLengthCovariance.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/LocalVarianceBand](LocalVarianceBand.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/MacroscopicEndpointGeometry](MacroscopicEndpointGeometry.md)
