# Covariance of frozen macroscopic lengths

## Abstract

Freezing and fixed block limits give the weighted overlap covariance of macroscopic lengths.

Let E be measurable and bounded on every compact interval, with D_v(x)=E(x+v)-E(x). Assume 0<alpha<theta<beta<1 and that V(Y,v)/(Y*v*log(Y/v)) tends uniformly to one for Y^alpha<=v<=Y^beta. Set h=X^theta, N=X*h*log(X), kappa=1-theta, u_j=1+j/n and I_j=[u_j*X,u_(j+1)*X], where n is a fixed positive integer. The length values a(u_j) and b(u_j) lie in [0,M] for some M>0; w(u_j) are arbitrary real weights. Only these finitely many values are used, so no continuity is required.

**Theorem 1.1 (Weighted covariance on fixed blocks).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/MacroscopicWeightedCovariance.fixed_block_covariance_tendsto`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/MacroscopicWeightedCovariance.fixed_block_covariance_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

As X tends to infinity, the sum over j<n of w(u_j) times the integral on I_j of D_(h*a(u_j))*D_(h*b(u_j)), divided by N, tends to (kappa/n) times the sum of w(u_j)*min(a(u_j),b(u_j)).

Apply fixed_length_covariance_tendsto with the common length M*X^theta and parameters a(u_j)/M and b(u_j)/M in [0,1]. The ratio of its normalizer X*(M*X^theta)*log(X/(M*X^theta)) to N tends to M*kappa. Since each block has macroscopic length 1/n, multiplication by this ratio and finite summation give the stated limit. The fixed-length theorem includes zero parameters, so zero lengths require no separate argument.

**Theorem 1.2 (Frozen squared norms).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/MacroscopicWeightedCovariance.fixed_block_square_tendsto`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/MacroscopicWeightedCovariance.fixed_block_square_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sum over j<n of the integrals on I_j of D_(h*a(u_j))^2, divided by N, tends to (kappa/n) times the sum of a(u_j). This is the weighted covariance limit with b=a and all weights equal to one.

**Theorem 1.3 (Size of the squared norm limit).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/MacroscopicWeightedCovariance.fixed_block_square_limit_mem`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/MacroscopicWeightedCovariance.fixed_block_square_limit_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If every frozen length lies in [0,M], then (kappa/n) times their sum lies in [0,M]. Indeed, 0<kappa<1 and the sum of n such lengths lies between zero and n*M.

**Theorem 1.4 (A weighted product bound).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/MacroscopicWeightedCovariance.young_abs`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/MacroscopicWeightedCovariance.young_abs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real x and y and every positive r, |x*y| is at most x^2/r+r*y^2. The elementary quadratic inequality controls both freezing errors and changes in the two time parameters.

**Theorem 1.5 (Continuous macroscopic weights and lengths).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/MacroscopicWeightedCovariance.weighted_covariance_tendsto`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/MacroscopicWeightedCovariance.weighted_covariance_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonnegative C1 functions a and b on [1,2] and a real continuous weight w, the integral of w(x/X)*D_(X^theta*a(x/X))(x)*D_(X^theta*b(x/X))(x), divided by X*X^theta*log(X), tends to kappa times the integral of w(u)*min(a(u),b(u)) on [1,2].

Compactness supplies common length and derivative bounds M and L. On n equal blocks freeze a, b and w at the left endpoints. The difference of the weighted products splits into the weight error and the two freezing errors. Young's inequality bounds their block integrals by the squared freezing errors and squared increment norms. The uniform bound 880*M controls the moving norms, while the fixed block square limit controls the frozen norm. Uniform continuity controls the weight error and the overlap Riemann sum. For each positive tolerance choose n once, then let X tend to infinity; the proof does not choose n as a function of X.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/MacroscopicWeightedCovariance.fixed_block_covariance_tendsto`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/MacroscopicWeightedCovariance.fixed_block_square_limit_mem`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/MacroscopicWeightedCovariance.fixed_block_square_tendsto`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/MacroscopicWeightedCovariance.weighted_covariance_tendsto`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/MacroscopicWeightedCovariance.young_abs`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/FixedLengthCovariance](FixedLengthCovariance.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/MacroscopicFreezing](MacroscopicFreezing.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/MacroscopicVarianceDefs](MacroscopicVarianceDefs.md)
- Dependency: [D5/S3/Combinatorics/Permanental/CycleGeodesic/CycleGeodesicScaling](../../../Combinatorics/Permanental/CycleGeodesic/CycleGeodesicScaling.md)
