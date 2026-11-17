# Moving differences on a larger interval

## Abstract

Moving differences on a larger interval.

**Theorem 1.1 (Moving differences on a larger interval).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/DyadicCovariancePairs.smooth_moving_difference_outer_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/DyadicCovariancePairs.smooth_moving_difference_outer_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 0<theta<1, one constant controls the moving difference u(x+s*x^theta)-u(x) for every s in [0,1] and every continuously differentiable u. On [X/2,4X], its L2 norm is bounded both by C*X^theta times the derivative norm and by C times the function norm on [X/4,8X]; its derivative norm is bounded by C times the derivative norm there. Apply the smooth estimates on the three adjacent dyadic intervals and add their square integrals.

**Theorem 1.2 (Pairing ordered block scales).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/DyadicCovariancePairs.dyadic_transfer_pair_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/DyadicCovariancePairs.dyadic_transfer_pair_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 0<a<1, let 0<R<=S<=X. Suppose u has L2 norm at most A*sqrt(R) and absolute value at most A on [X/2,4X], while the C1 function v has L2 norm at most A*sqrt(S), derivative norm at most A/sqrt(S), and absolute value at most A. The integral of (u(x+s*x^a)-u(x))*v(x) on every subinterval of [X,2X] is at most C*A^2*X^a in absolute value. The constant and the eventual threshold are independent of the functions, scales, interval, and s in [0,1]. The endpoint strips use the uniform bound for u.

**Theorem 1.3 (Pairing a small residual).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/DyadicCovariancePairs.residual_transfer_pair_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/DyadicCovariancePairs.residual_transfer_pair_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose the L2 norm of u is at most A*sqrt(X^a), the L2 norm of v is at most A*sqrt(k), its derivative norm is at most A/sqrt(X^a), and its absolute value is at most A*n, with n>=1 and sqrt(X^a)*sqrt(k)<=X. Uniformly on subintervals of [X,2X], the pairing of the short moving difference of u with v is at most C*A^2*X^a*n. Measurability and square integrability of u and C1 regularity of v are required on the working interval. The endpoint strips use the square norm of u.

**Theorem 1.4 (Pairing two smooth blocks).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/DyadicCovariancePairs.dyadic_block_covariance_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/DyadicCovariancePairs.dyadic_block_covariance_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let 0<a,b<1, and let two C1 functions have the smoothing-block norm, derivative, and uniform bounds at positive scales R and S at most X. Use bounds for the first function on [X/2,4X] and for the second on [X/4,8X]. The covariance of their moving differences on every subinterval of [X,2X] is at most C*A^2*X^a. For S<=R use the derivative bound on the short difference and Cauchy-Schwarz; for R<=S transfer that difference and use the uniform bounds on the endpoint strips. The estimate is independent of the ordering and separation of the scales.

**Theorem 1.5 (Square norms under an expanding moving map).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/DyadicCovariancePairs.measurable_moving_difference_l2_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/DyadicCovariancePairs.measurable_moving_difference_l2_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 0<theta<1, X>=4, and s in [0,1], a measurable square integrable u on [X/4,8X] has a square integrable moving difference on [X/2,4X]. Its L2 norm is at most twice the norm of u on the larger interval. The moving map has derivative at least one and its image stays inside that larger interval, so change of variables contracts the square integral.

**Theorem 1.6 (Long differences at the terminal scale).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/DyadicCovariancePairs.terminal_moving_difference_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/DyadicCovariancePairs.terminal_moving_difference_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let 0<b<1, K>=X^b, and u be C1. If its derivative has L2 norm at most A/sqrt(K) and absolute value at most A/K on [X/4,8X], then the long moving difference has L2 norm at most C*A*sqrt(K), derivative norm at most C*A/sqrt(K), and absolute value at most C*A on [X/2,4X]. The constant is uniform in K, A, u, and t in [0,1]. The pointwise estimate integrates the derivative between the two endpoints.

**Theorem 1.7 (Summing a finite covariance decomposition).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/DyadicCovariancePairs.finite_covariance_expansion_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/DyadicCovariancePairs.finite_covariance_expansion_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose an integrand is the sum of three individual terms, N terminal-block terms, and N squared block-pair terms. If the respective absolute integrals are bounded by B0, B1, B2, B3, and B4, then the absolute integral of the sum is at most B0+B1+B2+N*B3+N^2*B4. Every term is interval integrable. Finite-sum linearity and the triangle inequality retain all terms, including N=0 and degenerate intervals.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/DyadicCovariancePairs.dyadic_block_covariance_bound`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/DyadicCovariancePairs.dyadic_transfer_pair_bound`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/DyadicCovariancePairs.finite_covariance_expansion_bound`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/DyadicCovariancePairs.measurable_moving_difference_l2_bound`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/DyadicCovariancePairs.residual_transfer_pair_bound`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/DyadicCovariancePairs.smooth_moving_difference_outer_bounds`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/DyadicCovariancePairs.terminal_moving_difference_bounds`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/DyadicDecomposition](DyadicDecomposition.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/SmoothMovingDifference](SmoothMovingDifference.md)
