# Brownian pairings and kurtosis

## Abstract

The fourth Brownian pairing integral and strict dyadic excess kurtosis.

Let g be a real measurable integrable profile on the unit interval. Its quadratic energy Q(g) is the double integral of g(s)g(t)min(s,t). The fourth Brownian kernel is the sum of the three products min(s0,s1)min(s2,s3), min(s0,s2)min(s1,s3), and min(s0,s3)min(s1,s2).

**Definition 1.1 (Profile-weighted Brownian pair).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/BrownianFourthKernel.pairKernel`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/BrownianFourthKernel.pairKernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a real profile g and two coordinates s0,s1, pairKernel is g(s0)g(s1)min(s0,s1), the profile-weighted Brownian covariance kernel.

**Theorem 1.2 (Integrability of a profile pair).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/BrownianFourthKernel.pairKernel_integrable`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/BrownianFourthKernel.pairKernel_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every measurable integrable real profile g on the unit interval, g(s)g(t)min(s,t) is integrable on the unit square.

**Theorem 1.3 (Integral of a profile pair).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/BrownianFourthKernel.integral_pairKernel`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/BrownianFourthKernel.integral_pairKernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every measurable integrable real profile g on the unit interval, the integral of g(s)g(t)min(s,t) over the unit square equals Q(g).

**Theorem 1.4 (Factorization over disjoint coordinate pairs).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/BrownianFourthKernel.pair_product_integrable_and_integral`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/BrownianFourthKernel.pair_product_integrable_and_integral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let F and H be integrable real functions on the unit square, and let e be any permutation of the four coordinates. The function F(s(e(0)),s(e(1)))H(s(e(2)),s(e(3))) is integrable on the unit four-cube, and its integral is the product of the integrals of F and H.

**Theorem 1.5 (Integral of the fourth Brownian kernel).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/BrownianFourthKernel.brownianW4_integral`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/BrownianFourthKernel.brownianW4_integral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The integral of the product of the four profile values times the fourth Brownian kernel over the unit cube equals 3Q(g)^2. The min kernel is bounded by one on the unit square, so each pairing is absolutely integrable. Measure-preserving coordinate permutations reduce all three pairings to two independent copies of the min-kernel integral. Fubini then gives Q(g)^2 for each pairing.

**Theorem 1.6 (Strict excess kurtosis).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/BrownianFourthKernel.three_lt_kurtosis_ratio`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/BrownianFourthKernel.three_lt_kurtosis_ratio` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every kappa>0, the ratio 3*kappa*(2^(2*kappa)-1)*log(2)/(2*(2^kappa-1)^2) is strictly greater than three. For U with density du/(u*log(2)) on [1,2], strict positive covariance of the positive powers U^kappa and U^kappa gives E[U^(2*kappa)]>E[U^kappa]^2. Evaluating these power moments gives the displayed ratio.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/BrownianFourthKernel.brownianW4_integral`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/BrownianFourthKernel.integral_pairKernel`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/BrownianFourthKernel.pairKernel`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/BrownianFourthKernel.pairKernel_integrable`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/BrownianFourthKernel.pair_product_integrable_and_integral`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/BrownianFourthKernel.three_lt_kurtosis_ratio`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/DyadicMacroMoments](DyadicMacroMoments.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/MomentTransferDefs](MomentTransferDefs.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/TriangularMeanSquare](TriangularMeanSquare.md)
