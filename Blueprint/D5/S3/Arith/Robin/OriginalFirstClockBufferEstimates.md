# OriginalFirstClockBufferEstimates

## Abstract

Consumed estimates for the original first-clock prime buffer

These estimates support OriginalFirstClockTransport.good_edge_prime_buffer. The density is ActualRobinClockCovariance.activationDensity w(x)=(log(x)+1)/(x^2*log(x)^2). The logarithm window bound is stated in LogarithmBounds.

**Theorem 1.1 (Backward density comparison).**

Lean statement: `D5/S3/Arith/Robin/OriginalFirstClockBufferEstimates.buffer_density_left`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/OriginalFirstClockBufferEstimates.buffer_density_left` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real x>=256 and 0<h<=x/20, (81/100)*w(x-h)<=w(x). The original lower-end deletion argument consumes this comparison.

**Theorem 1.2 (Strict forward density comparison).**

Lean statement: `D5/S3/Arith/Robin/OriginalFirstClockBufferEstimates.buffer_density_right`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/OriginalFirstClockBufferEstimates.buffer_density_right` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real x>=256 and 0<h<=x/20, (81/100)*w(x)<w(x+h). The original upper-end insertion argument consumes the strict inequality.

**Theorem 1.3 (Integer removal from a literal nonlinear objective comparison).**

Lean statement: `D5/S3/Arith/Robin/OriginalFirstClockBufferEstimates.buffer_integer_removal_comparison`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/OriginalFirstClockBufferEstimates.buffer_integer_removal_comparison` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let M>=1, q be prime, and M*q=N. Assume the literal inequality log(sigma(M)/M)-log(log(log(M))) <= log(sigma(N)/N)-log(log(log(N))). Then log(log(log(N)))-log(log(log(M)))<=log(1+1/q). The existing exact single-layer delta and decrease of Euler marginals prove the estimate with arbitrary multiplicity of q. The original consumer supplies this input inequality from full maximality on the 5040*p class and its legal competitor M; no forced divisibility condition is removed from the good-edge theorem.

The density comparisons and integer removal estimate support the endpoint exclusions with the full GoodEdge hypotheses and the 5040 threshold.

## References

- Truth anchor: `D5/S3/Arith/Robin/OriginalFirstClockBufferEstimates.buffer_density_left`
- Truth anchor: `D5/S3/Arith/Robin/OriginalFirstClockBufferEstimates.buffer_density_right`
- Truth anchor: `D5/S3/Arith/Robin/OriginalFirstClockBufferEstimates.buffer_integer_removal_comparison`
- Dependency: [D5/S3/Arith/GoldenResource/FirstLayerMarginalAntitone](../GoldenResource/FirstLayerMarginalAntitone.md)
- Dependency: [D5/S3/Arith/GoldenResource/GoldenResource5040EndpointComparison](../GoldenResource/GoldenResource5040EndpointComparison.md)
- Dependency: [D5/S3/Arith/Robin/ActualRobinClockCovariance](ActualRobinClockCovariance.md)
- Dependency: [D5/S3/Arith/Robin/LogarithmBounds](LogarithmBounds.md)
