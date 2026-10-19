# OriginalFirstClockBufferEstimates

## Abstract

Consumed estimates for the original first-clock prime buffer

These are auxiliary estimates consumed on the live proof path of OriginalFirstClockTransport.good_edge_prime_buffer. They are moved from that owner to keep its source within the repository capacity limit. The density is the unchanged ActualRobinClockCovariance.activationDensity w(x)=(log(x)+1)/(x^2*log(x)^2). No second density or integer objective is defined.

**Theorem 1.1 (Logarithms near an original endpoint).**

Lean statement: `D5/S3/Arith/Robin/OriginalFirstClockBufferEstimates.buffer_log_size`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/OriginalFirstClockBufferEstimates.buffer_log_size` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real x>=256 and x-2<=z<=x+1, one has 5<log(z)<=x/20. Both endpoint exclusion proofs use this estimate at z=q, with h=log(q).

**Theorem 1.2 (Backward density comparison).**

Lean statement: `D5/S3/Arith/Robin/OriginalFirstClockBufferEstimates.buffer_density_left`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/OriginalFirstClockBufferEstimates.buffer_density_left` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real x>=256 and 0<h<=x/20, (81/100)*w(x-h)<=w(x). The original lower-end deletion argument consumes this comparison.

**Theorem 1.3 (Strict forward density comparison).**

Lean statement: `D5/S3/Arith/Robin/OriginalFirstClockBufferEstimates.buffer_density_right`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/OriginalFirstClockBufferEstimates.buffer_density_right` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real x>=256 and 0<h<=x/20, (81/100)*w(x)<w(x+h). The original upper-end insertion argument consumes the strict inequality.

**Theorem 1.4 (Integer removal from a literal nonlinear objective comparison).**

Lean statement: `D5/S3/Arith/Robin/OriginalFirstClockBufferEstimates.buffer_integer_removal_comparison`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/OriginalFirstClockBufferEstimates.buffer_integer_removal_comparison` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let M>=1, q be prime, and M*q=N. Assume the literal inequality log(sigma(M)/M)-log(log(log(M))) <= log(sigma(N)/N)-log(log(log(N))). Then log(log(log(N)))-log(log(log(M)))<=log(1+1/q). The existing exact single-layer delta and decrease of Euler marginals prove the estimate with arbitrary multiplicity of q. The original consumer supplies this input inequality from full maximality on the 5040*p class and its legal competitor M; no forced divisibility condition is removed from the good-edge theorem.

All four public helpers are actually consumed by the original endpoint exclusions. The complete good_edge_prime_buffer theorem remains in its original owner with its full hypotheses, original GoodEdge and 5040. This structural split adds no Robin or RH conclusion and makes no literature novelty claim.

## References

- Truth anchor: `D5/S3/Arith/Robin/OriginalFirstClockBufferEstimates.buffer_density_left`
- Truth anchor: `D5/S3/Arith/Robin/OriginalFirstClockBufferEstimates.buffer_density_right`
- Truth anchor: `D5/S3/Arith/Robin/OriginalFirstClockBufferEstimates.buffer_integer_removal_comparison`
- Truth anchor: `D5/S3/Arith/Robin/OriginalFirstClockBufferEstimates.buffer_log_size`
- Dependency: [D5/S3/Arith/GoldenResource/FirstLayerMarginalAntitone](../GoldenResource/FirstLayerMarginalAntitone.md)
- Dependency: [D5/S3/Arith/GoldenResource/GoldenResource5040EndpointComparison](../GoldenResource/GoldenResource5040EndpointComparison.md)
- Dependency: [D5/S3/Arith/Robin/ActualRobinClockCovariance](ActualRobinClockCovariance.md)
