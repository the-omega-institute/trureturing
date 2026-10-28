# Actual Integer Logarithmic Envelope

## Abstract

A fixed-price integer comparator removes the large-prime split error in the actual Robin objective.

**Theorem 1.1 (A finite prime-support bound for the actual sigma ratio).**

Lean statement: `D5/S3/Arith/Robin/ActualIntegerLogEnvelope.supported_sigma_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ActualIntegerLogEnvelope.supported_sigma_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive natural integer U and every real x, if each prime factor p of U satisfies p<=x, then sigma(1,U)/U is at most the product of (1-1/p)^(-1) over primes in the natural interval (0,floor(x)]. Prime-power reconstruction and the multiplicative sigma formula express the ratio as finite geometric factors. Each factor is bounded by (1-1/p)^(-1); GronwallUpperEnvelope.small_prime_product_le pads the product to the full prime interval.

The coefficient-two envelope applies this bound to its positive fixed-price comparator U. AbundancyRecord5040.large_prime_of_abundancy applies it directly with U=m and x=30: if every prime factor is at most thirty, padding further to all integers from two through thirty telescopes to thirty, contradicting sigma(1,m)/m>30.

**Theorem 1.2 (An arbitrary positive inventory error).**

Lean statement: `D5/S3/Arith/Robin/ActualIntegerLogEnvelope.eventual_actual_integer_envelope_epsilon`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ActualIntegerLogEnvelope.eventual_actual_integer_envelope_epsilon` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every epsilon>0 there is A>=286 such that every positive actual integer n with log(n)>=A satisfies F(n)-gamma<=(19/10+epsilon)/log(log(n)). The comparator has strict layer counts at price 1/(X*log(X)), X=log(n). Its uniform inventory growth gives 1-log(U)/X<=epsilon. The exact fixed-price cost difference is (1-log(U)/X)/log(X). Combining this with the effective prime-product coefficient 19/10 proves the bound. Only U has smooth support. The coefficient-two theorem takes epsilon=1/10; ActualLeastCrossingPriceRecord takes epsilon=1/20 directly.

**Theorem 1.3 (An unconditional coefficient-two bound for every sufficiently large integer).**

Lean statement: `D5/S3/Arith/Robin/ActualIntegerLogEnvelope.eventual_actual_integer_envelope`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ActualIntegerLogEnvelope.eventual_actual_integer_envelope` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There is a real A>=286 such that every positive natural integer n with A<=log(n) satisfies originalObjective(n)-gamma<=2/log(log(n)). Here originalObjective(n)=log(sigma(1,n)/n)-log(log(log(n))) and gamma is the Euler-Mascheroni constant. The integer n is arbitrary; no smoothness or optimality assumption is imposed on it.

Put X=log(n) and lambda=1/(X*log(X)). The actual positive integer U from GoldenResourceOptimalLayerCount.optimal_layer_count_spec has the strict exponent counts at lambda and maximizes W(k)-lambda*log(k) over all positive natural integers k, where W(k)=log(sigma(1,k)/k). EulerLayerInventoryGrowth.active_power_bound, at the first layer, implies every prime factor of U is less than X. Only this comparator uses the support bound. The full finite geometric Euler factors, padded by GronwallUpperEnvelope.small_prime_product_le, then give sigma(1,U)/U at most the reciprocal prime product up to X.

MertensExplicitEnvelope.prime_product_upper_effective supplies W(U)<=gamma+log(log(X))+19/(10*log(X)). The uniform strict-inventory growth theorem with epsilon=1/10 gives 1-log(U)/X<=1/10. Global fixed-price comparison transfers the bound to n and adds at most 1/(10*log(X)), yielding coefficient two. All prime powers in U are retained. This deduction combines the existing arithmetic inputs without a literature priority claim. In ActualIntegerHeightJump the bound is applied at the actual divisor m/q, after proving its size.

The estimate is unconditional and uses the existing unconditional MediumPNT through strict-inventory growth. It proves neither Robin's inequality nor RH, and supplies no signed upper bound or bounded-height cofinal envelope.

## References

- Truth anchor: `D5/S3/Arith/Robin/ActualIntegerLogEnvelope.supported_sigma_bound`
- Truth anchor: `D5/S3/Arith/Robin/ActualIntegerLogEnvelope.eventual_actual_integer_envelope`
- Truth anchor: `D5/S3/Arith/Robin/ActualIntegerLogEnvelope.eventual_actual_integer_envelope_epsilon`
- Dependency: [D5/S3/Arith/Robin/EulerLayerInventoryGrowth](EulerLayerInventoryGrowth.md)
- Dependency: [D5/S3/Arith/Robin/MertensExplicitEnvelope](MertensExplicitEnvelope.md)
- Dependency: [D5/S3/Arith/Robin/OriginalFirstClockTransport](OriginalFirstClockTransport.md)
