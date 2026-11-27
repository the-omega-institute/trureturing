# Optimal order of the compact loss

## Abstract

The quadratic scale of the original compact compression loss is necessary.

**Definition 1.1 (The excess at the singleton window).**

Lean statement: `D5/S3/Arith/FactorialRatio/Compression/OptimalLoss.endpointExcess`

*Formalization.* `D5/S3/Arith/FactorialRatio/Compression/OptimalLoss.endpointExcess` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Set r=n+1 and s=n. The only legal integer parameter is b=0, so the compact gcd is (n!)^(n+1). The tail has degree n(n+2) and cutoff n. For n>=1 the tail divides this gcd, and endpointExcess is the resulting positive integer quotient.

**Theorem 1.2 (The exact limiting constant).**

Lean statement: `D5/S3/Arith/FactorialRatio/Compression/OptimalLoss.endpoint_loss_tendsto`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/Compression/OptimalLoss.endpoint_loss_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

As n tends to infinity through the natural numbers, log(endpointExcess(n))/(n+1)^2 tends to the Euler-Mascheroni constant gamma. Thus log E=gamma r^2+o(r^2) along s=r-1. Since gamma>1/2, a uniform loss estimate o(r^2) over the original compact windows is impossible.

The exact finite tail estimate compares its centered logarithm D(n+2,n) with the complete Mangoldt error U(n+2). Their difference lies between zero and psi(n+2)/n. The bound psi(y)<=(log 4+4)y makes this difference negligible after division by n+1. The weighted Mangoldt limit sum_{m<=y} Lambda(m)/m-log y -> -gamma and the prime number theorem psi(y)/y -> 1 give U(y)/y -> 0.

For the numerator, the logarithmic factorial bounds leave an error at most log(n+2)+1 beyond n log n-n. The remaining logarithmic terms are multiples of log(n/(n+2)) and log(n+2)/(n+1), both tending to zero. The constant term left by the tail normalization is gamma.

## References

- Truth anchor: `D5/S3/Arith/FactorialRatio/Compression/OptimalLoss.endpointExcess`
- Truth anchor: `D5/S3/Arith/FactorialRatio/Compression/OptimalLoss.endpoint_loss_tendsto`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/CompactQuarticBridge](../../../Weil/Mertens/IntegratedExplicit/CompactQuarticBridge.md)
- Dependency: [D5/S3/Weil/Mertens/WeightedPrimeLimit](../../../Weil/Mertens/WeightedPrimeLimit.md)
