# The full arithmetic surplus

## Abstract

Full prime-power compensation for arbitrary positive valuations on the exact initial prime support.

**Theorem 1.1 (A strict lower bound without a containment hypothesis).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/FullPrimePowerArithmeticSurplus.full_prime_power_arithmetic_surplus`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/FullPrimePowerArithmeticSurplus.full_prime_power_arithmetic_surplus` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real z>=4 and positive integer n with primeFactors(n)=primesLE(floor(z)), tail(n)+(log(n)-Chebyshev.psi(z))/(z*log(z))-fullPrimePowerResidual(z) strictly exceeds log(2)/(6*z*log(z)). No assumption requires n to contain every prime power up to z. The residual is the literal finite sum over primes p<=z of the full infinite sum of p^(-k)/k for k>=2 and z<p^k. Equality p^k=z remains in psi, and is excluded from the residual.

The exact floor cutoff agrees with the integer logarithm. Summability is proved before reindexing each complete residual as a shifted tail; the default value of a nonsummable real tsum is never used. The factorization identity writes log(n)-psi(z) as a signed sum of actual valuation minus cutoff valuation. For filled inventories, additional copies pay their cutoff price. For underfilled inventories, writing b=a+1+e and using e+1<=2^e lets the larger actual Euler tail pay both the signed missing-copy cost and the whole geometric reference tail. The prime two supplies the strict global constant; every other prime contribution is positive.

This proof reuses OriginalEndpointPrimeTail.tail and layerTail, Mathlib's exact Chebyshev psi/factorization identities, geometric-series results, and logarithm bounds. It integrates the completed stronger arbitrary-inventory source of 2026-11-06; the earlier restricted proof remains valid under its additional containment assumption and is not evidence for this stronger statement. The curvature consumer uses this stronger theorem with no containment premise. This is a finite-state arithmetic inequality, with no signed-integral identity, J-sign conclusion, RH conclusion, or literature novelty claim.

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/FullPrimePowerArithmeticSurplus.full_prime_power_arithmetic_surplus`
- Dependency: [D5/S3/Arith/Robin/OriginalEndpointPrimeTail](../OriginalEndpointPrimeTail.md)
