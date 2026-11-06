# The full arithmetic surplus

## Abstract

Full prime-power compensation for arbitrary positive valuations on the exact initial prime support.

**Theorem 1.1 (An explicit bound for every real cutoff at least four).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/FullPrimePowerArithmeticSurplus.full_prime_power_arithmetic_surplus_root_scale`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/FullPrimePowerArithmeticSurplus.full_prime_power_arithmetic_surplus_root_scale` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For EVERY real z>=4 and positive integer n with primeFactors(n)=primesLE(floor(z)), the unchanged full signed arithmetic surplus exceeds 1/(2000*sqrt(z)*log(z)). No optimizer, eventual threshold, containment of powers, exponent-one, or desired sign premise is imposed. Mathlib theta_ge supplies the explicit theta(x)>x/4 estimate for x>=4096. For z>=16384 the actual strict/inclusive band 2*sqrt(z)<p<=32*sqrt(z) has logarithmic mass greater than 4*sqrt(z). Each positive actual valuation pays more than p^(-2)/3, using the actual logarithmic price when its exponent is at least two. Outside the band the signed-inventory positivity proof is reused. The previously proved log(2) bound covers 4<=z<=16384. These classical square-root correction estimates carry no novelty or RH claim.

**Theorem 1.2 (The exact complete Mangoldt and Euler ledger).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/FullPrimePowerArithmeticSurplus.complete_mangoldt_add_E3_eq_neg_residual`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/FullPrimePowerArithmeticSurplus.complete_mangoldt_add_E3_eq_neg_residual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real z>=4, Mertens.E2Lambda(z)+Mertens.E3(z)=-fullPrimePowerResidual(z). The generic finite prime-power reindex is converted to the exact cutoff-filtered prime prefix without enlarging a sum by an inequality. The genuinely summable complete Euler logarithm is split at its exact cutoff exponent, and the whole shifted remainder is identified with the existing strict z<p^k residual. Equality p^k=z remains in the prefix. The actual Mertens gamma normalization is used; no convergence, normalization, or residual identity is assumed.

**Theorem 1.3 (A strict lower bound without a containment hypothesis).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/FullPrimePowerArithmeticSurplus.full_prime_power_arithmetic_surplus`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/FullPrimePowerArithmeticSurplus.full_prime_power_arithmetic_surplus` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real z>=4 and positive integer n with primeFactors(n)=primesLE(floor(z)), tail(n)+(log(n)-Chebyshev.psi(z))/(z*log(z))-fullPrimePowerResidual(z) strictly exceeds log(2)/(6*z*log(z)). No assumption requires n to contain every prime power up to z. The residual is the literal finite sum over primes p<=z of the full infinite sum of p^(-k)/k for k>=2 and z<p^k. Equality p^k=z remains in psi, and is excluded from the residual.

The exact floor cutoff agrees with the integer logarithm. Summability is proved before reindexing each complete residual as a shifted tail; the default value of a nonsummable real tsum is never used. The factorization identity writes log(n)-psi(z) as a signed sum of actual valuation minus cutoff valuation. For filled inventories, additional copies pay their cutoff price. For underfilled inventories, writing b=a+1+e and using e+1<=2^e lets the larger actual Euler tail pay both the signed missing-copy cost and the whole geometric reference tail. The prime two supplies the strict global constant; every other prime contribution is positive.

This proof reuses OriginalEndpointPrimeTail.tail and layerTail, Mathlib's exact Chebyshev psi/factorization identities, geometric-series results, and logarithm bounds. It integrates the completed stronger arbitrary-inventory source of 2026-11-06; the earlier restricted proof remains valid under its additional containment assumption and is not evidence for this stronger statement. The curvature consumer uses this stronger theorem with no containment premise. This is a finite-state arithmetic inequality, with no signed-integral identity, J-sign conclusion, RH conclusion, or literature novelty claim.

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/FullPrimePowerArithmeticSurplus.complete_mangoldt_add_E3_eq_neg_residual`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/FullPrimePowerArithmeticSurplus.full_prime_power_arithmetic_surplus`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/FullPrimePowerArithmeticSurplus.full_prime_power_arithmetic_surplus_root_scale`
- Dependency: [D5/S3/Arith/Robin/OriginalEndpointPrimeTail](../OriginalEndpointPrimeTail.md)
