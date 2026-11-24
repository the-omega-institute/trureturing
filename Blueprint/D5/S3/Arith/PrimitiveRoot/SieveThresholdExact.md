# The exact arithmetic threshold for the coarse character sieve

## Abstract

The exact arithmetic threshold for the coarse character sieve

**Theorem 1.1 (Unconditional necessary exclusions).**

Lean statement: `D5/S3/Arith/PrimitiveRoot/SieveThresholdExact.feasible_ne_exceptions`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/PrimitiveRoot/SieveThresholdExact.feasible_ne_exceptions` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural x, feasibility implies x≠3483481 and x≠3573571. No lower threshold or primality assumption is required. At either exception the full support and the covering condition force a coefficient greater than 42 times the positive density, contradicting the strict margin.

**Theorem 1.2 (Exact feasibility and the two exceptions).**

Lean statement: `D5/S3/Arith/PrimitiveRoot/SieveThresholdExact.feasible_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/PrimitiveRoot/SieveThresholdExact.feasible_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* K. McGown, E. Treviño, T. Trudgian (2016). *Resolving Grosswald's conjecture on GRH*. DOI: [10.7169/facm/2016.55.2.5](https://doi.org/10.7169/facm/2016.55.2.5). URL: <https://doi.org/10.7169/facm/2016.55.2.5>.

*Commentary.*

For every integer x at least 3483481, Feasible(x) holds if and only if x differs from both 3483481 and 3573571. Feasibility uses precisely the signed coefficient K, the bound (3/2)sqrt(x)log(x), and the main term x/2-sqrt(x). There is no primality or GRH assumption.

An ordered prime-support split covers the unbounded tail. Below it, seven-prime supports with large reciprocal mass have ten possible radicals. Divisibility leaves eight integers, including one exception; the other seven satisfy exact rational margin certificates. For each exception, the cover forces the sieve set to be the difference of the full prime support and the gcd support. Every subset of that seven-element support has K greater than 42 times its positive margin, which contradicts the signed estimate.

This is an arithmetic classification of the sieve criterion. The analytic character-sum estimates remain hypotheses of its application to primitive roots.

**Theorem 1.3 (From coarse analytic estimates to a prime primitive root).**

Lean statement: `D5/S3/Arith/PrimitiveRoot/SieveThresholdExact.exists_prime_primitiveRoot`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/PrimitiveRoot/SieveThresholdExact.exists_prime_primitiveRoot` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* K. McGown, E. Treviño, T. Trudgian (2016). *Resolving Grosswald's conjecture on GRH*. DOI: [10.7169/facm/2016.55.2.5](https://doi.org/10.7169/facm/2016.55.2.5). URL: <https://doi.org/10.7169/facm/2016.55.2.5>.

*Commentary.*

Let p be prime and at least 3483482. Assume the real part of the principal smoothed character sum is at least p/2-sqrt(p). For each nonprincipal character whose order divides the product of the distinct prime factors of p-1, assume the absolute real part is at most (3/2)sqrt(p)log(p). Then there is a prime q less than p with order p-1 modulo p.

The exact feasibility theorem supplies sieve parameters. Replacing e by gcd(e,p-1) preserves the sieve primes and restricts every character order used by the signed sieve to a divisor of the radical of p-1. The signed error coefficient is nonnegative and the density margin is positive, so the coarse bounds replace both sides in the required directions. No unconditional character-sum estimate is asserted.

## References

- Truth anchor: `D5/S3/Arith/PrimitiveRoot/SieveThresholdExact.exists_prime_primitiveRoot`
- Truth anchor: `D5/S3/Arith/PrimitiveRoot/SieveThresholdExact.feasible_iff`
- Truth anchor: `D5/S3/Arith/PrimitiveRoot/SieveThresholdExact.feasible_ne_exceptions`
- Dependency: [D5/S3/Arith/PrimitiveRoot/SieveSevenFactors](SieveSevenFactors.md)
- Dependency: [D5/S3/Arith/PrimitiveRoot/SieveThreshold](SieveThreshold.md)
