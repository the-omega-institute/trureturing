# Actual Prime-Layer Exchange and Abundancy Records

## Abstract

An actual one-layer prime exchange forces 5040 to divide large strict abundancy records.

**Theorem 1.1 (A smaller actual integer with larger abundancy).**

Lean statement: `D5/S3/Arith/ExponentExchange/AbundancyRecord5040.one_layer_abundancy_exchange`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ExponentExchange/AbundancyRecord5040.one_layer_abundancy_exchange` (`✓ std3`). ∎

*Citation.* Leonidas Alaoglu and Paul Erdos (1944). *On highly composite and similar numbers*. DOI: [10.2307/1990319](https://doi.org/10.2307/1990319).

*Commentary.*

Let m be a positive natural number, p and q primes, and k>=1. Assume q divides m, the sum B(p,k)=p+...+p^k is below q, and the p-exponent of m is below k. The actual integer m'=(m/q)*p is positive and strictly smaller than m, and sigma(1,m')/m' is strictly larger than sigma(1,m)/m.

At price zero the exact single-layer resource identity gives W(m')-W(m)=log(1+1/B(p,a+1))-log(1+1/B(q,b)), where a=v_p(m) and b=v_q(m)>=1. The first denominator is at most B(p,k)<q<=B(q,b). Strict monotonicity of the reciprocal and logarithm proves the gain. This removes one copy of q and inserts one copy of p; no full-exponent exchange is assumed.

**Theorem 1.2 (The literal 5040 core).**

Lean statement: `D5/S3/Arith/ExponentExchange/AbundancyRecord5040.strict_abundancy_record_divisible_5040`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ExponentExchange/AbundancyRecord5040.strict_abundancy_record_divisible_5040` (`✓ std3`). ∎

*Citation.* Leonidas Alaoglu and Paul Erdos (1944). *On highly composite and similar numbers*. DOI: [10.2307/1990319](https://doi.org/10.2307/1990319).

*Commentary.*

For every positive natural m, assume sigma(1,m)/m>30 and a strict abundancy record against every positive natural n<m, including one and two. Then the literal integer 5040 divides m.

The exact Euler factors bound sigma(1,m)/m by the product of p/(p-1) over its prime support. If all primes were at most thirty, padding to every integer from two through thirty would give the telescoping upper bound thirty. Hence an actual prime q>30 divides m. A missing layer among (2,4),(3,2),(5,1),(7,1) would have denominator at most thirty and permit the preceding smaller integer exchange, contradicting the record. The pairwise coprime powers 16,9,5,7 therefore divide m and have product 5040.

This is an application of the classical superabundant-number exchange method, with no claim of literature priority. It does not assert that such records occur at any particular scale, nor prove a Robin upper inequality or RH.

## References

- Truth anchor: `D5/S3/Arith/ExponentExchange/AbundancyRecord5040.one_layer_abundancy_exchange`
- Truth anchor: `D5/S3/Arith/ExponentExchange/AbundancyRecord5040.strict_abundancy_record_divisible_5040`
- Dependency: [D5/S3/Arith/GoldenResource/EightStepAbundancy](../GoldenResource/EightStepAbundancy.md)
- Dependency: [D5/S3/Arith/GoldenResource/GoldenResource5040EndpointComparison](../GoldenResource/GoldenResource5040EndpointComparison.md)
