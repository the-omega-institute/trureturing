# Zero-temperature limit of the resource objective

## Abstract

The Boltzmann sum of the resource objective converges exactly when beta times lambda exceeds one, factors over primes, and tends to the optimal value at zero temperature.

The resource objective at price lambda is J(n) = log(sigma(n)/n) - lambda log n. Its Boltzmann sum at inverse temperature beta is Z(lambda, beta), the sum over n >= 1 of exp(beta J(n)), that is of (sigma(n)/n)^beta times n^(-beta lambda). The optimal value V(lambda) is the finite sum of log p times (marginal - lambda) over all prime layers whose marginal exceeds lambda; the frozen supremum theorem identifies it with the largest objective value.

**Theorem 1.1 (Exact convergence domain).**

Lean statement: `D5/S3/Arith/GoldenResource/GoldenResourceZeroTemperature.boltzmann_summable_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/GoldenResourceZeroTemperature.boltzmann_summable_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For beta > 0 the weights exp(beta J(n)) are summable if and only if beta lambda > 1. Since sigma(n)/n >= 1 each weight is at least n^(-beta lambda), which forces beta lambda > 1. Conversely sigma(n)/n is at most the harmonic number H_n <= 1 + log n, and log n <= n^eps / eps with eps = (beta lambda - 1)/(2 beta) bounds each weight by a constant times n^(-(beta lambda + 1)/2).

**Theorem 1.2 (Euler product).**

Lean statement: `D5/S3/Arith/GoldenResource/GoldenResourceZeroTemperature.boltzmann_sum_euler_product`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/GoldenResourceZeroTemperature.boltzmann_sum_euler_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the convergence domain Z(lambda, beta) equals the product over primes p of the local sums over e >= 0 of exp(beta L_p(e)), where L_p(e) is the frozen local objective of the prime power p^e. The objective is additive on coprime factors by the frozen prime factorization, so the weights are multiplicative and the standard Euler product applies.

**Theorem 1.3 (Zero-temperature limit).**

Lean statement: `D5/S3/Arith/GoldenResource/GoldenResourceZeroTemperature.zero_temperature_limit`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/GoldenResourceZeroTemperature.zero_temperature_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every lambda > 0 the set of optimizers {n >= 1 : J(n) = V(lambda)} is finite and nonempty, Z(lambda, beta) exp(-beta V(lambda)) tends to its cardinality, and log Z(lambda, beta) / beta tends to V(lambda) as beta tends to infinity.

Each shifted weight exp(beta (J(n) - V)) tends to 1 at an optimizer and to 0 elsewhere, and for beta >= 2/lambda it is dominated by the summable weight at beta = 2/lambda; dominated convergence of series gives the first limit, and taking logarithms gives the second. This is the standard Laplace principle applied to the resource objective.

Reading: at finite beta the prime directions contribute independent factors and log Z is smooth in the parameters; as beta grows the free energy log Z / beta converges to the piecewise linear optimum, and the number of tied optimizers appears only in the correction log(count) / beta. The limit concerns the optimum at each fixed price; it makes no claim about Robin's inequality beyond the frozen results.

## References

- Truth anchor: `D5/S3/Arith/GoldenResource/GoldenResourceZeroTemperature.boltzmann_sum_euler_product`
- Truth anchor: `D5/S3/Arith/GoldenResource/GoldenResourceZeroTemperature.boltzmann_summable_iff`
- Truth anchor: `D5/S3/Arith/GoldenResource/GoldenResourceZeroTemperature.zero_temperature_limit`
- Dependency: [D5/S3/Arith/GoldenResource/GoldenResourceSupremum](GoldenResourceSupremum.md)
