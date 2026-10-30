# Every exponential polynomial has a genuine Fock vector

## Abstract

Every exponential polynomial has a genuine Fock vector.

**Theorem 1.1 (Every exponential polynomial has a genuine Fock vector).**

Lean statement: `D5/S3/Quantum/QuantumChannels/FockAttenuator/ExponentialPolynomialFock.exponential_polynomial_reconstruction`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/FockAttenuator/ExponentialPolynomialFock.exponential_polynomial_reconstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite exponential-polynomial function with arbitrary complex exponents and polynomial coefficients, there exists an actual completed square-summable Fock vector whose Bargmann transform is that function. This assertion applies to exponential polynomials, rather than to all entire functions.

For z^m*exp(alpha*z), the coefficient at n=k+m is sqrt((k+m)!)*alpha^k/k!, and coefficients below m are zero. A symbolic factorial comparison bounds (k+m)!/(k!)^2 by m!*2^m*2^k/k!. The exponential series proves square summability for every complex alpha, without a magnitude restriction.

The constructed lp vector has the required entire transform by the convergent factorial series. Finite polynomial and exponential-block sums give the full reconstruction. Transform injectivity gives uniqueness when it is needed by a consumer. No numerical summability test, cutoff, energy premise or real-coefficient restriction is used.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/ExponentialPolynomialFock.exponential_polynomial_reconstruction`
- Dependency: [D5/S3/Analytic/Entire/ExponentialPolynomial](../../../Analytic/Entire/ExponentialPolynomial.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/FockAttenuator/Bargmann](Bargmann.md)
