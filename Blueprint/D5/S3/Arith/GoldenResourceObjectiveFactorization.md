# Golden Resource Objective Factorization

## Abstract

At every real resource price, the objective of a positive integer is the finite sum of its prime-direction local objectives.

**Theorem 1.1 (The objective factors over prime directions).**

$$\forall lambda \in \mathbb{R}, n \in \mathbb{N},\; 1 \le n \Rightarrow goldenResourceObjective\left(lambda, n\right) = \sum_{p \in primeFactors\left(n\right)} goldenPrimeLocalObjective\left(lambda, p, factorization\left(n, p\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResourceObjectiveFactorization.golden_resource_objective_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real price lambda and positive natural number n, the global resource objective equals the sum over the prime factors of n of the local objective at the corresponding factorization exponent. The proof applies Mathlib's multiplicative factorization of sigma, the logarithm of a finite product, and the prime-power geometric sum formula.

This is the cross-prime version of the atom's displayed local identity. It does not compute the unrestricted optimum, characterize optimal exponents, prove finiteness of profitable layers, settle tied thresholds, or address the boundary at 5040.

**Theorem 1.2 (The objective sums over any finite prime superset).**

$$\forall lambda \in \mathbb{R}, n \in \mathbb{N}, s \in Finset\left(\mathbb{N}\right),\; \left(1 \le n \land primeFactors\left(n\right) \subseteq s\right) \Rightarrow goldenResourceObjective\left(lambda, n\right) = \sum_{p \in s} goldenPrimeLocalObjective\left(lambda, p, factorization\left(n, p\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResourceObjectiveFactorization.golden_resource_objective_sum_on` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If a finite set s contains every prime factor of a positive n, the same objective is the sum of the local objectives over s. Exponents outside the prime support are zero and their local terms vanish. This companion result consumes the factorization theorem, so the dependency direction is sum_on to factorization.

## References

- Truth anchor: `D5/S3/Arith/GoldenResourceObjectiveFactorization.golden_resource_objective_factorization`
- Truth anchor: `D5/S3/Arith/GoldenResourceObjectiveFactorization.golden_resource_objective_sum_on`
- Dependency: [D5/S3/Arith/GoldenLocalThreshold](GoldenLocalThreshold.md)
