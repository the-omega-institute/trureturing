# Golden Local Threshold

## Abstract

Boundary marginal inequalities at a common price make a chosen exponent optimal within one prime direction.

**Definition 1.1 (The one-prime local objective).**

$$\forall lambda \in \mathbb{R}, p \in \mathbb{N}, a \in \mathbb{N},\; goldenPrimeLocalObjective\left(lambda, p, a\right) = log\left(\frac{1 - (\frac{1}{p})^{a + 1}}{1 - (\frac{1}{p})}\right) - lambda \cdot a \cdot log\left(p\right)$$

*Formalization.* `D5/S3/Arith/GoldenLocalThreshold.goldenPrimeLocalObjective` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a real price lambda, natural base p, and natural exponent a, this is the logarithm of the reciprocal geometric factor through layer a, minus lambda times a log p. The definition is total; the optimality theorem below restricts p to be prime.

**Theorem 1.2 (Boundary thresholds suffice for local optimality).**

$$\forall p \in \mathbb{N}, a \in \mathbb{N}, lambda \in \mathbb{R},\; \left(Prime\left(p\right) \land \left(goldenLayerMarginal\left(p, a + 1\right) \le lambda \land \left(a = 0 \lor lambda \le goldenLayerMarginal\left(p, a\right)\right)\right)\right) \Rightarrow \left(\forall b \in \mathbb{N},\; goldenPrimeLocalObjective\left(lambda, p, b\right) \le goldenPrimeLocalObjective\left(lambda, p, a\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenLocalThreshold.golden_prime_local_objective_maximal_of_threshold` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every prime p, real price lambda, and chosen exponent a, assume the next marginal is at most lambda. If a is positive, also assume lambda is at most the adopted boundary marginal; when a is zero, that lower-bound condition is absent. Then every competing natural exponent b has local objective at most the objective at a. Both boundary comparisons are non-strict, so equality and tied optima are retained.

The proof identifies each adjacent objective difference with log p times marginal minus price. Frozen strict decrease of the prime marginals propagates the two boundary inequalities, making the objective nondecreasing up to a and nonincreasing after a.

This is only the sufficiency direction for one fixed prime. It does not prove local necessity, combine prime directions, define the global bounds L or U, characterize highly abundant numbers, reduce absent prime checks to the smallest missing prime, or classify all endpoint ties.

## References

- Truth anchor: `D5/S3/Arith/GoldenLocalThreshold.goldenPrimeLocalObjective`
- Truth anchor: `D5/S3/Arith/GoldenLocalThreshold.golden_prime_local_objective_maximal_of_threshold`
- Dependency: [D5/S3/Arith/GoldenResourceOptimalInteger](GoldenResourceOptimalInteger.md)
