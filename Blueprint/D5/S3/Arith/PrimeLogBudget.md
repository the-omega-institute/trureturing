# Prime Log Budget

## Abstract

Every positive real budget uniquely determines a threshold above two through the sum of logarithmic prime ratios.

**Definition 1.1 (The prime log budget).**

$$\forall y \in \mathbb{R}, primeLogBudget\left(y\right) = \sum_{p \in primesBelow\left(natCeil\left(y\right)\right)} log\left(\frac{y}{p}\right)$$

*Formalization.* `D5/S3/Arith/PrimeLogBudget.primeLogBudget` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The index set is the natural primes strictly below the ceiling of y, so the summand is a finite sum of logarithmic ratios. A fixed upper cutoff retains the value as further primes enter the active set, which is what makes the total continuous in y.

**Theorem 1.2 (A positive budget has exactly one threshold above two).**

$$\begin{aligned}\forall T \in \mathbb{R}, 0 < T \Rightarrow\\\exists! y \in \mathbb{R}, (2 < y \land T = primeLogBudget\left(y\right)).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/PrimeLogBudget.exists_unique_prime_log_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The statement quantifies over every positive real budget T. It asserts a unique real y with 2 < y whose prime log budget is exactly T. Uniqueness is part of the conclusion, not an added hypothesis.

The proof shows the budget is continuous at every positive point and strictly monotone on the ray from two, evaluates it to zero at two, and bounds it below by a single logarithmic ratio. The intermediate value theorem then supplies existence on a closed interval and strict monotonicity supplies uniqueness.

This module carries only the existence and uniqueness of the threshold. The optimal exponent formula, the closed form of the optimal value, and the budget constraint argument that uses them are not conclusions of this module.

## References

- Truth anchor: `D5/S3/Arith/PrimeLogBudget.exists_unique_prime_log_budget`
- Truth anchor: `D5/S3/Arith/PrimeLogBudget.primeLogBudget`
