# Prime Euler Logarithm Tail

## Abstract

The omitted-prime Euler logarithms have an explicit power-decay tail bound.

**Theorem 1.1 (Explicit bound for omitted prime directions).**

$$\forall s\in\mathbb{R}, \forall X\in\mathbb{N}, (1<s \land 2\leq X) \implies \sum_{p \in \mathbb{P}, X<p} -\log(1-p^{-s}) \leq \frac{1}{1-2^{-s}} \cdot \frac{X^{1-s}}{s-1}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SeriesInequalities/PrimeEulerLogTail.prime_euler_log_tail_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sum ranges over natural primes strictly greater than the integer X. The parameter s is real and greater than one.

Compare each nonnegative Euler logarithm with the corresponding negative power using the uniform denominator at two. Summability follows from the power series. Including composite integers enlarges the tail, and the decreasing power function bounds that tail by its improper integral.

This result controls only omitted prime directions. It does not identify a finite divisor-window error, bound finite Fibonacci exponent truncations, or prove the resulting quantified epsilon convergence statement.

## References

- Truth anchor: `D5/S3/Analytic/SeriesInequalities/PrimeEulerLogTail.prime_euler_log_tail_le`
