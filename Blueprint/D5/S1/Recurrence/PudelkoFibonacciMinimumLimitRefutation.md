# Fibonacci Minima Under Bounded Initialization

## Abstract

A uniform count bound refutes the proposed one-quarter limit for Fibonacci minima.

**Definition 1.1 (The bilateral Fibonacci sequence).**

$$\forall x \in \mathbb{Z}, y \in \mathbb{Z}, k \in \mathbb{Z},\; \operatorname{bilateralFibonacci}\left(x, y, k\right) = x \cdot Int.fib\left(k - 1\right) + y \cdot Int.fib\left(k\right)$$

*Formalization.* `D5/S1/Recurrence/PudelkoFibonacciMinimumLimitRefutation.bilateral_fibonacci` (`✓ std3`).

*Citation.* Marc T. Pudelko (2025). *Modular Periodicity of Random Initialized Recurrences*. URL: <https://arxiv.org/abs/2510.24882v5>.

*Commentary.*

For integer initial values x and y, this closed form has value x at index zero and y at index one. It satisfies a(k+2)=a(k+1)+a(k) for every integer k, so negative and positive indices belong to one bilateral recurrence. The notation bilateralFibonacci is the canonical underscore-free rendering of bilateral_fibonacci.

**Definition 1.2 (A global minimum at position zero).**

$$\forall x \in \mathbb{Z}, y \in \mathbb{Z},\; (\operatorname{min0}\left(x, y\right)) \Leftrightarrow ((\forall k \in \mathbb{Z},\; \left|\operatorname{bilateralFibonacci}\left(x, y, 0\right)\right| \le \left|\operatorname{bilateralFibonacci}\left(x, y, k\right)\right|))$$

*Formalization.* `D5/S1/Recurrence/PudelkoFibonacciMinimumLimitRefutation.min0` (`✓ std3`).

*Citation.* Marc T. Pudelko (2025). *Modular Periodicity of Random Initialized Recurrences*. URL: <https://arxiv.org/abs/2510.24882v5>.

*Commentary.*

The predicate allows ties: position zero need only be one global minimizer of the absolute values. The quantifier ranges over every integer index, rather than a finite observation window.

**Definition 1.3 (The bounded-initialization probability).**

$$\forall N \in \mathbb{N},\; \operatorname{boundedMin0Probability}\left(N\right) = \frac{(\left|\{(x, y) \in \mathbb{Z}^{2} \mid ((-(N: \mathbb{Z}) \le x) \land \left((x \le (N: \mathbb{Z})) \land \left((-(N: \mathbb{Z}) \le y) \land \left((y \le (N: \mathbb{Z})) \land (\operatorname{min0}\left(x, y\right))\right)\right)\right))\}\right|: \mathbb{Q})}{(2 \cdot N + 1: \mathbb{Q})^{2}}$$

*Formalization.* `D5/S1/Recurrence/PudelkoFibonacciMinimumLimitRefutation.bounded_min0_probability` (`✓ std3`).

*Citation.* Marc T. Pudelko (2025). *Modular Periodicity of Random Initialized Recurrences*. URL: <https://arxiv.org/abs/2510.24882v5>.

*Commentary.*

The numerator counts integer pairs in the inclusive square [-N,N]^2 for which zero is a global minimizer. The denominator is the square's cardinality (2N+1)^2, and both quantities are coerced to rational numbers before division.

**Definition 1.4 (The proposed one-quarter limit).**

$$(claim) \Leftrightarrow ((\forall epsilon \in \mathbb{Q},\; (0 < epsilon) \Rightarrow ((\exists Nzero \in \mathbb{N},\; \forall N \in \mathbb{N},\; (Nzero \le N) \Rightarrow ((\left|\operatorname{boundedMin0Probability}\left(N\right) - \frac{1}{4}\right| < epsilon))))))$$

*Formalization.* `D5/S1/Recurrence/PudelkoFibonacciMinimumLimitRefutation.claim` (`✓ std3`).

*Citation.* Marc T. Pudelko (2025). *Modular Periodicity of Random Initialized Recurrences*. URL: <https://arxiv.org/abs/2510.24882v5>.

*Commentary.*

This is the epsilon-threshold form of convergence of the bounded probability to one quarter. It is the bounded-initialization reading of the paper's formula at minimum position zero for the Fibonacci recurrence.

**Theorem 1.5 (The proposed limit is false).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/PudelkoFibonacciMinimumLimitRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/pudelko-fibonacci-minimum-limit-refutation` (refuted) by `D5/S1/Recurrence/PudelkoFibonacciMinimumLimitRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"pudelko-fibonacci-minimum-limit-refutation","declaration_gid":"D5/S1/Recurrence/PudelkoFibonacciMinimumLimitRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Marc T. Pudelko (2025). *Modular Periodicity of Random Initialized Recurrences*. URL: <https://arxiv.org/abs/2510.24882v5>.

*Commentary.*

For t at least three, the count bound gives probability at most 2/9, which is separated from 1/4 by more than 1/72. After any proposed threshold, choosing t as the maximum of three and that threshold supplies a later index N=6t and contradicts the required epsilon bound.

## References

- Truth anchor: `D5/S1/Recurrence/PudelkoFibonacciMinimumLimitRefutation.bilateral_fibonacci`
- Truth anchor: `D5/S1/Recurrence/PudelkoFibonacciMinimumLimitRefutation.bounded_min0_probability`
- Truth anchor: `D5/S1/Recurrence/PudelkoFibonacciMinimumLimitRefutation.claim`
- Truth anchor: `D5/S1/Recurrence/PudelkoFibonacciMinimumLimitRefutation.min0`
- Truth anchor: `D5/S1/Recurrence/PudelkoFibonacciMinimumLimitRefutation.result`
