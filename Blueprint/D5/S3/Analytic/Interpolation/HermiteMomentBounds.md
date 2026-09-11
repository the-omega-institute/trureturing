# Hermite nodes from two moments

## Abstract

The mean and total squared deviation of positive finite coordinates determine a positive lower Hermite node and an upper node bounding all coordinates.

**Theorem 1.1 (Positive lower node and coordinate upper bound).**

$$\forall k: \operatorname{Nat}\left(\right), \forall x: \operatorname{Fin}\left(k\right) \to \operatorname{Real}\left(\right), (2 \le k \land (\forall i: \operatorname{Fin}\left(k\right), 0 < \operatorname{x}\left(i\right))) \implies (0 < m-r \land (\forall i: \operatorname{Fin}\left(k\right), \operatorname{x}\left(i\right) \le m+(k-1)r))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/HermiteMomentBounds.hermite_moment_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let k be a natural number at least two, and let x assign a positive real coordinate to each element of Fin k. Write m for their arithmetic mean, V for their total squared deviation, and r for the nonnegative radius defined below. The lower and upper nodes are m-r and m+(k-1)r.

$m = \frac{\sum_{i \in \operatorname{Fin}\left(k\right)} \operatorname{x}\left(i\right)}{k}, V = \sum_{i \in \operatorname{Fin}\left(k\right)} (\operatorname{x}\left(i\right)-m)^{2}, r = \sqrt{\frac{V}{k(k-1)}}$

Strict positivity gives a sum of squares strictly smaller than the square of the sum, hence V is less than k(k-1)m squared and r is less than m. The centered coordinates sum to zero. Cauchy-Schwarz on all indices other than a chosen index bounds its squared deviation by (k-1) times the remaining squared deviations. Substitution of the radius gives the upper bound, including when V is zero.

## References

- Truth anchor: `D5/S3/Analytic/Interpolation/HermiteMomentBounds.hermite_moment_bounds`
