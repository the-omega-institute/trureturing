# Hermite nodes from two moments

## Abstract

The mean and total squared deviation of positive finite coordinates determine a positive lower Hermite node and an upper node bounding all coordinates.

**Theorem 1.1 (Strict square-sum inequality).**

$$\forall (k: \operatorname{Nat}\left(\right)), (\forall (x: \operatorname{Fin}\left(k\right) \to \operatorname{Real}\left(\right)), (((2 \le k) \land (\forall (i: \operatorname{Fin}\left(k\right)), (0 < \operatorname{x}\left(i\right)))) \to (\sum_{i \in \operatorname{Fin}\left(k\right)} \operatorname{x}\left(i\right)^{2} < (\sum_{i \in \operatorname{Fin}\left(k\right)} \operatorname{x}\left(i\right))^{2})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/HermiteMomentBounds.sum_sq_lt_sq_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For at least two positive real coordinates, the sum of their squares is strictly less than the square of their sum. For each index i, another index j has a positive coordinate, so Finset.single_lt_sum gives xᵢ < ∑ⱼxⱼ. Multiplying by xᵢ > 0 and summing the strict inequalities gives ∑ᵢxᵢ² < ∑ᵢxᵢ(∑ⱼxⱼ) = (∑ᵢxᵢ)².

**Theorem 1.2 (Positive lower node and coordinate upper bound).**

$$\forall k: \operatorname{Nat}\left(\right), \forall x: \operatorname{Fin}\left(k\right) \to \operatorname{Real}\left(\right), (2 \le k \land (\forall i: \operatorname{Fin}\left(k\right), 0 < \operatorname{x}\left(i\right))) \implies (0 < m-r \land (\forall i: \operatorname{Fin}\left(k\right), \operatorname{x}\left(i\right) \le m+(k-1)r))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/HermiteMomentBounds.hermite_moment_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let k be a natural number at least two, and let x assign a positive real coordinate to each element of Fin k. Write m for their arithmetic mean, V for their total squared deviation, and r for the nonnegative radius defined below. The lower and upper nodes are m-r and m+(k-1)r.

$m = \frac{\sum_{i \in \operatorname{Fin}\left(k\right)} \operatorname{x}\left(i\right)}{k}, V = \sum_{i \in \operatorname{Fin}\left(k\right)} (\operatorname{x}\left(i\right)-m)^{2}, r = \sqrt{\frac{V}{k(k-1)}}$

The strict square-sum inequality sum_sq_lt_sq_sum gives ∑ᵢxᵢ² < (∑ᵢxᵢ)². Since V = ∑ᵢxᵢ² - km² and ∑ᵢxᵢ = km, this implies V < k(k-1)m² and r < m. The centered coordinates sum to zero. Cauchy-Schwarz on all indices other than a chosen index bounds its squared deviation by (k-1) times the remaining squared deviations. Substitution of the radius gives the upper bound, including when V is zero.

## References

- Truth anchor: `D5/S3/Analytic/Interpolation/HermiteMomentBounds.hermite_moment_bounds`
- Truth anchor: `D5/S3/Analytic/Interpolation/HermiteMomentBounds.sum_sq_lt_sq_sum`
