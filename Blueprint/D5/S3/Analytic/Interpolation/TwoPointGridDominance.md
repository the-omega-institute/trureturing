# Actual corners and the distance variance

## Abstract

Positive actual corners control the sum of squared distances to two coordinate grids.

**Theorem 1.1 (The positive envelope domain).**

$$\forall c,d: \operatorname{Fin}\left(2\right) \to \operatorname{Real}\left(\right), \forall A,B: \operatorname{Real}\left(\right), ((\forall i: \operatorname{Fin}\left(2\right), 0 < \operatorname{c}\left(i\right) \land \operatorname{c}\left(i\right) < \operatorname{d}\left(i\right)) \land \operatorname{Nonempty}\left(\operatorname{corners}\left(c, d, A, B\right)\right)) \implies (0 < \frac{B}{2} \land 0 \le \operatorname{varianceFloor}\left(c, d, A, B\right) \land \operatorname{varianceFloor}\left(c, d, A, B\right) < 2(\frac{B}{2})^{2})$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/TwoPointGridDominance.two_point_grid_domain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let c and d assign real endpoints to Fin 2, with 0 < c(i) < d(i) for each coordinate. Let A and B be real budgets. The set C consists of actual endpoint pairs whose coordinate sum lies in the closed interval from A to B. Write V for the sum of the two squared distances from the interval [A/2,B/2] to the coordinate sets. The distance to a two point set is the minimum of the distances to its two points.

$C = \operatorname{corners}\left(c, d, A, B\right), V = \operatorname{varianceFloor}\left(c, d, A, B\right)$

A single positive actual corner suffices: B/2 is positive and V lies between zero and 2(B/2) squared, with a strict upper inequality. The quantity V is a sum of squared deviations, not an average. Neither a positive lower budget nor a strict budget width is assumed here.

For an actual corner (x,y), its mean m=(x+y)/2 belongs to [A/2,B/2]. Each set distance is at most the absolute deviation of the corresponding coordinate from m. Their squared sum is at most (x-m) squared plus (y-m) squared, which equals 2m squared minus 2xy. Positivity of xy makes this strictly smaller than 2m squared, and m is at most B/2.

**Theorem 1.2 (The lower corner of a straddling row).**

$$\forall c,d,t,u,A,B: \operatorname{Real}\left(\right), (\operatorname{Nontrivial}\left(S\right) \land c+t < B \land B < d+t) \implies (A \le c+t \land c+t \le B)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/TwoPointGridDominance.two_actual_corners_lower_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let c,d,t,u,A,B be arbitrary real numbers. Define S to be the endpoint pairs in {c,d} times {t,u} whose sum lies in [A,B]. Nontrivial means that S contains two different pairs; their sums may be equal.

$S = \{ (x,y) \in \operatorname{Real}\left(\right)^{2} \mid (x = c \lor x = d) \land (y = t \lor y = u) \land A \le x+y \land x+y \le B \}$

If c+t < B < d+t, then A is at most c+t and c+t is at most B. Thus the lower corner (c,t) belongs to the slab. No positivity or ordering of the second pair of endpoints is required.

Suppose instead that c+t < A. The pairs (c,t) and (d,t) are outside the slab. If both remaining pairs (c,u) and (d,u) belonged to it, comparing their lower and upper sum inequalities with the two strict inequalities would give a contradiction. Consequently at most one pair could belong to S, contradicting the two different pairs.

## References

- Truth anchor: `D5/S3/Analytic/Interpolation/TwoPointGridDominance.two_actual_corners_lower_mem`
- Truth anchor: `D5/S3/Analytic/Interpolation/TwoPointGridDominance.two_point_grid_domain`
- Dependency: [D5/S3/Analytic/Interpolation/HermiteEnvelopeEquality](HermiteEnvelopeEquality.md)
- Dependency: [D5/S3/Analytic/Knapsack/FractionalKnapsackDual](../Knapsack/FractionalKnapsackDual.md)
