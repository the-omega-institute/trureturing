# An Invariant Measure on the Golden Word Subshift

## Abstract

Cesaro averages of successive forward images of a point mass have a convergent subsequence in the compact space of probability measures, and the telescoping boundary term vanishes along it, so the limit is shift invariant.

Write X_g for the golden word subshift and sigma for its one-step forward shift, which restricts to X_g because a shift of a subshift member is again a member. For a point x of X_g, the Cesaro average A_{x,n} is the normalized sum of the first n forward images of the Dirac mass at x; it is a probability measure whenever n is positive. Below, BC(X_g) denotes the bounded continuous real-valued functions on X_g. The inverse n^{-1} is the total inverse of the reals, so it is zero at n = 0; the identities below are stated for every natural n, and both sides vanish in that degenerate case.

Mathlib supplies the two analytic inputs: the space of probability measures on a compact space is itself compact, and pushforward along a continuous map is continuous for the topology of convergence in distribution. It carries no existence theorem for invariant measures, so the construction is carried out here for this system.

**Theorem 1.1 (Integrating a Cesaro average is averaging along the orbit).**

$$\forall f\in \operatorname{BC}(X_g), \forall x\in X_g, \forall n\in \mathbb{N}, \int f dA_{x,n} = n^{-1} \sum_{k < n} f(\sigma^{k}(x))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/GoldenSubshiftInvariantMeasure.integral_cesaroAverage` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Integration against a finite sum of measures is the finite sum of the integrals, proved by induction on the block length; each summand is a pushed-forward Dirac mass, whose integral is one evaluation of f. The scalar normalization then produces the displayed average.

**Theorem 1.2 (Shifting a Cesaro average leaves only a boundary term).**

$$\forall f\in \operatorname{BC}(X_g), \forall x\in X_g, \forall n\in \mathbb{N}, \int (f\circ\sigma) dA_{x,n} - \int f dA_{x,n} = n^{-1}(f(\sigma^{n}(x)) - f(x))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/GoldenSubshiftInvariantMeasure.cesaroAverage_shift_diff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Applying the previous identity to f composed with sigma and to f, the two orbit sums differ by a telescoping cancellation of all interior terms. What survives is the difference of the two endpoint values, divided by the block length.

**Theorem 1.3 (The golden subshift carries an invariant probability measure).**

$$\exists \mu \in \operatorname{Prob}(X_g), \operatorname{Measurable}(\sigma) \land \operatorname{map}(\sigma)(\mu) = \mu$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/GoldenSubshiftInvariantMeasure.exists_invariant_probabilityMeasure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Start from any point of X_g, which is nonempty because the golden word itself is a member. The averages A_{x,n+1} live in the space of probability measures on X_g, which is compact and sequentially compact because X_g is compact; take a convergent subsequence. Pushforward along sigma is continuous, so it carries that subsequence to a sequence converging to the pushforward of the limit. Along the subsequence the boundary term of the preceding identity is bounded by twice the supremum norm of f divided by the block length, hence tends to zero. The two limits therefore integrate every bounded continuous function alike, and finite Borel measures agreeing on all such integrals coincide. The conclusion is the two-part measure-preserving predicate: the shift is measurable, and the limit measure is its own pushforward. Uniqueness of the invariant measure is not claimed here, and no ergodicity statement is made.

## References

- Truth anchor: `D5/S1/Words/Complexity/GoldenSubshiftInvariantMeasure.cesaroAverage_shift_diff`
- Truth anchor: `D5/S1/Words/Complexity/GoldenSubshiftInvariantMeasure.exists_invariant_probabilityMeasure`
- Truth anchor: `D5/S1/Words/Complexity/GoldenSubshiftInvariantMeasure.integral_cesaroAverage`
- Dependency: [D5/S1/Words/Complexity/GoldenSubshiftMinimality](GoldenSubshiftMinimality.md)
