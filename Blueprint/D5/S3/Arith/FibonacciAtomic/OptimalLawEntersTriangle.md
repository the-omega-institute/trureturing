# Optimal Laws Enter the Triangular Graph

## Abstract

Canonical triangular paths for all positive attaining laws.

**Theorem 1.1 (Fixed relabelling and exact cost).**

$$(\forall m: \mathbb{N}, (m \ge 2 \implies (\forall p: \operatorname{Fin}\left(m\right) \to \mathbb{R}, (((\forall i: \operatorname{Fin}\left(m\right), 0 < \operatorname{p}\left(i\right)) \land (\sum_{i}\operatorname{p}\left(i\right) = 1 \land \operatorname{L}\left(p\right) = \operatorname{alpha}\left(m\right)\cdot\operatorname{min}\left(p\right))) \implies (\exists sigma: \operatorname{Perm}\left(\operatorname{Fin}\left(m\right)\right), \exists gamma: \operatorname{RootPath}\left(m\right), ((\forall i: \operatorname{Fin}\left(m\right), \operatorname{probability}\left(gamma, i\right) = \operatorname{p}\left(\operatorname{sigma}\left(i\right)\right)) \land (\operatorname{anchorMass}\left(gamma\right) = \operatorname{min}\left(p\right) \land \operatorname{pathCost}\left(gamma\right) = \operatorname{L}\left(p\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/OptimalLawEntersTriangle.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let m >= 2 and let p be a strictly positive real probability law on m labels. Suppose its dyadic cost equals alpha(m) times its minimum coordinate. Then there is a fixed permutation sigma and a legal reduced triangular root path gamma whose written probabilities are p(sigma(i)). Its anchor mass is the minimum of p, and its layer cost is exactly the dyadic cost of p.

Each coordinate above the minimum has a least terminating binary depth D and equals the nearest strictly larger grid point at that depth. Its floor prefixes agree with the anchor at every shallower depth: an earlier disagreement would place the coordinate on an earlier binary grid, contrary to minimality. At and after D its fractional tail is zero. Thus a label outside the equal-prefix group writes no further digits.

Sort the coordinates in increasing order. At every depth the equal-prefix group is an initial label interval. Its fractional tails sum to the integer residual r, and each tail is below one, so r < e. An anchor one forces all e retained labels to write one. An anchor zero permits only terminal departures, each with current tail one half; the anchor tail is strictly below one half. Hence the two cases satisfy e <= 2r and 2r < e respectively. The labels departing together occupy the end of the current interval, and the residual recurrence gives the two triangular successors.

The written digits coincide with the coordinates' canonical binary digits. The original carry embedding supplies the integer residuals and anchor expansion, so both infinite series retain their exact values. No rationality or computability assumption is imposed on the positive real law.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/OptimalLawEntersTriangle.result`
- Dependency: [D5/S3/Arith/FibonacciAtomic/CarryGraphEmbedding](CarryGraphEmbedding.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/OptimalLawNearestStrictCeiling](OptimalLawNearestStrictCeiling.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/TriangularPathNormalization](TriangularPathNormalization.md)
