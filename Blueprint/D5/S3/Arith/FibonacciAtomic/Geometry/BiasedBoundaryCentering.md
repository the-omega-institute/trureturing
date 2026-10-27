# Centering and Conditional Suffix Residuals

## Abstract

Actual integral centering on the biased boundary cancels both the finite prefix constant and the global centering constant in every conditional suffix trace.

**Definition 1.1 (mean).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCentering.mean`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCentering.mean` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mean functional is the L2 inner product with the actual constant one. Since M is a probability measure, this constant has norm one and the functional equals the actual integral with respect to M.

**Definition 1.2 (Pi).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCentering.Pi`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCentering.Pi` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Pi is the orthogonal projection onto the orthogonal complement of the span of the actual constant one. Its ambient formula is F minus the constant function with value mean(F).

**Definition 1.3 (C).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCentering.C`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCentering.C` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The centered trace is C=Pi composed with the original J. Its values are included in the original ambient G when conditional pullbacks are applied.

**Theorem 1.4 (The Actual Centered Suffix).**

$$(\forall F: \operatorname{G}\left(\right), (\operatorname{mean}\left(F\right)=\operatorname{integral}\left(M, F\right)))\land(\forall c: \mathbb{R}, (\operatorname{mean}\left(\operatorname{constG}\left(c\right)\right)=c))\land(\forall F: \operatorname{G}\left(\right), (\operatorname{Pi}\left(F\right)=F-\operatorname{constG}\left(\operatorname{mean}\left(F\right)\right)))\land(\forall F: \operatorname{G}\left(\right), (\Vert \operatorname{Pi}\left(F\right) \Vert\leq\Vert F \Vert))\land(\forall p: \operatorname{Address}\left(\right), (\forall z: \operatorname{H}\left(\right), (\operatorname{Pi}\left(\operatorname{pullback}\left(p, \operatorname{C}\left(z\right)\right)\right)=\operatorname{C}\left(\operatorname{S}\left(p, z\right)\right))))\land(\forall p: \operatorname{Address}\left(\right), (\forall z: \operatorname{H}\left(\right), ((\Vert \operatorname{Pi}\left(\operatorname{pullback}\left(p, \operatorname{C}\left(z\right)\right)\right) \Vert)^{2}\leq(\operatorname{goldenRatio}\left(\right)) \cdot ((\Vert \operatorname{S}\left(p, z\right) \Vert)^{2}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCentering.centered_suffix_residual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every F in G the mean equals its M integral, mean sends the constant c to c, and Pi subtracts that constant mean. Orthogonal projection makes Pi a contraction.

For every original finite prefix p and every original z in H, first pulling back Cz and then centering in the suffix L2(M) gives exactly C applied to the strict suffix vector S(p)z. Conditional composition fixes constants. The all-vector path split therefore cancels both the finite prefix sum and the constant subtracted by global centering.

The squared norm of this centered conditional suffix is at most the golden ratio times the squared norm of S(p)z. This follows from the contraction of Pi and the original all-vector Hardy bound for J, using the original golden biased parameter.

This statement concerns centering in a fixed conditional suffix space for each p. Identifying the global stopping-cylinder atom-average operator, summing the weighted conditional norms, and proving the global threshold bound require further results. No covariance or spectral counting assertion is made.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCentering.C`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCentering.Pi`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCentering.centered_suffix_residual`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCentering.mean`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryPathSplit](BiasedBoundaryPathSplit.md)
