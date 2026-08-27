# Countable Weighted Holder Interpolation

## Abstract

Nonnegative summable families obey weighted geometric-mean interpolation.

**Theorem 1.1 (A weighted geometric-mean series is bounded by its endpoint sums).**

$$\begin{gathered}\forall iota,\\\forall f, g: iota\to \mathbb{R},\\(\forall i, 0\le f\left(i\right)) \land (\forall i, 0\le g\left(i\right)) \land\\Summable\left(f\right) \land Summable\left(g\right) \land\\0< a \land 0< b \land a+b=1 \Rightarrow\\\sum_{i} f\left(i\right)^{a} \cdot g\left(i\right)^{b} \le {\sum_{i} f\left(i\right)}^{a} \cdot {\sum_{i} g\left(i\right)}^{b}.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SeriesInequalities/CountableWeightedHolderInterpolation.countable_weighted_holder_interpolation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let f and g be nonnegative summable real families on an arbitrary index type, and let a and b be positive weights with a+b=1. The sum of f(i)^a g(i)^b is at most the product of the endpoint sums raised to a and b.

The proof applies countable Holder inequality with conjugate exponents 1/a and 1/b. Raising f(i)^a to 1/a recovers f(i), and the same cancellation recovers g(i), including when a term is zero because both weights are positive.

This theorem packages the common interpolation step used by the golden displacement log-convexity argument. Two earlier private specializations in the frozen zeta modules demonstrate the same need but remain unchanged.

The theorem does not assert equality conditions, strictness, signed or complex variants, nonsummable endpoint behavior, zero endpoint weights, or interpolation among more than two families.

## References

- Truth anchor: `D5/S3/Analytic/SeriesInequalities/CountableWeightedHolderInterpolation.countable_weighted_holder_interpolation`
