# Golden Reciprocal Fixed Point Uniqueness

## Abstract

The positive real fixed point of the reciprocal residual map is uniquely the golden ratio.

**Theorem 1.1 (The golden ratio is the unique positive fixed point).**

$$\forall x \in \mathbb{R}, 0 < x \Rightarrow (1 + \frac{1}{x} = x \iff x = \frac{1 + \sqrt{5}}{2}).$$

*Proof.* Machine-checked in Lean as `D5/S1/FixedPoints/Algebraic/GoldenFixedPoint.golden_fixed_point_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Define R(x) = 1 + 1/x. For every positive real x, R(x) equals x if and only if x is the displayed positive radical root.

The reverse direction applies the repository's existing golden-ratio fixed-point theorem. For the forward direction, the existing reciprocal-to-quadratic equivalence gives x squared equal to x plus one; comparison with the golden-ratio identity factors the difference, and positivity excludes the other factor.

Thus the statement includes both that the displayed value is a fixed point and that every positive fixed point equals it. No continuity, nonzero, or conjectural premise is added.

## References

- Truth anchor: `D5/S1/FixedPoints/Algebraic/GoldenFixedPoint.golden_fixed_point_unique`
- Dependency: [D5/S0/Carrier/GoldenRatio](../../../S0/Carrier/GoldenRatio.md)
- Dependency: [D5/S0/Tower/GoldenFixedPoint](../../../S0/Tower/GoldenFixedPoint.md)
- Dependency: [D5/S0/Tower/QuadraticFixedPoint](../../../S0/Tower/QuadraticFixedPoint.md)
