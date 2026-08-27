# Golden Reciprocal Fixed Point Uniqueness

## Abstract

The displayed radical is a positive fixed point of the reciprocal residual map, and it is the unique positive fixed point.

**Theorem 1.1 (The golden ratio is the unique positive fixed point).**

$$0 < \frac{1 + \sqrt{5}}{2} \land (1 + \frac{1}{\frac{1 + \sqrt{5}}{2}} = \frac{1 + \sqrt{5}}{2}) \land \forall x \in \mathbb{R}, 0 < x \Rightarrow (1 + \frac{1}{x} = x \iff x = \frac{1 + \sqrt{5}}{2}).$$

*Proof.* Machine-checked in Lean as `D5/S1/FixedPoints/Algebraic/GoldenFixedPoint.golden_fixed_point_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Define R(x) = 1 + 1/x. The displayed radical is asserted to be positive and to satisfy R(the displayed radical) = the displayed radical; the quantified clause then says that every positive real x is a fixed point exactly when it equals that radical.

The reverse direction applies the repository's existing golden-ratio fixed-point theorem. For the forward direction, the existing reciprocal-to-quadratic equivalence gives x squared equal to x plus one; comparison with the golden-ratio identity factors the difference, and positivity excludes the other factor.

Thus the type carries the existence witness directly as its first two conjuncts (positivity and fixed-point equality), and carries uniqueness in the final universal characterization. No continuity, nonzero, or conjectural premise is added.

## References

- Truth anchor: `D5/S1/FixedPoints/Algebraic/GoldenFixedPoint.golden_fixed_point_unique`
- Dependency: [D5/S0/Carrier/GoldenRatio](../../../S0/Carrier/GoldenRatio.md)
- Dependency: [D5/S0/Tower/GoldenFixedPoint](../../../S0/Tower/GoldenFixedPoint.md)
- Dependency: [D5/S0/Tower/QuadraticFixedPoint](../../../S0/Tower/QuadraticFixedPoint.md)
