# Linear gain for the full logarithmic profile

## Abstract

The exact compensated generator has a positive quadratic lower bound on both integer tails.

**Theorem 1.1 (One threshold and gain constant for both signs).**

$$\exists A\in \mathbb{R},\quad0<A \land (\exists N\in \mathbb{N},\quad\forall z\in \mathbb{Z},\quad N<\left\lvert z\right\rvert\longrightarrow A\cdot \operatorname{discrepancyProfile}\left(z\right)^{2}\le \operatorname{actualGenerator}\left(\operatorname{discrepancyProfile}, z\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Patterns/Separable/OccupiedResidualGain.eventual_discrepancy_linear_gain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The discrepancy profile is the reciprocal of the product of the square root and logarithm of the base two plus the absolute position. The generator is the actual compensated weighted jump series. The integer absolute value of z must strictly exceed the natural threshold N, viewed as an integer.

Subtracting the finite exponent mixture from the full profile leaves the inverse three-quarter power of the base divided by its logarithm. Convexity gives nonnegative residual increments for jumps that stay on the same side. The remaining crossing jumps have a polynomially small total lower cost. The positive mixture gain absorbs that cost, and evenness transfers the estimate to negative positions.

## References

- Truth anchor: `D5/S1/Words/Patterns/Separable/OccupiedResidualGain.eventual_discrepancy_linear_gain`
- Dependency: [D5/S0/Asymptotics/WeightedProbability/AbsoluteDiscrepancySeries](../../../../S0/Asymptotics/WeightedProbability/AbsoluteDiscrepancySeries.md)
- Dependency: [D5/S1/Words/Patterns/Separable/OccupiedKernelCoefficient](OccupiedKernelCoefficient.md)
- Dependency: [D5/S1/Words/Patterns/Separable/OccupiedTruncatedMixture](OccupiedTruncatedMixture.md)
