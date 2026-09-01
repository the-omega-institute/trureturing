# Li Curvature Criterion

## Abstract

Toeplitz positivity of every Li-curvature section is equivalent to the Riemann hypothesis under the stated representation interfaces.

**Theorem 1.1 (Li curvature criterion).**

$$\forall c \in \operatorname{Integer}\left(\right) \to \operatorname{Complex}\left(\right), lambda \in \operatorname{Natural}\left(\right) \to \operatorname{Real}\left(\right),\; \left(\left(\left(\left(\left(\left(\operatorname{RiemannHypothesis}\left(\right) \Leftrightarrow \left(\forall n \in \operatorname{Natural}\left(\right),\; 0 \le lambda\left(n\right)\right)\right) \land lambda\left(0\right) = 0\right) \land 0 \le lambda\left(1\right)\right) \land \left(\forall n \in \operatorname{Natural}\left(\right),\; 1 \le n \Rightarrow lambda\left(n + 1\right) - 2 \cdot lambda\left(n\right) + lambda\left(n - 1\right) = 2 \cdot lambda\left(1\right) \cdot \operatorname{realPart}\left(c\left(n\right)\right)\right)\right) \land \left(\operatorname{RiemannHypothesis}\left(\right) \Rightarrow \left(\exists mu \in \operatorname{Measure}\left(\operatorname{Circle}\left(\right)\right),\; \operatorname{IsProbabilityMeasure}\left(mu\right) \land \left(\forall k \in \operatorname{Integer}\left(\right),\; c\left(k\right) = \operatorname{circleMoment}\left(mu, k\right)\right)\right)\right)\right) \land \left(\left(\forall N \in \operatorname{Natural}\left(\right),\; \operatorname{PosSemidef}\left(\operatorname{toeplitzMatrix}\left(c, N\right)\right)\right) \Rightarrow \left(\exists mu \in \operatorname{Measure}\left(\operatorname{Circle}\left(\right)\right),\; \operatorname{IsProbabilityMeasure}\left(mu\right) \land \left(\forall k \in \operatorname{Integer}\left(\right),\; c\left(k\right) = \operatorname{circleMoment}\left(mu, k\right)\right)\right)\right)\right) \Rightarrow \left(\operatorname{RiemannHypothesis}\left(\right) \Leftrightarrow \left(\forall N \in \operatorname{Natural}\left(\right),\; \operatorname{PosSemidef}\left(\operatorname{toeplitzMatrix}\left(c, N\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/TestFunctions/LiCurvatureCriterion.li_curvature_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The statement keeps the Li criterion, the canonical initial data and curvature recurrence, and the two common probability-measure representations as explicit interfaces. These are the ingredients not supplied together by the pinned library.

For the forward direction, the circle-moment representation turns each Toeplitz quadratic form into the integral of the squared modulus of its analytic coefficient polynomial.

For the reverse direction, the finite geometric polynomial has empty sum at zero. Its squared modulus reconstructs a nonnegative Li sequence with the prescribed first two values and second differences. Two-step recurrence uniqueness identifies it with the supplied Li sequence, after which the Li criterion applies.

## References

- Truth anchor: `D5/S3/Weil/TestFunctions/LiCurvatureCriterion.li_curvature_criterion`
- Dependency: [D5/S3/Weil/TestFunctions/LiCurvatureFourierRepresentation](LiCurvatureFourierRepresentation.md)
