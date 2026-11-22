# The logistic midline contour

## Abstract

The reflected inner product on the Yang strip gives an exact logistic energy comparison.

**Definition 1.1 (Vertical parametrization).**

Lean statement: `D5/S3/Analytic/PetzLogisticMidline.line`

*Formalization.* `D5/S3/Analytic/PetzLogisticMidline.line` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The vertical line at real part x is parameterized by x + it.

**Definition 1.2 (Closed strip).**

Lean statement: `D5/S3/Analytic/PetzLogisticMidline.closedStrip`

*Formalization.* `D5/S3/Analytic/PetzLogisticMidline.closedStrip` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real part is in [0, 1/2].

**Definition 1.3 (Open strip).**

Lean statement: `D5/S3/Analytic/PetzLogisticMidline.openStrip`

*Formalization.* `D5/S3/Analytic/PetzLogisticMidline.openStrip` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real part is in (0, 1/2).

**Definition 1.4 (Upper weight).**

Lean statement: `D5/S3/Analytic/PetzLogisticMidline.upperWeight`

*Formalization.* `D5/S3/Analytic/PetzLogisticMidline.upperWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The upper weight is π/(cosh(2πt) + 1).

**Definition 1.5 (Lower weight).**

Lean statement: `D5/S3/Analytic/PetzLogisticMidline.lowerWeight`

*Formalization.* `D5/S3/Analytic/PetzLogisticMidline.lowerWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The lower weight is π/(cosh(2πt) − 1) with totalized division.

**Definition 1.6 (Midline weight).**

Lean statement: `D5/S3/Analytic/PetzLogisticMidline.midlineWeight`

*Formalization.* `D5/S3/Analytic/PetzLogisticMidline.midlineWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The midline weight is π/cosh²(2πt).

**Definition 1.7 (Contour denominator).**

Lean statement: `D5/S3/Analytic/PetzLogisticMidline.kernelDen`

*Formalization.* `D5/S3/Analytic/PetzLogisticMidline.kernelDen` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The contour denominator is 1 + cos(2πz).

**Definition 1.8 (Contour kernel).**

Lean statement: `D5/S3/Analytic/PetzLogisticMidline.kernel`

*Formalization.* `D5/S3/Analytic/PetzLogisticMidline.kernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The contour kernel is π divided by the contour denominator.

**Definition 1.9 (Reflection across the midline).**

Lean statement: `D5/S3/Analytic/PetzLogisticMidline.reflect`

*Formalization.* `D5/S3/Analytic/PetzLogisticMidline.reflect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Reflection sends z to 1/2 − conj z.

**Definition 1.10 (Reflected inner product).**

Lean statement: `D5/S3/Analytic/PetzLogisticMidline.reflectedPair`

*Formalization.* `D5/S3/Analytic/PetzLogisticMidline.reflectedPair` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Pair the value at the reflected argument with the value at z. Mathlib uses the first slot conjugate-linear.

**Theorem 1.11 (Real part of a vertical line).**

Lean statement: `D5/S3/Analytic/PetzLogisticMidline.line_re`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PetzLogisticMidline.line_re` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real part at parameter t is x.

**Theorem 1.12 (Imaginary part of a vertical line).**

Lean statement: `D5/S3/Analytic/PetzLogisticMidline.line_im`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PetzLogisticMidline.line_im` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The imaginary part at parameter t is t.

**Theorem 1.13 (Continuity of a vertical line).**

Lean statement: `D5/S3/Analytic/PetzLogisticMidline.continuous_line`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PetzLogisticMidline.continuous_line` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The parametrization is continuous in t for every real x.

**Theorem 1.14 (Rectangular contour with decay).**

Lean statement: `D5/S3/Analytic/PetzLogisticMidline.vertical_integrals_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PetzLogisticMidline.vertical_integrals_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A continuous function on a closed vertical strip that is holomorphic in its interior and is bounded by a common integrable majorant tending to zero at both infinities is integrable on every vertical section and has equal vertical integrals on both edges.

**Theorem 1.15 (Contour with the logistic kernel).**

Lean statement: `D5/S3/Analytic/PetzLogisticMidline.weighted_vertical_integrals_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PetzLogisticMidline.weighted_vertical_integrals_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the strip from zero to one quarter the kernel times a bounded function continuous on the closed strip and holomorphic inside is integrable on each vertical line and has equal integrals on the two edges.

**Theorem 1.16 (Holomorphy of the reflected cross term).**

Lean statement: `D5/S3/Analytic/PetzLogisticMidline.differentiableAt_reflectedPair`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PetzLogisticMidline.differentiableAt_reflectedPair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complex differentiability at a point and its reflection gives complex differentiability of the reflected pair at the point. Conjugate-linearity in the first slot cancels conjugation of the increment.

**Theorem 1.17 (Exact midline identity).**

Lean statement: `D5/S3/Analytic/PetzLogisticMidline.integral_midline`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PetzLogisticMidline.integral_midline` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a bounded Hilbert-valued curve continuous on the closed strip and holomorphic inside, the integral of the real reflected cross term against the upper weight equals the integral of the squared midline norm against the midline weight. Both integrands are integrable.

**Theorem 1.18 (Integrability of the upper weight).**

Lean statement: `D5/S3/Analytic/PetzLogisticMidline.integrable_upperWeight`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PetzLogisticMidline.integrable_upperWeight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The upper weight is Lebesgue integrable on the real line.

**Theorem 1.19 (Poisson weight difference).**

Lean statement: `D5/S3/Analytic/PetzLogisticMidline.weight_difference_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PetzLogisticMidline.weight_difference_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At every nonzero time the lower weight minus the upper weight equals 2π/sinh²(2πt).

**Theorem 1.20 (Full logistic boundary energy).**

Lean statement: `D5/S3/Analytic/PetzLogisticMidline.full_logistic_strip`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PetzLogisticMidline.full_logistic_strip` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take a bounded Hilbert-valued curve continuous on the closed strip and holomorphic inside. Assume the lower weighted boundary square is integrable. Then the logistic square of the boundary difference is integrable. Its integral subtracted from the sum of the two weighted boundary squares equals the lower square weighted by the difference of the weights plus twice the midline integral. Both contributions are nonnegative.

## References

- Truth anchor: `D5/S3/Analytic/PetzLogisticMidline.closedStrip`
- Truth anchor: `D5/S3/Analytic/PetzLogisticMidline.continuous_line`
- Truth anchor: `D5/S3/Analytic/PetzLogisticMidline.differentiableAt_reflectedPair`
- Truth anchor: `D5/S3/Analytic/PetzLogisticMidline.full_logistic_strip`
- Truth anchor: `D5/S3/Analytic/PetzLogisticMidline.integrable_upperWeight`
- Truth anchor: `D5/S3/Analytic/PetzLogisticMidline.integral_midline`
- Truth anchor: `D5/S3/Analytic/PetzLogisticMidline.kernel`
- Truth anchor: `D5/S3/Analytic/PetzLogisticMidline.kernelDen`
- Truth anchor: `D5/S3/Analytic/PetzLogisticMidline.line`
- Truth anchor: `D5/S3/Analytic/PetzLogisticMidline.line_im`
- Truth anchor: `D5/S3/Analytic/PetzLogisticMidline.line_re`
- Truth anchor: `D5/S3/Analytic/PetzLogisticMidline.lowerWeight`
- Truth anchor: `D5/S3/Analytic/PetzLogisticMidline.midlineWeight`
- Truth anchor: `D5/S3/Analytic/PetzLogisticMidline.openStrip`
- Truth anchor: `D5/S3/Analytic/PetzLogisticMidline.reflect`
- Truth anchor: `D5/S3/Analytic/PetzLogisticMidline.reflectedPair`
- Truth anchor: `D5/S3/Analytic/PetzLogisticMidline.upperWeight`
- Truth anchor: `D5/S3/Analytic/PetzLogisticMidline.vertical_integrals_eq`
- Truth anchor: `D5/S3/Analytic/PetzLogisticMidline.weight_difference_eq`
- Truth anchor: `D5/S3/Analytic/PetzLogisticMidline.weighted_vertical_integrals_eq`
