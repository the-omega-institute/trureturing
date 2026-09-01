# Finite Triangle Holonomy Curvature

## Abstract

Triangle loops define a finite matrix curvature whose holonomy conjugates and whose trace and determinant are gauge invariant.

**Definition 1.1 (Oriented triangle path).**

Lean statement: `D5/S3/Observer/HigherHolonomy/TriangleHolonomyCurvature.trianglePath`

*Formalization.* `D5/S3/Observer/HigherHolonomy/TriangleHolonomyCurvature.trianglePath` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Three vertices determine the closed path from the first vertex through the second and third and back to the first.

**Definition 1.2 (Triangle holonomy).**

Lean statement: `D5/S3/Observer/HigherHolonomy/TriangleHolonomyCurvature.triangleHolonomy`

*Formalization.* `D5/S3/Observer/HigherHolonomy/TriangleHolonomyCurvature.triangleHolonomy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite path transport around the oriented triangle is its multiplicative holonomy.

**Definition 1.3 (Triangle curvature defect).**

Lean statement: `D5/S3/Observer/HigherHolonomy/TriangleHolonomyCurvature.triangleCurvature`

*Formalization.* `D5/S3/Observer/HigherHolonomy/TriangleHolonomyCurvature.triangleCurvature` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Subtracting the identity matrix from triangle holonomy gives an additive curvature witness.

**Definition 1.4 (Flat triangle).**

Lean statement: `D5/S3/Observer/HigherHolonomy/TriangleHolonomyCurvature.IsFlatTriangle`

*Formalization.* `D5/S3/Observer/HigherHolonomy/TriangleHolonomyCurvature.IsFlatTriangle` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A triangle is flat when its loop holonomy is the identity unit.

**Theorem 1.5 (Ordered product formula).**

Lean statement: `D5/S3/Observer/HigherHolonomy/TriangleHolonomyCurvature.triangle_holonomy_formula`

*Formalization.* `D5/S3/Observer/HigherHolonomy/TriangleHolonomyCurvature.triangle_holonomy_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Triangle holonomy is the return edge multiplied by the second edge and then the first edge.

**Theorem 1.6 (Triangle holonomy is gauge conjugate).**

Lean statement: `D5/S3/Observer/HigherHolonomy/TriangleHolonomyCurvature.triangle_holonomy_gauge_conjugate`

*Formalization.* `D5/S3/Observer/HigherHolonomy/TriangleHolonomyCurvature.triangle_holonomy_gauge_conjugate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All interior gauges telescope and only conjugation at the base vertex remains.

**Theorem 1.7 (Triangle trace is gauge invariant).**

Lean statement: `D5/S3/Observer/HigherHolonomy/TriangleHolonomyCurvature.triangle_trace_gauge_invariant`

*Formalization.* `D5/S3/Observer/HigherHolonomy/TriangleHolonomyCurvature.triangle_trace_gauge_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The trace of triangle holonomy is unchanged by every vertex gauge.

**Theorem 1.8 (Triangle determinant is gauge invariant).**

Lean statement: `D5/S3/Observer/HigherHolonomy/TriangleHolonomyCurvature.triangle_determinant_gauge_invariant`

*Formalization.* `D5/S3/Observer/HigherHolonomy/TriangleHolonomyCurvature.triangle_determinant_gauge_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The determinant of triangle holonomy is unchanged by every vertex gauge.

**Theorem 1.9 (Zero curvature characterizes flatness).**

Lean statement: `D5/S3/Observer/HigherHolonomy/TriangleHolonomyCurvature.triangle_curvature_eq_zero_iff`

*Formalization.* `D5/S3/Observer/HigherHolonomy/TriangleHolonomyCurvature.triangle_curvature_eq_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The additive triangle curvature vanishes exactly when the loop holonomy is the identity.

**Theorem 1.10 (Gauge transport preserves flatness).**

Lean statement: `D5/S3/Observer/HigherHolonomy/TriangleHolonomyCurvature.isFlatTriangle_gauge`

*Formalization.* `D5/S3/Observer/HigherHolonomy/TriangleHolonomyCurvature.isFlatTriangle_gauge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A flat triangle remains flat after arbitrary vertex gauge transport.

**Theorem 1.11 (Inverse-edge backtracking is trivial).**

Lean statement: `D5/S3/Observer/HigherHolonomy/TriangleHolonomyCurvature.backtrack_holonomy_eq_one`

*Formalization.* `D5/S3/Observer/HigherHolonomy/TriangleHolonomyCurvature.backtrack_holonomy_eq_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Traversing an edge and its prescribed inverse gives identity holonomy.

## References

- Truth anchor: `D5/S3/Observer/HigherHolonomy/TriangleHolonomyCurvature.trianglePath`
- Truth anchor: `D5/S3/Observer/HigherHolonomy/TriangleHolonomyCurvature.triangleHolonomy`
- Truth anchor: `D5/S3/Observer/HigherHolonomy/TriangleHolonomyCurvature.triangleCurvature`
- Truth anchor: `D5/S3/Observer/HigherHolonomy/TriangleHolonomyCurvature.IsFlatTriangle`
- Truth anchor: `D5/S3/Observer/HigherHolonomy/TriangleHolonomyCurvature.triangle_holonomy_formula`
- Truth anchor: `D5/S3/Observer/HigherHolonomy/TriangleHolonomyCurvature.triangle_holonomy_gauge_conjugate`
- Truth anchor: `D5/S3/Observer/HigherHolonomy/TriangleHolonomyCurvature.triangle_trace_gauge_invariant`
- Truth anchor: `D5/S3/Observer/HigherHolonomy/TriangleHolonomyCurvature.triangle_determinant_gauge_invariant`
- Truth anchor: `D5/S3/Observer/HigherHolonomy/TriangleHolonomyCurvature.triangle_curvature_eq_zero_iff`
- Truth anchor: `D5/S3/Observer/HigherHolonomy/TriangleHolonomyCurvature.isFlatTriangle_gauge`
- Truth anchor: `D5/S3/Observer/HigherHolonomy/TriangleHolonomyCurvature.backtrack_holonomy_eq_one`
- Dependency: [D5/S3/Observer/HigherHolonomy/MatrixGaugeCovariance](MatrixGaugeCovariance.md)
