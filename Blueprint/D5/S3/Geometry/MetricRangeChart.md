# Continuous metric-normalized local range products

## Abstract

Continuous metric-normalized local range products

**Definition 1.1 (Metric-normalized actual linear charts).**

Lean statement: `D5/S3/Geometry/MetricRangeChart.NormalizedChart`

*Formalization.* `D5/S3/Geometry/MetricRangeChart.NormalizedChart` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A normalized chart is an actual local linear chart whose reconstruction map pulls the supplied positive range metric back to the fixed Euclidean inner product.

**Theorem 1.2 (Continuous normalization).**

Lean statement: `D5/S3/Geometry/MetricRangeChart.exists_normalized_chart`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/MetricRangeChart.exists_normalized_chart` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A continuous positive ambient operator that is positive definite on each actual submodule normalizes every actual local chart. Pull the metric back by the chart, take its unique positive square root and compose reconstruction with the inverse square root. The inverse coordinate map uses the square root. Positivity on the actual range proves invertibility locally. All map families and their inverses are continuous on the same open neighborhood.

**Definition 1.3 (The exact closed disc product).**

Lean statement: `D5/S3/Geometry/MetricRangeChart.discHomeomorph`

*Formalization.* `D5/S3/Geometry/MetricRangeChart.discHomeomorph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The actual range-restricted metric disc over a chart neighborhood is homeomorphic to that neighborhood times the closed Euclidean unit ball. The maps are the normalized linear coordinates and reconstruction. The inverse identities and continuity are proved for the entire local product.

**Definition 1.4 (The actual sphere product).**

Lean statement: `D5/S3/Geometry/MetricRangeChart.sphereHomeomorph`

*Formalization.* `D5/S3/Geometry/MetricRangeChart.sphereHomeomorph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The actual range-restricted metric unit sphere has the corresponding local product with the Euclidean unit sphere, using the same normalized linear coordinates and continuous inverse.

## References

- Truth anchor: `D5/S3/Geometry/MetricRangeChart.NormalizedChart`
- Truth anchor: `D5/S3/Geometry/MetricRangeChart.discHomeomorph`
- Truth anchor: `D5/S3/Geometry/MetricRangeChart.exists_normalized_chart`
- Truth anchor: `D5/S3/Geometry/MetricRangeChart.sphereHomeomorph`
- Dependency: [D5/S3/Geometry/ContinuousRangeBundle](ContinuousRangeBundle.md)
- Dependency: [D5/S3/Geometry/EllipsoidShape](EllipsoidShape.md)
