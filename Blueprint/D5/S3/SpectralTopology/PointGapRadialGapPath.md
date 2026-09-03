# Point-Gap Radial Gap Path

## Abstract

A point-gap norm budget keeps the whole radial localizer path invertible.

**Definition 1.1 (Scale gap budget).**

Lean statement: `D5/S3/SpectralTopology/PointGapRadialGapPath.scaleGapBudget`

*Formalization.* `D5/S3/SpectralTopology/PointGapRadialGapPath.scaleGapBudget` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The inverse zero-scale norm, scale norm, and position-direction norm form the explicit Neumann budget.

**Definition 1.2 (Admissible scale).**

Lean statement: `D5/S3/SpectralTopology/PointGapRadialGapPath.IsAdmissibleScale`

*Formalization.* `D5/S3/SpectralTopology/PointGapRadialGapPath.IsAdmissibleScale` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A scale is admissible when the spectral shift has a point gap and its explicit budget is below one.

**Definition 1.3 (Radial localizer path).**

Lean statement: `D5/S3/SpectralTopology/PointGapRadialGapPath.radialLocalizer`

*Formalization.* `D5/S3/SpectralTopology/PointGapRadialGapPath.radialLocalizer` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The unit-interval parameter contracts the requested scale along the line from zero to the finite-scale localizer.

**Theorem 1.4 (Zero-scale budget).**

Lean statement: `D5/S3/SpectralTopology/PointGapRadialGapPath.scale_gap_budget_zero`

*Formalization.* `D5/S3/SpectralTopology/PointGapRadialGapPath.scale_gap_budget_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The zero scale consumes no Neumann budget.

**Theorem 1.5 (Radial budget monotonicity).**

Lean statement: `D5/S3/SpectralTopology/PointGapRadialGapPath.radial_scale_gap_budget_le`

*Formalization.* `D5/S3/SpectralTopology/PointGapRadialGapPath.radial_scale_gap_budget_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Contracting a scale along the unit interval cannot increase its explicit gap budget.

**Theorem 1.6 (Zero-scale admissibility).**

Lean statement: `D5/S3/SpectralTopology/PointGapRadialGapPath.admissible_scale_zero`

*Formalization.* `D5/S3/SpectralTopology/PointGapRadialGapPath.admissible_scale_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every point gap makes the zero scale admissible.

**Theorem 1.7 (Star-shaped admissible region).**

Lean statement: `D5/S3/SpectralTopology/PointGapRadialGapPath.admissible_scale_radial`

*Formalization.* `D5/S3/SpectralTopology/PointGapRadialGapPath.admissible_scale_radial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every radial contraction of an admissible scale remains admissible.

**Theorem 1.8 (Affine radial localizer).**

Lean statement: `D5/S3/SpectralTopology/PointGapRadialGapPath.radial_localizer_affine`

*Formalization.* `D5/S3/SpectralTopology/PointGapRadialGapPath.radial_localizer_affine` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The radial family is the zero-scale localizer plus the linearly scaled position direction.

**Theorem 1.9 (Radial path start).**

Lean statement: `D5/S3/SpectralTopology/PointGapRadialGapPath.radial_localizer_zero`

*Formalization.* `D5/S3/SpectralTopology/PointGapRadialGapPath.radial_localizer_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The radial path starts at the zero-scale localizer.

**Theorem 1.10 (Radial path endpoint).**

Lean statement: `D5/S3/SpectralTopology/PointGapRadialGapPath.radial_localizer_one`

*Formalization.* `D5/S3/SpectralTopology/PointGapRadialGapPath.radial_localizer_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The radial path ends at the requested finite-scale localizer.

**Theorem 1.11 (Radial Hermitianity).**

Lean statement: `D5/S3/SpectralTopology/PointGapRadialGapPath.radial_localizer_isHermitian`

*Formalization.* `D5/S3/SpectralTopology/PointGapRadialGapPath.radial_localizer_isHermitian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A Hermitian position observable makes every radial-path matrix Hermitian.

**Theorem 1.12 (Radial gap preservation).**

Lean statement: `D5/S3/SpectralTopology/PointGapRadialGapPath.radial_localizer_isUnit`

*Formalization.* `D5/S3/SpectralTopology/PointGapRadialGapPath.radial_localizer_isUnit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every point on an admissible radial segment is invertible.

**Theorem 1.13 (Hermitian invertible radial path).**

Lean statement: `D5/S3/SpectralTopology/PointGapRadialGapPath.radial_hermitian_gap_path`

*Formalization.* `D5/S3/SpectralTopology/PointGapRadialGapPath.radial_hermitian_gap_path` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An admissible scale supplies a Hermitian invertible path on the whole unit interval.

**Theorem 1.14 (Gap-closure budget obstruction).**

Lean statement: `D5/S3/SpectralTopology/PointGapRadialGapPath.one_le_scale_gap_budget_of_gap_closure`

*Formalization.* `D5/S3/SpectralTopology/PointGapRadialGapPath.one_le_scale_gap_budget_of_gap_closure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Any finite-scale gap closure above a point-gap zero scale forces the explicit budget to reach at least one.

**Theorem 1.15 (Radial gap-closure obstruction).**

Lean statement: `D5/S3/SpectralTopology/PointGapRadialGapPath.one_le_endpoint_budget_of_radial_gap_closure`

*Formalization.* `D5/S3/SpectralTopology/PointGapRadialGapPath.one_le_endpoint_budget_of_radial_gap_closure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A gap closure anywhere on the radial segment forces the endpoint budget to reach at least one.

**Theorem 1.16 (Exact initial inertia with radial gap path).**

Lean statement: `D5/S3/SpectralTopology/PointGapRadialGapPath.point_gap_exact_inertia_and_radial_gap_path`

*Formalization.* `D5/S3/SpectralTopology/PointGapRadialGapPath.point_gap_exact_inertia_and_radial_gap_path` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A point gap supplies exact initial chiral inertia and a Hermitian invertible path to every admissible scale.

## References

- Truth anchor: `D5/S3/SpectralTopology/PointGapRadialGapPath.scaleGapBudget`
- Truth anchor: `D5/S3/SpectralTopology/PointGapRadialGapPath.IsAdmissibleScale`
- Truth anchor: `D5/S3/SpectralTopology/PointGapRadialGapPath.radialLocalizer`
- Truth anchor: `D5/S3/SpectralTopology/PointGapRadialGapPath.scale_gap_budget_zero`
- Truth anchor: `D5/S3/SpectralTopology/PointGapRadialGapPath.radial_scale_gap_budget_le`
- Truth anchor: `D5/S3/SpectralTopology/PointGapRadialGapPath.admissible_scale_zero`
- Truth anchor: `D5/S3/SpectralTopology/PointGapRadialGapPath.admissible_scale_radial`
- Truth anchor: `D5/S3/SpectralTopology/PointGapRadialGapPath.radial_localizer_affine`
- Truth anchor: `D5/S3/SpectralTopology/PointGapRadialGapPath.radial_localizer_zero`
- Truth anchor: `D5/S3/SpectralTopology/PointGapRadialGapPath.radial_localizer_one`
- Truth anchor: `D5/S3/SpectralTopology/PointGapRadialGapPath.radial_localizer_isHermitian`
- Truth anchor: `D5/S3/SpectralTopology/PointGapRadialGapPath.radial_localizer_isUnit`
- Truth anchor: `D5/S3/SpectralTopology/PointGapRadialGapPath.radial_hermitian_gap_path`
- Truth anchor: `D5/S3/SpectralTopology/PointGapRadialGapPath.one_le_scale_gap_budget_of_gap_closure`
- Truth anchor: `D5/S3/SpectralTopology/PointGapRadialGapPath.one_le_endpoint_budget_of_radial_gap_closure`
- Truth anchor: `D5/S3/SpectralTopology/PointGapRadialGapPath.point_gap_exact_inertia_and_radial_gap_path`
- Dependency: [D5/S3/SpectralTopology/PointGapFiniteScaleStability](PointGapFiniteScaleStability.md)
- Dependency: [D5/S3/SpectralTopology/PointGapExactInertia](PointGapExactInertia.md)
