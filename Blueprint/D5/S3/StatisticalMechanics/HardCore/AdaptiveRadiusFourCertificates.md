# Adaptive radius-four certificates

## Abstract

Adaptive radius-four geometric coverage for the zero-freeness proof.

**Definition 1.1 (Actual blocked vertices).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/AdaptiveRadiusFourCertificates.radiusFourMask`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/AdaptiveRadiusFourCertificates.radiusFourMask` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The integer mask decodes to actual grid points in the full lexicographic Manhattan disk. Distinct codes are checked; no numerical-weight quotient replaces the geometry.

**Definition 1.2 (Selected local order).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/AdaptiveRadiusFourCertificates.radiusFourChoice`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/AdaptiveRadiusFourCertificates.radiusFourChoice` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicit state-dependent controller selects one of six orders.

**Definition 1.3 (Geometrically computed successor).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/AdaptiveRadiusFourCertificates.radiusFourStep`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/AdaptiveRadiusFourCertificates.radiusFourStep` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The successor is obtained by computing memoryStep and looking up its exact mask. The unused action argument fits the shared counting API; only the selected order is certified. No supplied transition list is trusted.

**Definition 1.4 (Stored integer weight).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/AdaptiveRadiusFourCertificates.radiusFourWeight`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/AdaptiveRadiusFourCertificates.radiusFourWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The original integer weight payload is retained as a public accessor.

**Theorem 1.5 (Complete selected geometric closure).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/AdaptiveRadiusFourCertificates.radiusFour_geometry`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/AdaptiveRadiusFourCertificates.radiusFour_geometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All 881 masks and all 2643 selected direction cases are checked against actual integer-grid updates. A failed lookup cannot be accepted as a blocked move unless that direction is genuinely in the mask.

**Definition 1.6 (Four root directions).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/AdaptiveRadiusFourCertificates.rootDirection`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/AdaptiveRadiusFourCertificates.rootDirection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The unconditioned root has east, south, north and west directions.

**Definition 1.7 (Actual root branch domain).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/AdaptiveRadiusFourCertificates.rootDomain`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/AdaptiveRadiusFourCertificates.rootDomain` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The root and earlier neighbors are deleted before the chosen branch is translated and rotated. Its parent is proved absent.

**Definition 1.8 (Full root deletion count).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/AdaptiveRadiusFourCertificates.rootCount`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/AdaptiveRadiusFourCertificates.rootCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Actual domain membership decides root and child availability. Nonroot branches use the same certified adaptive controller.

The finite geometric checks are replayed by Lean's kernel. Resource measurements are recorded separately.
