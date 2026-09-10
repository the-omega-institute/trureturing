# Adaptive radius-four certificates

## Abstract

Adaptive radius-four geometric coverage and integer branching certificates.

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

**Definition 1.4 (Integer super-potential).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/AdaptiveRadiusFourCertificates.radiusFourWeight`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/AdaptiveRadiusFourCertificates.radiusFourWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The positive weight is bounded above by one hundred thousand.

**Theorem 1.5 (Complete selected geometric closure).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/AdaptiveRadiusFourCertificates.radiusFour_geometry`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/AdaptiveRadiusFourCertificates.radiusFour_geometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All 881 masks and all 2643 selected direction cases are checked against actual integer-grid updates. A failed lookup cannot be accepted as a blocked move unless that direction is genuinely in the mask.

**Theorem 1.6 (Exact row inequalities).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/AdaptiveRadiusFourCertificates.radiusFour_potential`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/AdaptiveRadiusFourCertificates.radiusFour_potential` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every weighted child sum times 2500 is at most the parent weight times 6202. Positivity, the cap and initial weight are also checked. Numerical eigensolver output is not a premise.

**Theorem 1.7 (All states and depths).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/AdaptiveRadiusFourCertificates.radiusFour_count_upper`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/AdaptiveRadiusFourCertificates.radiusFour_count_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The existing branching-potential induction turns the exact rows into an upper bound for every depth and every state.

**Theorem 1.8 (Uniform actual-domain bound).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/AdaptiveRadiusFourCertificates.radiusFour_domain_upper`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/AdaptiveRadiusFourCertificates.radiusFour_domain_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Selected-action geometric simulation transfers the bound to every finite domain disjoint from its recorded blockers. The cap is uniform over all states, holes, boundaries and depths.

**Theorem 1.9 (Parent-deleted domains).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/AdaptiveRadiusFourCertificates.radiusFour_parent_domain_upper`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/AdaptiveRadiusFourCertificates.radiusFour_parent_domain_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The initial parent-only mask gives a bound for every finite domain with that parent absent.

**Definition 1.10 (Four root directions).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/AdaptiveRadiusFourCertificates.rootDirection`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/AdaptiveRadiusFourCertificates.rootDirection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The unconditioned root has east, south, north and west directions.

**Definition 1.11 (Actual root branch domain).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/AdaptiveRadiusFourCertificates.rootDomain`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/AdaptiveRadiusFourCertificates.rootDomain` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The root and earlier neighbors are deleted before the chosen branch is translated and rotated. Its parent is proved absent.

**Definition 1.12 (Full root deletion count).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/AdaptiveRadiusFourCertificates.rootCount`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/AdaptiveRadiusFourCertificates.rootCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Actual domain membership decides root and child availability. Nonroot branches use the same certified adaptive controller.

**Theorem 1.13 (Uniform four-neighbor root bound).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/AdaptiveRadiusFourCertificates.radiusFour_root_upper`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/AdaptiveRadiusFourCertificates.radiusFour_root_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A single prefactor of four hundred thousand covers every finite root domain and every depth. This is a deletion-count theorem; the partition-polynomial identity is separate.

Exact geometric and integer replay was executed independently of the candidate discovery implementation. Lean elaboration, axiom-print execution and Scribe emission remain unperformed.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/AdaptiveRadiusFourCertificates.radiusFourChoice`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/AdaptiveRadiusFourCertificates.radiusFourMask`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/AdaptiveRadiusFourCertificates.radiusFourStep`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/AdaptiveRadiusFourCertificates.radiusFourWeight`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/AdaptiveRadiusFourCertificates.radiusFour_count_upper`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/AdaptiveRadiusFourCertificates.radiusFour_domain_upper`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/AdaptiveRadiusFourCertificates.radiusFour_geometry`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/AdaptiveRadiusFourCertificates.radiusFour_parent_domain_upper`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/AdaptiveRadiusFourCertificates.radiusFour_potential`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/AdaptiveRadiusFourCertificates.radiusFour_root_upper`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/AdaptiveRadiusFourCertificates.rootCount`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/AdaptiveRadiusFourCertificates.rootDirection`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/AdaptiveRadiusFourCertificates.rootDomain`
- Dependency: [D5/S3/StatisticalMechanics/HardCore/AdaptiveRadiusFourData](AdaptiveRadiusFourData.md)
- Dependency: [D5/S3/StatisticalMechanics/HardCore/OrderedGridMemory](OrderedGridMemory.md)
