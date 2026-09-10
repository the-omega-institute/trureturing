# Certified Radius-Four Growth Bound

## Abstract

Geometric hard-core memory, exact path semantics and integer certificates.

**Definition 1.1 (Actual blocked vertices).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/RadiusFourCertificates.radiusFourMask`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/RadiusFourCertificates.radiusFourMask` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Decode the geometric mask in the fixed Manhattan-disk coordinate order.

**Definition 1.2 (Fixed-SRL transitions).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/RadiusFourCertificates.radiusFourStep`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/RadiusFourCertificates.radiusFourStep` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Only action zero is implemented; other actions return none without any coverage claim. Selected successors are computed from the geometric update and exact lookup.

**Definition 1.3 (Positive integer potential).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/RadiusFourCertificates.radiusFourWeight`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/RadiusFourCertificates.radiusFourWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Read the exact positive weight associated with each geometric state.

**Theorem 1.4 (Full selected-order geometric closure).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/RadiusFourCertificates.radiusFour_geometry`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/RadiusFourCertificates.radiusFour_geometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Check all 851 states and three directions, distinct masks, initial state, parent retention and origin exclusion. Option-map equality preserves each direction, including absent children.

**Theorem 1.5 (Exact integer row certificate).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/RadiusFourCertificates.radiusFour_potential`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/RadiusFourCertificates.radiusFour_potential` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every weight is between one and twenty thousand. Ten thousand times the child-weight sum is at most 24827 times the parent weight. The root weight is exactly twenty thousand. Equality in a row is allowed.

**Theorem 1.6 (All-depth represented count bound).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/RadiusFourCertificates.radiusFour_table_upper`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/RadiusFourCertificates.radiusFour_table_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The existing super-potential induction supplies the quantitative bound for every state, depth and history.

**Theorem 1.7 (Transport to the raw geometric process).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/RadiusFourCertificates.radiusFour_geometric_upper`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/RadiusFourCertificates.radiusFour_geometric_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact fixed-order presentation semantics transfers the bound to the actual radius-four memory rooted at the parent-blocked set. No spectral-fit or supplied count-equality premise remains.

**Theorem 1.8 (An actual finite-domain consumer).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/RadiusFourCertificates.radiusFour_finite_domain_upper`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/RadiusFourCertificates.radiusFour_finite_domain_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite integer-grid vertex set with the parent absent, the raw ordered deletion count has prefactor twenty thousand and rate at most 24827 over ten thousand. Real domain membership determines child availability. Partition-polynomial and complex zero-free consequences remain separate obligations.

**Theorem 1.9 (A finite universal separation).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/RadiusFourCertificates.radiusFour_beats_every_radiusThree_controller`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/RadiusFourCertificates.radiusFour_beats_every_radiusThree_controller` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At depth seven hundred, the fixed-SRL radius-four count is strictly below the count of every history-dependent radius-three controller. The proof combines the actual two model certificates with an exact integer comparison; it does not enumerate policies or transfer a relaxed-model lower bound to the physical grid.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/RadiusFourCertificates.radiusFourMask`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/RadiusFourCertificates.radiusFourStep`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/RadiusFourCertificates.radiusFourWeight`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/RadiusFourCertificates.radiusFour_beats_every_radiusThree_controller`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/RadiusFourCertificates.radiusFour_finite_domain_upper`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/RadiusFourCertificates.radiusFour_geometric_upper`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/RadiusFourCertificates.radiusFour_geometry`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/RadiusFourCertificates.radiusFour_potential`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/RadiusFourCertificates.radiusFour_table_upper`
- Dependency: [D5/S3/StatisticalMechanics/HardCore/MemoryRefinement](MemoryRefinement.md)
- Dependency: [D5/S3/StatisticalMechanics/HardCore/RadiusFourData](RadiusFourData.md)
- Dependency: [D5/S3/StatisticalMechanics/HardCore/RadiusThreeCertificates](RadiusThreeCertificates.md)
