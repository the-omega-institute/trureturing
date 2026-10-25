# Three Canonical Sector Fields

## Abstract

The six actual canonical three-field products have a common vector series.

Take arbitrary ordinary even integral lattice data D, three charges alpha,beta,gamma and arbitrary oscillator descendants u,v,t. The labelled fields are precisely Y D applied to their canonical sector inclusions. Charges, states and field values may repeat. Degenerate and indefinite forms and rank zero are included; no inverse Gram matrix is used.

**Theorem 1.1 (All six orders on an arbitrary fourth-sector state).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeSectorThreeFieldCommonSeries.actual_three_field_common_series`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeSectorThreeFieldCommonSeries.actual_three_field_common_series` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Atsushi Matsuo; Kiyokazu Nagatomo (1997). *On axioms for a vertex algebra and the locality of quantum fields*. URL: <https://arxiv.org/abs/hep-th/9706118v1>.

*Commentary.*

There is one locality order k for the three fields before the fourth charge delta and state w are chosen. For each delta,w there are nonnegative cutoffs a and a native MvPowerSeries in three variables with coefficients in the common total-charge oscillator sector. Each original canonical mode vanishes on w at every integer mode at least its cutoff.

At every signed exponent vector e, clearing by Q and evaluating at e-a gives the signed extension of this same P for each of the six orders 012,021,102,120,201,210. The products are the literal three nested canonical operators, with the exponent attached to its original label. inclusion_canonical and its charge_homogeneity supplier identify each nested product with the original Carrier field word; permutation invariance of total charge puts all six in one sector. Projection commutes with finite convolution and signed extension.

This endpoint requires no locality certificate from its caller: stateField_locality discharges it for the actual fields, and the actual VertexOperator truncation discharges the input cutoffs. It proves neither associator nor pentagon, hexagon, four-object sewing or convergence on an arbitrary algebraic dual. Full charged module categories, symmetry anomalies, Monster realization, CFT, string theory and AdS/CFT remain further mathematical obligations.

Classical lattice and formal-locality sources are those of the imported Bakalov-Kac, Matsuo-Nagatomo and Carnahan suppliers. The construction asserts no new literature theorem.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeSectorThreeFieldCommonSeries.actual_three_field_common_series`
- Dependency: [D5/S3/VertexAlgebra/FormalSeries/UngradedLocalWordSeries](../FormalSeries/UngradedLocalWordSeries.md)
- Dependency: [D5/S3/VertexAlgebra/Sectors/LatticeSectorBorcherds](LatticeSectorBorcherds.md)
