# Transport both relabel factors through the actual charts

## Abstract

Transport both relabel factors through the actual charts.

countedInCharts composes cG, r and cH.symm on both vertices and numbered edges. charted_weight transports the two row matrices together through these charts. It does not infer invariance of an individual edge value under an arbitrary basis change. The literal forward factor uses reindex r.vertex, and the backward factor uses timeMap G after the inverse reindexing.

The Charts section quantifies V,E,W,J with Fintype instances, DecidableEq V and W, graphs G,H, dimensions n,m and count matrices A,B. Each weight theorem takes d and NeZero d; residue comparisons also take 3 ∣ d. presentation_relabel_residue uses the chosen chart F and chart H. chart_forward_residue retains the next chart phase, and chart_backward_residue retains the negative old chart phase. positive_leaf_residue keeps both chart corrections and the original nonnegative middle factors R,S.

These constructions and identities are repository-derived. Their provenance does not assert literature novelty.

**Definition 1.1 (countedInCharts).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelCharts.countedInCharts`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelCharts.countedInCharts` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Literally cH^{-1} after r after cG, on vertices AND numbered edges.

**Theorem 1.2 (charted_weight).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelCharts.charted_weight`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelCharts.charted_weight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Transport the forward and backward row factors together through the actual old and new charts. Their weight equals that of the composed counted relabel for every nonzero period.

**Theorem 1.3 (positive_leaf_residue).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelCharts.positive_leaf_residue`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelCharts.positive_leaf_residue` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Immediate actual positive-leaf specialization with BOTH chart terms. The nonnegative middle factors are the original R,S.

**Remark 1.4 (compose).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelCharts.compose`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelCharts.compose` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Compose both vertex and edge equivalences and their endpoint laws. The resulting graph relabel is used to form the literal counted chart composite.

**Remark 1.5 (identityRelabel).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelCharts.identityRelabel`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelCharts.identityRelabel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use identity equivalences on the vertices and numbered edges of a counted graph. This supplies the standard chart without introducing another enumeration.

**Remark 1.6 (charted_residue).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelCharts.charted_residue`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelCharts.charted_residue` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For nonzero periods divisible by three, apply the actual counted relabel comparison after transporting both factors through the charts. The result retains the phase of that complete composite.

**Remark 1.7 (identity_basis).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelCharts.identity_basis`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelCharts.identity_basis` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The identity vertex reindexing leaves the standard coefficient basis unchanged. This removes an identity chart in the positive-leaf comparison.

**Remark 1.8 (presentation_relabel_residue).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelCharts.presentation_relabel_residue`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelCharts.presentation_relabel_residue` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Actual arbitrary-presentation relabel leaf, in P1's chosen two charts.

**Remark 1.9 (chart_forward_residue).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelCharts.chart_forward_residue`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelCharts.chart_forward_residue` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The next correction uses the real counted composite chart(F)^{-1} r.

**Remark 1.10 (chart_backward_residue).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelCharts.chart_backward_residue`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelCharts.chart_backward_residue` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The old^{-1} correction has the literal opposite phase. Neither chart term is erased, even when the chart preserves beam action.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelCharts.chart_backward_residue`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelCharts.chart_forward_residue`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelCharts.charted_residue`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelCharts.charted_weight`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelCharts.compose`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelCharts.countedInCharts`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelCharts.identityRelabel`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelCharts.identity_basis`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelCharts.positive_leaf_residue`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelCharts.presentation_relabel_residue`
- Dependency: [D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelResidue](ActualRelabelResidue.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualWordLocalizedComparison](ActualWordLocalizedComparison.md)
