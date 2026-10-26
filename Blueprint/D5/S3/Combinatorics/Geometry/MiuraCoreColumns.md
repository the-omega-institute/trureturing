# Symmetric columns have no extrema

## Abstract

Finite signed contraction on the actual rectangular height grid.

**Definition 1.1 (Occupied columns).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraCoreColumns.activeColumn`

*Formalization.* `D5/S3/Combinatorics/Geometry/MiuraCoreColumns.activeColumn` (`✓ std3`).

*Citation.* Chakshu Gupta (2026). *One construction for the Miura-ori flip-graph degree sequence*. DOI: [10.48550/arXiv.2607.05567](https://doi.org/10.48550/arXiv.2607.05567). URL: <https://arxiv.org/abs/2607.05567v3>.

*Commentary.*

A column is occupied exactly when an actual strict minimum or maximum lies in it.

**Definition 1.2 (Maximal unoccupied runs).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraCoreColumns.numFrozenRuns`

*Formalization.* `D5/S3/Combinatorics/Geometry/MiuraCoreColumns.numFrozenRuns` (`✓ std3`).

*Citation.* Chakshu Gupta (2026). *One construction for the Miura-ori flip-graph degree sequence*. DOI: [10.48550/arXiv.2607.05567](https://doi.org/10.48550/arXiv.2607.05567). URL: <https://arxiv.org/abs/2607.05567v3>.

*Commentary.*

A run starts at an unoccupied column whose predecessor is occupied, with a separate condition at the first physical column.

**Definition 1.3 (Symmetric internal columns).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraCoreColumns.frozenColumn`

*Formalization.* `D5/S3/Combinatorics/Geometry/MiuraCoreColumns.frozenColumn` (`✓ std3`).

*Citation.* Chakshu Gupta (2026). *One construction for the Miura-ori flip-graph degree sequence*. DOI: [10.48550/arXiv.2607.05567](https://doi.org/10.48550/arXiv.2607.05567). URL: <https://arxiv.org/abs/2607.05567v3>.

*Commentary.*

Both horizontal neighbours exist and their heights sum to twice the middle height in every row.

**Theorem 1.4 (Occupied columns are bounded by extrema).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraCoreColumns.numActiveColumns_le_numExtrema`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraCoreColumns.numActiveColumns_le_numExtrema` (`✓ std3`). ∎

*Citation.* Chakshu Gupta (2026). *One construction for the Miura-ori flip-graph degree sequence*. DOI: [10.48550/arXiv.2607.05567](https://doi.org/10.48550/arXiv.2607.05567). URL: <https://arxiv.org/abs/2607.05567v3>.

*Commentary.*

Projecting each actual extremum onto its column covers all occupied columns, so their number is at most the number of extrema.

**Theorem 1.5 (Runs lie between occupied columns).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraCoreColumns.numFrozenRuns_le`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraCoreColumns.numFrozenRuns_le` (`✓ std3`). ∎

*Citation.* Chakshu Gupta (2026). *One construction for the Miura-ori flip-graph degree sequence*. DOI: [10.48550/arXiv.2607.05567](https://doi.org/10.48550/arXiv.2607.05567). URL: <https://arxiv.org/abs/2607.05567v3>.

*Commentary.*

If both boundary columns are occupied, the number of maximal unoccupied runs plus one is at most the number of occupied columns.

**Theorem 1.6 (Symmetric columns have no extrema).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraCoreColumns.frozenColumn_not_active`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraCoreColumns.frozenColumn_not_active` (`✓ std3`). ∎

*Citation.* Chakshu Gupta (2026). *One construction for the Miura-ori flip-graph degree sequence*. DOI: [10.48550/arXiv.2607.05567](https://doi.org/10.48550/arXiv.2607.05567). URL: <https://arxiv.org/abs/2607.05567v3>.

*Commentary.*

In a symmetric interior column, the two horizontal neighbours exclude both signs of strict local extremum. No unit-edge assumption is needed for this implication.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraCoreColumns.activeColumn`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraCoreColumns.frozenColumn`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraCoreColumns.frozenColumn_not_active`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraCoreColumns.numActiveColumns_le_numExtrema`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraCoreColumns.numFrozenRuns`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraCoreColumns.numFrozenRuns_le`
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraHeightEnvelope](MiuraHeightEnvelope.md)
