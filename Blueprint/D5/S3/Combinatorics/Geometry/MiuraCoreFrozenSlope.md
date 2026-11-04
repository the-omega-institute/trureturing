# One slope for the whole column

## Abstract

Finite signed contraction on the actual rectangular height grid.

**Theorem 1.1 (Extremum-free columns are symmetric).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraCoreFrozenSlope.inactive_imp_frozenColumn`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraCoreFrozenSlope.inactive_imp_frozenColumn` (`✓ std3`). ∎

*Citation.* Chakshu Gupta (2026). *One construction for the Miura-ori flip-graph degree sequence*. DOI: [10.48550/arXiv.2607.05567](https://doi.org/10.48550/arXiv.2607.05567). URL: <https://arxiv.org/abs/2607.05567v3>.

*Commentary.*

For an integer unit-edge height function on a nonempty row axis, every unoccupied interior column has symmetric horizontal neighbours at every row.

**Theorem 1.2 (Frozen classification).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraCoreFrozenSlope.frozenColumn_iff_inactive`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraCoreFrozenSlope.frozenColumn_iff_inactive` (`✓ std3`). ∎

*Citation.* Chakshu Gupta (2026). *One construction for the Miura-ori flip-graph degree sequence*. DOI: [10.48550/arXiv.2607.05567](https://doi.org/10.48550/arXiv.2607.05567). URL: <https://arxiv.org/abs/2607.05567v3>.

*Commentary.*

An interior column is symmetric exactly when it has no strict local extremum, using all existing ambient neighbours.

**Theorem 1.3 (Adjacent rows have the same slope).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraCoreFrozenSlope.frozenColumn_dL_const_adjacent`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraCoreFrozenSlope.frozenColumn_dL_const_adjacent` (`✓ std3`). ∎

*Citation.* Chakshu Gupta (2026). *One construction for the Miura-ori flip-graph degree sequence*. DOI: [10.48550/arXiv.2607.05567](https://doi.org/10.48550/arXiv.2607.05567). URL: <https://arxiv.org/abs/2607.05567v3>.

*Commentary.*

For a frozen column in an actual unit-edge height function, its left horizontal height difference agrees between adjacent rows.

**Theorem 1.4 (One slope for the whole column).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraCoreFrozenSlope.frozenColumn_dL_eq_row0`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraCoreFrozenSlope.frozenColumn_dL_eq_row0` (`✓ std3`). ∎

*Citation.* Chakshu Gupta (2026). *One construction for the Miura-ori flip-graph degree sequence*. DOI: [10.48550/arXiv.2607.05567](https://doi.org/10.48550/arXiv.2607.05567). URL: <https://arxiv.org/abs/2607.05567v3>.

*Commentary.*

On a nonempty row axis, induction along adjacent rows identifies every left horizontal difference with its value at row zero.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraCoreFrozenSlope.frozenColumn_dL_const_adjacent`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraCoreFrozenSlope.frozenColumn_dL_eq_row0`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraCoreFrozenSlope.frozenColumn_iff_inactive`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraCoreFrozenSlope.inactive_imp_frozenColumn`
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraCoreColumns](MiuraCoreColumns.md)
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraCoreFrozenWalk](MiuraCoreFrozenWalk.md)
